# chess-dl

Distill a small chess-playing neural net from Stockfish, then send it to play
real games on Lichess.

**Teacher:** Stockfish 18 (local, via `python-chess`).
**Student:** a small AlphaZero-style policy+value CNN, trained with
[MLX](https://github.com/ml-explore/mlx) on Apple Silicon GPU.
**Arena:** a [Lichess](https://lichess.org) BOT account, driven by
[lichess-bot](https://github.com/lichess-bot-devs/lichess-bot) calling into a
minimal UCI wrapper around the student model.

## How it works

1. **`generate_data.py`** — Stockfish plays itself (a few random opening
   plies, then temperature-sampled self-play afterwards for diversity). At
   each position we record Stockfish's top-K moves (MultiPV) as a soft policy
   target (softmax over their centipawn scores) and the best move's eval as a
   value target in `[-1, 1]`. Output: JSONL.
2. **`build_dataset.py`** — encodes JSONL positions into dense tensors
   (`X`: 8x8x17 board planes, `P`: 4096-way policy target, `V`: scalar value,
   `G`: per-position game-group id) and saves a `.npz` shard. Positions are
   **de-duplicated** (fixed-teacher self-play revisits the same openings —
   ~1.6x duplication measured — and the targets are identical, so duplicates
   add no signal but would leak the exact same position into both train and
   val). `G` records which game each position came from so training can hold
   out *whole games* rather than individual (correlated) positions. Board/move
   encoding lives in `encoding.py` and is framework-agnostic (plain NumPy).
3. **`train.py`** — trains `ChessNet` (`model.py`, MLX) on the `.npz` dataset
   with a combined cross-entropy (policy) + MSE (value) loss.
4. **`evaluate.py`** — plays the student against Stockfish at a capped
   `UCI_Elo` and reports W/D/L plus a rough Elo-gap estimate, so you can track
   whether the student is actually improving. `--mcts-sims N` plays with PUCT
   search instead of raw policy (see "Move selection" below).
5. **`auto_train.py`** — unattended version of `train.py`: keeps training
   epochs with early stopping (on validation loss) instead of a fixed epoch
   count, checkpointing the best model as it goes and periodically running a
   `evaluate.py`-style Stockfish match for a human-readable strength readout.
6. **`auto_pipeline.py`** — the full unattended loop: generate data, train to
   plateau (`auto_train`'s inner loop), generate *more* data, train again,
   repeat — until more data stops improving measured playing strength. This
   is what you actually want to background and leave running. See
   "Unattended training" below.
7. **`uci_engine.py`** — wraps the trained model in a minimal UCI protocol so
   it can be dropped into `lichess-bot` (or any UCI-speaking GUI/arena).

Move encoding is `from_square * 64 + to_square` (4096 classes) with the board
always oriented to the side to move; under-promotions collapse to the queen-
promotion class (the model always promotes to queen — a documented v1
limitation, see below).

### Move selection (`play.py`)

The same net supports three strengths of play, cheapest first — all share the
`--no-value-lookahead` / `--mcts-sims` flags across `evaluate.py`,
`auto_train.py`, `auto_pipeline.py`, and `uci_engine.py`:

1. **Greedy policy** (`--no-value-lookahead`) — play the policy head's argmax
   legal move. One net call, no lookahead.
2. **1-ply value lookahead** (default) — evaluate the policy's top-K
   candidates with the value head and keep the one the opponent likes least.
   One extra batched net call, no tree.
3. **PUCT search** (`--mcts-sims N`, e.g. `200`–`800`) — AlphaZero-style
   Monte-Carlo tree search: the **policy head** supplies the priors that steer
   which moves get explored, the **value head** evaluates the leaves (no random
   rollouts), and the move actually played is the **most-visited** root child —
   the one that survived deeper scrutiny. This looks several plies deep along
   the lines that matter, so it catches the tactical blunders that one-shot
   policy play (1 and 2) makes, which is what caps a distilled policy net's
   strength well below its teacher. Cost is one net call per simulation
   (~1–3 ms each here), so `--mcts-sims` is a direct speed↔strength knob and
   `--c-puct` (default 1.5) trades exploration against exploitation.

Selection order: `--mcts-sims > 0` runs PUCT; otherwise `--no-value-lookahead`
picks between 1 and 2. The PUCT formula and tree logic are documented in
`play.py`'s `run_mcts`.

## Setup

Stockfish and the Python deps are already installed into the shared repo
`venv` (per the repo's `CLAUDE.md` convention — one venv, `requirements.txt`
kept in sync via `pip freeze`).

```bash
brew install stockfish   # already done
cd monodump
source venv/bin/activate
```

## Running the pipeline

All commands below assume `cd chess-dl/src && source ../../venv/bin/activate`.

```bash
# 1. Generate data (Stockfish self-play). Start small, scale up once it works.
python generate_data.py --games 200 --depth 10 --multipv 5 \
    --out ../data/games_001.jsonl

# 2. Build a training set from one or more JSONL shards.
python build_dataset.py ../data/games_001.jsonl --out ../data/dataset.npz

# 3. Train the student net.
python train.py --data ../data/dataset.npz --epochs 20 --batch-size 256 \
    --channels 64 --blocks 4 --out ../checkpoints/chessnet.npz

# 4. Check strength against a rating-limited Stockfish.
python evaluate.py --checkpoint ../checkpoints/chessnet.npz \
    --channels 64 --blocks 4 --games 20 --sf-elo 1350

# 4b. Same, but play with PUCT search — expect a large strength jump over the
#     raw policy net (this is the biggest single lever for playing strength).
python evaluate.py --checkpoint ../checkpoints/chessnet.npz \
    --channels 64 --blocks 4 --games 20 --sf-elo 1350 --mcts-sims 400
```

Repeat 1–4 with more games / higher Stockfish depth / a bigger model
(`--channels`, `--blocks`) as the student's strength plateaus. `train.py`
takes `--init-from` to continue training an existing checkpoint on new data
instead of starting over.

## Unattended training

`auto_pipeline.py` is the script to background and forget. It runs the whole
loop end to end — generate self-play data, train to a plateau, generate more
data, train again — climbing an **Elo ladder** against Stockfish as it goes,
and stops once it either reaches the top rung or genuinely stops improving.

**Recommended command (copy-paste).** Self-contained — run it from the repo
root. It backgrounds the run and tails the round-level log; the tuned
defaults below are the ones to start from:

```bash
cd chess-dl/src && source ../../venv/bin/activate

python auto_pipeline.py \
    --data-path ../data/self_play.jsonl --out-dir ../checkpoints/auto \
    --channels 64 --blocks 4 \
    --games-per-round 200 --depth 10 --multipv 5 \
    --patience 10 --round-patience 5 \
    --lr 1e-3 --lr-decay 0.9 --min-lr 2e-4 --weight-decay 1e-4 \
    --sf-elo-start 1350 --sf-elo-step 100 --sf-elo-max 2400 \
    --mcts-sims 400 \
    > ../checkpoints/auto_pipeline.out 2>&1 &

tail -f ../checkpoints/auto/rounds.csv   # one line per round: Elo rung + strength trend
# tail -f ../checkpoints/auto/log.csv    # one line per epoch: training detail within a round
```

This reuses whatever is already in `../data/self_play.jsonl` (it gets
re-encoded and de-duplicated at the start of round 1, so a previous run's data
is picked up automatically) and starts training a fresh model on it. To
instead **resume the model** from a previous run's checkpoint rather than
retraining from scratch, add `--init-from ../checkpoints/auto/best.npz`.

Watch the first few rows of `rounds.csv`: with the fixes above, `best_val_loss`
should stop climbing round-to-round and `round_eval_elo_gap` should trend up
(less negative) instead of sliding — the earlier symptom was both going the
wrong way every round.

Add `--mcts-sims 400` to evaluate each round's strength *with* PUCT search
(see "Move selection" above). This is slower per round but measures the
strength you'll actually deploy with on Lichess, and — because the outer loop's
Elo-ladder promotion is gated on that score — lets the curriculum climb rungs
the raw policy net can't clear on its own. Leave it off for the fastest rounds
if you only care about the training-loss trend.

It's two nested early-stopping loops:

- **Inner (per round, epochs):** trains on the data accumulated so far,
  gated on **validation loss** — cheap to compute every epoch, and a good
  proxy for "still learning from this dataset." Stops after `--patience`
  epochs without a `--min-delta` improvement. The validation set is held out
  **by whole game** (see `build_dataset.py`'s `G` groups), so val_loss isn't
  flattered by near-duplicate positions from the same game landing in both
  splits. Because each round warm-starts from an already-fit model, the best
  checkpoint is reached within the first few epochs — so `--patience` is kept
  small (default 10); a large value just burns epochs overfitting.
- **Outer (across rounds):** after each round, plays `--round-eval-games`
  games against Stockfish at the *current Elo rung* and compares the result
  to previous rounds at that same rung. This — not validation loss — gates
  the outer loop, because each round's dataset is bigger and different from
  the last, so val_loss isn't comparable round-to-round the way it is
  *within* one round's fixed dataset; measured strength against a constant
  opponent is.

**The opponent isn't fixed — it's a ladder.** A constant-Elo Stockfish is a
bad outer-loop signal on its own: once the student reliably beats it, every
later round reports basically the same score with nothing left to tell
"still improving" from "plateaued" apart — the ceiling becomes the
opponent, not the model. So the target `UCI_Elo` starts at `--sf-elo-start`
(Stockfish's practical floor is ~1320) and rises by `--sf-elo-step` any time
a round's score against the current rung reaches `--promotion-score`
(default 0.5 — break-even), up to `--sf-elo-max` (default 2400, FIDE's
International Master threshold). A level-up always counts as progress and
resets the round-patience counter — it isn't a "stall" even though score
legitimately drops back toward 0 against the harder opponent that follows.
Reaching and beating `--sf-elo-max` stops the run as a success.

Stops when: **(a)** the student beats Stockfish at `--sf-elo-max` — success;
or **(b)** score at the *current* rung hasn't improved by more than
`--round-min-delta` for `--round-patience` rounds — plateaued, likely
capacity-limited (try bumping `--channels`/`--blocks` and resuming with
`--init-from`); or **(c)** `--max-rounds` as a backstop.

Data accumulates in `--data-path` (appended every round, like
`generate_data.py` does on its own) and gets fully re-encoded (and
de-duplicated) into `../checkpoints/auto/dataset.npz` each round, so later
rounds train on all self-play data generated so far. The **model** stays in
memory across rounds — each round warm-starts from exactly where the previous
round's best checkpoint left off — but the **optimizer is rebuilt fresh each
round**, with a learning rate that decays across rounds (`--lr-decay`, floored
at `--min-lr`) and AdamW weight decay (`--weight-decay`). That combination is
what keeps the loop from slowly regressing: at each round's end the model is
rolled back to its *best* weights, so carrying stale Adam momentum (which
describes the later, over-fit weights) onto them would nudge the next round
off the good minimum and compound every round. A fresh, decayed-LR optimizer
keeps momentum matched to the weights it's training and damps the immediate
per-round overfitting. `best.npz` is always the best checkpoint from the
most-recently-completed round (what you want for
`evaluate.py`/`uci_engine.py`); `latest.npz` is the most recent epoch,
useful for resuming with `--init-from` if you kill the run early.

`--games-per-round`, `--depth`, etc. are `generate_data.py`'s knobs, passed
straight through and reused every round; `--patience`/`--min-delta`/
`--eval-every` control the inner loop (same meaning as in `auto_train.py`),
and `--lr`/`--lr-decay`/`--min-lr`/`--weight-decay` control the per-round
optimizer (learning-rate schedule across rounds + AdamW regularization);
`--round-patience`/`--round-min-delta`/`--round-eval-games`/`--max-rounds`/
`--sf-elo-start`/`--sf-elo-step`/`--sf-elo-max`/`--promotion-score` control
the outer loop and the Elo ladder.

If you'd rather run the loops separately (e.g. to inspect/curate data or
manually raise the Elo target between rounds), `generate_data.py` →
`build_dataset.py` → `auto_train.py --sf-elo <rung> --init-from <previous
best>` do the same thing manually, one round at a time.

**Compute notes:** MLX runs on the Mac's GPU by default (`mx.default_device()`
reports `gpu`) and is the primary path here. If a dataset/model gets too big
for the laptop, the `.npz` format from `build_dataset.py` is plain NumPy, so
the same data can be loaded by a PyTorch training script on Colab — only
`model.py`, `train.py`, and `auto_train.py`/`auto_pipeline.py`'s training
calls would need a PyTorch port; `encoding.py`, `generate_data.py`, and
`build_dataset.py` stay as-is.

## Arena: playing on Lichess

`uci_engine.py` speaks UCI, so it plugs into
[lichess-bot](https://github.com/lichess-bot-devs/lichess-bot) directly.

1. **Create a dedicated Lichess account** for the bot (bot accounts can't be
   converted back to a normal account — don't use your main one).
2. **Upgrade it to a BOT account**: generate a personal API token with the
   `bot:play` scope (Lichess → Preferences → API access tokens), then:
   ```bash
   curl -d '' https://lichess.org/api/bot/account/upgrade \
       -H "Authorization: Bearer <token>"
   ```
3. **Clone lichess-bot** (outside this repo, or as a sibling folder) and
   follow its setup instructions to install its own dependencies:
   ```bash
   git clone https://github.com/lichess-bot-devs/lichess-bot.git
   ```
4. **Point it at our engine** in `lichess-bot/config.yml`:
   ```yaml
   token: "<your bot token>"
   engine:
     dir: "/Users/trung/Documents/personal/monodump/chess-dl/src"
     name: "uci_engine.py"
     protocol: "uci"
     working_dir: "/Users/trung/Documents/personal/monodump/chess-dl/src"
     interpreter: "/Users/trung/Documents/personal/monodump/venv/bin/python"
     interpreter_options: "uci_engine.py --checkpoint ../checkpoints/auto/best.npz --channels 64 --blocks 4 --mcts-sims 400"
   ```
   (Exact key names/nesting depend on the lichess-bot version — check its
   `config.yml.default` template. The key point: it needs to invoke the repo
   venv's Python running `uci_engine.py` with the right `--checkpoint`.
   `--mcts-sims 400` makes it play with PUCT search — strongly recommended for
   real games; raise it for more strength at the cost of slower moves, or drop
   it for the faster raw-policy play.)
5. **Run it**: `python lichess-bot.py` (from inside the lichess-bot repo,
   its own venv). It will accept challenges / enter tournaments per its
   config.

Since bot-account creation and token generation require the account owner,
these steps are manual — the pipeline above only prepares the engine that
gets plugged in.

## Known v1 limitations

- Under-promotions (to knight/bishop/rook) are never produced; always queen.
- No opening book / endgame tablebase — everything is learned from the
  teacher's shallow-depth self-play data.
- `evaluate.py`'s Elo estimate is a rough single-match-set approximation, not
  a calibrated rating.
