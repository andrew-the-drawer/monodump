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

1. **`generate_data.py`** — Stockfish always **labels** every position (its
   top-K moves via MultiPV, recorded as a soft policy target — softmax over
   centipawn scores — plus the best move's eval as a value target in
   `[-1, 1]`). Who **plays** the moves that decide which positions get
   labeled is a separate, configurable choice (a few random opening plies
   either way, for diversity):
   - **off-policy (default)** — Stockfish plays both sides, temperature-
     sampled afterwards so it doesn't just replay one line every game.
   - **on-policy (`--student-checkpoint`)** — the student itself plays both
     sides instead (optionally with MCTS/value lookahead). See "On-policy
     self-play" below for why this matters. Output: JSONL either way.
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

### On-policy self-play (`generate_data.py` / `auto_pipeline.py`)

Plain distillation trains the student only on positions Stockfish itself
would visit playing well. But at deployment the student plays its *own*
moves — the moment it makes a small error, it drifts onto a position type
under-represented in that training data, has no signal for how to respond,
and is more likely to err again. This is the standard covariate-shift
problem in behavioral cloning/imitation learning: train-time and test-time
state distributions diverge, and the gap is worst exactly when the student
is weakest.

The fix is **DAgger** (Dataset Aggregation — Ross, Gordon & Bagnell, 2011,
[arXiv:1011.0686](https://arxiv.org/abs/1011.0686)): let the *learner*
choose which states to visit, and keep the *expert* only for labeling them.
Concretely here: the student (optionally driven by MCTS/value lookahead, the
same move-selection code `evaluate.py` uses) plays both sides of the
self-play game, while Stockfish still analyses and labels every position
reached, exactly as before. The dataset then matches what the student
actually encounters at play time — including the positions its own mistakes
lead it into — instead of only the positions a flawless teacher would reach.

- `generate_data.py --student-checkpoint <path>` turns this on for a
  standalone run (`--student-temp`/`--mcts-sims`/`--c-puct`/
  `--no-value-lookahead` control how the student plays, same meaning as
  `evaluate.py`).
- `auto_pipeline.py --on-policy-from-round N` (default 2) turns this on
  automatically starting at round `N`, using the in-memory model straight
  from the previous round's best checkpoint — no separate checkpoint path
  needed. Round 1 always uses Stockfish self-play, since a freshly
  initialized (or still-weak, freshly warm-started) student has nothing
  useful to play yet; this mirrors DAgger's own first iteration, which is
  pure expert rollout. Set it to `1` to skip the bootstrap round entirely,
  e.g. when resuming `--init-from` an already-decent checkpoint.
- `--student-play-temp` (auto_pipeline) / `--student-temp` (generate_data)
  samples the student's move instead of always taking its single best one
  (by MCTS visit count, or by policy softmax without MCTS) — needed because a
  fully deterministic student would replay the exact same game every round.

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
# 1. Generate data (off-policy: Stockfish self-play). Start small, scale up
#    once it works.
python generate_data.py --games 200 --depth 10 --multipv 5 \
    --out ../data/games_001.jsonl

# 1b. Once you have a checkpoint, generate on-policy data instead (student
#     plays, Stockfish still labels) — see "On-policy self-play" above.
python generate_data.py --games 200 --depth 10 --multipv 5 \
    --out ../data/games_002.jsonl \
    --student-checkpoint ../checkpoints/chessnet.npz --mcts-sims 400

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

Repeat 1(b)–4 with more games / higher Stockfish depth / a bigger model
(`--channels`, `--blocks`) as the student's strength plateaus, switching to
1b (on-policy) once a checkpoint exists. `train.py` takes `--init-from` to
continue training an existing checkpoint on new data instead of starting
over.

## Unattended training

`auto_pipeline.py` is the script to background and forget. It runs the whole
loop end to end — generate self-play data, train to a plateau, generate more
data, train again — climbing an **Elo ladder** against Stockfish as it goes,
and stops once it either reaches the top rung or genuinely stops improving.

**Recommended command (copy-paste).** Self-contained — run from the repo root;
it backgrounds the run and tails the round-level log. Use the first variant for
a brand-new model, the second to continue an existing run. The tuned flags
shown are the ones to start from. Both default to **on-policy self-play from
round 2 onward** (`--on-policy-from-round 2`) — see "On-policy self-play"
above; `--mcts-sims 400` doubles as both the evaluation *and* the on-policy
move-selection strength.

**First run (fresh model, from scratch):**

```bash
cd chess-dl/src && source ../../venv/bin/activate

python auto_pipeline.py \
    --data-path ../data/self_play.jsonl --out-dir ../checkpoints/auto \
    --channels 64 --blocks 4 \
    --games-per-round 200 --depth 10 --multipv 5 --opening-random-plies 10 \
    --patience 10 --round-patience 5 \
    --lr 1e-3 --lr-decay 0.9 --min-lr 2e-4 --weight-decay 1e-4 \
    --sf-elo-start 1350 --sf-elo-step 100 --sf-elo-max 2400 \
    --mcts-sims 400 \
    > ../checkpoints/auto_pipeline.out 2>&1 &

tail -f ../checkpoints/auto/rounds.csv   # one line per round: Elo rung + strength trend
# tail -f ../checkpoints/auto/log.csv    # one line per epoch: training detail within a round
```

**Resuming from an existing checkpoint** (continue a previous run rather than
retraining from scratch) — the recommended way to keep a run going. It
warm-starts the model from `best.npz` and keeps extending the same data file
with *new* games (the entropy-seeded RNG guarantees they aren't replays):

```bash
python auto_pipeline.py \
    --data-path ../data/self_play.jsonl --out-dir ../checkpoints/auto \
    --channels 64 --blocks 4 \
    --games-per-round 200 --depth 10 --multipv 5 --opening-random-plies 10 \
    --patience 10 --round-patience 5 \
    --lr 1e-3 --lr-decay 0.9 --min-lr 2e-4 --weight-decay 1e-4 \
    --sf-elo-start 1350 --sf-elo-step 100 --sf-elo-max 2400 \
    --mcts-sims 400 \
    --init-from ../checkpoints/auto/best.npz \
    --on-policy-from-round 1 \
    > ../checkpoints/auto_pipeline.out 2>&1 &
```

`--on-policy-from-round 1` here skips the bootstrap round: `best.npz` is
already a real, non-random checkpoint, so there's no reason to spend round 1
on off-policy Stockfish self-play the way a from-scratch run needs to.

Both reuse whatever is already in `../data/self_play.jsonl` (it gets re-encoded
and de-duplicated at the start of round 1, so prior data is picked up
automatically). `--init-from` loads the old weights into memory *before* the
loop begins, so it's safe even though the run overwrites `best.npz`/`latest.npz`
as it trains.

**Do I need to delete old checkpoints / data before re-running?** No — and you
shouldn't delete the data:

- **`self_play.jsonl` — keep it.** Those are real Stockfish-labeled positions;
  deleting throws away signal. Duplicate lines from earlier fixed-seed runs are
  harmless (de-dup drops them at encode time), and new rounds now *extend* the
  file with fresh positions.
- **`best.npz` / `latest.npz` — keep them.** Warm-starting with `--init-from
  ../checkpoints/auto/best.npz` (the ~0.40-vs-SF@1350 model) beats starting from
  random weights. They get overwritten during the run regardless.
- **`rounds.csv` / `log.csv` — optionally archive them.** The pipeline *appends*
  to these and restarts its round/epoch counters at 1 each run, so a resumed run
  tacks new `round 1, 2, …` rows onto the old ones — cosmetically messy but not
  functionally harmful (the outer-loop patience state is in-memory and resets
  each run). For a clean strength trend, `mv rounds.csv rounds.prev.csv` (same
  for `log.csv`) before resuming, or point `--out-dir` at a new folder. Do this
  when a run's methodology actually changes (e.g. the first run after adding
  on-policy self-play) so the trend isn't a mix of off-policy and on-policy
  rounds — the checkpoints and data themselves stay valid across the switch,
  only the round-by-round comparison gets muddled.

**Self-play RNG (why data now keeps growing across runs).** `generate_game` is
deterministic given its RNG — the same random opening plies produce the same
fixed-depth Stockfish replies, the same positions, and even the same
`game_id`. A *fixed* `--seed` therefore makes a restarted/resumed run replay
byte-identical games, which `build_dataset` then de-duplicates away, silently
freezing the dataset (the symptom: `total N unique, M game-groups` never
changing round-to-round even as `+positions` are "added"). So `--seed` now
defaults to `<0` = **system entropy**: every run generates genuinely new games.
Pass an explicit `--seed` only if you want reproducibility — it's still made
resume-safe by offsetting with the amount of data already on disk, so appends
continue the sequence rather than repeat it. If you have an old data file
generated under the previous fixed-seed default, its duplicate lines are
harmless (de-dup drops them at encode time), but new rounds will now extend it
with fresh positions.

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
the outer loop and the Elo ladder; `--on-policy-from-round`/
`--student-play-temp` (plus the shared `--mcts-sims`/`--c-puct`/
`--no-value-lookahead`) control on-policy self-play (see "On-policy
self-play" above).

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
