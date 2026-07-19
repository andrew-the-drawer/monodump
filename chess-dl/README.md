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
   (`X`: 8x8x17 board planes, `P`: 4096-way policy target, `V`: scalar value)
   and saves a `.npz` shard. Board/move encoding lives in `encoding.py` and is
   framework-agnostic (plain NumPy).
3. **`train.py`** — trains `ChessNet` (`model.py`, MLX) on the `.npz` dataset
   with a combined cross-entropy (policy) + MSE (value) loss.
4. **`evaluate.py`** — plays the student against Stockfish at a capped
   `UCI_Elo` and reports W/D/L plus a rough Elo-gap estimate, so you can track
   whether the student is actually improving.
5. **`uci_engine.py`** — wraps the trained model in a minimal UCI protocol so
   it can be dropped into `lichess-bot` (or any UCI-speaking GUI/arena).

Move encoding is `from_square * 64 + to_square` (4096 classes) with the board
always oriented to the side to move; under-promotions collapse to the queen-
promotion class (the model always promotes to queen — a documented v1
limitation, see below).

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
```

Repeat 1–4 with more games / higher Stockfish depth / a bigger model
(`--channels`, `--blocks`) as the student's strength plateaus. `train.py`
takes `--init-from` to continue training an existing checkpoint on new data
instead of starting over.

**Compute notes:** MLX runs on the Mac's GPU by default (`mx.default_device()`
reports `gpu`) and is the primary path here. If a dataset/model gets too big
for the laptop, the `.npz` format from `build_dataset.py` is plain NumPy, so
the same data can be loaded by a PyTorch training script on Colab — only
`model.py` and `train.py` would need a PyTorch port; `encoding.py`,
`generate_data.py`, and `build_dataset.py` stay as-is.

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
     interpreter_options: "uci_engine.py --checkpoint ../checkpoints/chessnet.npz --channels 64 --blocks 4"
   ```
   (Exact key names/nesting depend on the lichess-bot version — check its
   `config.yml.default` template. The key point: it needs to invoke the repo
   venv's Python running `uci_engine.py` with the right `--checkpoint`.)
5. **Run it**: `python lichess-bot.py` (from inside the lichess-bot repo,
   its own venv). It will accept challenges / enter tournaments per its
   config.

Since bot-account creation and token generation require the account owner,
these steps are manual — the pipeline above only prepares the engine that
gets plugged in.

## Known v1 limitations

- Move selection is greedy policy + a cheap 1-ply value-head lookahead over
  the top candidates (`play.py`), not real search (no MCTS/alpha-beta). This
  caps strength well below Stockfish regardless of net quality.
- Under-promotions (to knight/bishop/rook) are never produced; always queen.
- No opening book / endgame tablebase — everything is learned from the
  teacher's shallow-depth self-play data.
- `evaluate.py`'s Elo estimate is a rough single-match-set approximation, not
  a calibrated rating.
