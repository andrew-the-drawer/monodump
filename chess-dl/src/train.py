"""Train the student ChessNet on a distilled Stockfish dataset (MLX)."""

import argparse
import time
from pathlib import Path

import mlx.core as mx
import mlx.nn as nn
import mlx.optimizers as optim
import numpy as np

from model import ChessNet


def load_dataset(path: str, val_fraction: float, seed: int):
    data = np.load(path)
    X, P, V = data["X"], data["P"], data["V"]
    n = len(V)
    rng = np.random.default_rng(seed)
    perm = rng.permutation(n)
    n_val = max(1, int(n * val_fraction))
    val_idx, train_idx = perm[:n_val], perm[n_val:]
    to_mx = lambda a: mx.array(a)
    train = (to_mx(X[train_idx]), to_mx(P[train_idx]), to_mx(V[train_idx]))
    val = (to_mx(X[val_idx]), to_mx(P[val_idx]), to_mx(V[val_idx]))
    return train, val


def loss_fn(model, x, p_target, v_target, value_weight):
    p_logits, v_pred = model(x)
    # Soft-target cross-entropy written explicitly as -(target . log_softmax).
    # This is bounded below by 0 for any non-negative target, so a stray
    # un-normalized row can't make the loss diverge. (mx.nn cross_entropy
    # computes logsumexp - sum(target * logits), which is only a valid
    # cross-entropy when the target sums to 1 -- otherwise it is unbounded
    # below and training will happily blow the logits up to drive it to -inf.)
    log_probs = nn.log_softmax(p_logits, axis=-1)
    policy_loss = -(p_target * log_probs).sum(axis=-1).mean()
    value_loss = nn.losses.mse_loss(v_pred, v_target, reduction="mean")
    return policy_loss + value_weight * value_loss, (policy_loss, value_loss)


def iterate_batches(X, P, V, batch_size, rng_key):
    n = X.shape[0]
    perm = mx.array(np.random.default_rng(int(rng_key)).permutation(n))
    for start in range(0, n, batch_size):
        idx = perm[start : start + batch_size]
        yield X[idx], P[idx], V[idx]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data", default="../data/dataset.npz")
    ap.add_argument("--epochs", type=int, default=10)
    ap.add_argument("--batch-size", type=int, default=256)
    ap.add_argument("--lr", type=float, default=1e-3)
    ap.add_argument("--channels", type=int, default=64)
    ap.add_argument("--blocks", type=int, default=4)
    ap.add_argument("--value-weight", type=float, default=1.0)
    ap.add_argument("--val-fraction", type=float, default=0.1)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--out", default="../checkpoints/chessnet.npz")
    ap.add_argument("--init-from", default=None, help="resume/fine-tune from an existing checkpoint")
    args = ap.parse_args()

    (Xtr, Ptr, Vtr), (Xval, Pval, Vval) = load_dataset(args.data, args.val_fraction, args.seed)
    print(f"train={Xtr.shape[0]} val={Xval.shape[0]}")

    model = ChessNet(channels=args.channels, num_blocks=args.blocks)
    if args.init_from:
        model.load_weights(args.init_from)
    mx.eval(model.parameters())

    optimizer = optim.Adam(learning_rate=args.lr)
    loss_and_grad = nn.value_and_grad(model, loss_fn)

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)

    for epoch in range(args.epochs):
        model.train()
        t0 = time.time()
        epoch_loss = epoch_ploss = epoch_vloss = 0.0
        nbatches = 0
        for xb, pb, vb in iterate_batches(Xtr, Ptr, Vtr, args.batch_size, rng_key=epoch):
            (loss, (ploss, vloss)), grads = loss_and_grad(model, xb, pb, vb, args.value_weight)
            optimizer.update(model, grads)
            mx.eval(model.parameters(), optimizer.state)
            epoch_loss += loss.item()
            epoch_ploss += ploss.item()
            epoch_vloss += vloss.item()
            nbatches += 1

        model.eval()
        val_loss, (val_ploss, val_vloss) = loss_fn(model, Xval, Pval, Vval, args.value_weight)
        dt = time.time() - t0
        print(
            f"epoch {epoch + 1}/{args.epochs} "
            f"train_loss={epoch_loss / nbatches:.4f} (p={epoch_ploss / nbatches:.4f} v={epoch_vloss / nbatches:.4f}) "
            f"val_loss={val_loss.item():.4f} (p={val_ploss.item():.4f} v={val_vloss.item():.4f}) "
            f"[{dt:.1f}s]"
        )

    model.save_weights(str(out_path))
    print(f"saved weights to {out_path}")


if __name__ == "__main__":
    main()
