"""Embedding-inversion attack against the server's database (docs/03-inversion.md).

Two roles, kept visibly separate:

  ATTACKER  has a copy of index.db (breach, insider, leaked backup). Reads the
            stored GTR vectors and runs vec2text to reconstruct text. Never
            touches the key or the workspace.
  EVALUATOR has the workspace + key, and only exists to score the attack:
            it decrypts the pointer and reads the true lines for comparison.

Requires the server to have indexed with MINDEX_EMBEDDER=gtr (vec2text's
public inverter is trained for GTR-T5-base).

    python scripts/invert_attack.py --db .demo-inv/server/index.db \\
        --workspace-dir .demo-inv/victim --workspace victim -n 8
"""

from __future__ import annotations

import argparse
import re
import sqlite3
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

# Words, with identifiers split on _ and camelCase: charge_customer -> charge, customer.
TOKEN = re.compile(r"[A-Z]?[a-z]+|[A-Z]+(?![a-z])|\d+")


def attacker_load(db: Path, workspace: str, n: int) -> list[tuple[str, int, int, np.ndarray]]:
    con = sqlite3.connect(db)
    rows = con.execute(
        """
        SELECT c.path, c.start_line, c.end_line, e.vector
        FROM chunks c JOIN embeddings e ON e.chunk_hash=c.chunk_hash AND e.model='gtr'
        WHERE c.workspace=? ORDER BY c.path, c.start_line LIMIT ?
        """,
        (workspace, n),
    ).fetchall()
    return [(p, s, e, np.frombuffer(v, dtype=np.float32)) for p, s, e, v in rows]


def _load_vec2text_model(cls, repo: str):
    """Stand-in for `cls.from_pretrained(repo)`.

    vec2text's model __init__ itself calls from_pretrained (for the T5 backbone),
    which transformers>=5 rejects because from_pretrained now builds models on
    the meta device. So: construct normally, then load the shards ourselves.
    """
    import json

    import torch
    from huggingface_hub import snapshot_download
    from safetensors.torch import load_file

    folder = Path(snapshot_download(repo))
    model = cls(cls.config_class.from_pretrained(folder))
    for index_name, loader in (("model.safetensors.index.json", load_file),
                               ("pytorch_model.bin.index.json", lambda f: torch.load(f, map_location="cpu"))):
        if (folder / index_name).exists():
            shards = sorted(set(json.loads((folder / index_name).read_text())["weight_map"].values()))
            break
    else:
        shards, loader = ["model.safetensors"], load_file
    state = {}
    for shard in shards:
        state.update(loader(folder / shard))
    missing, unexpected = model.load_state_dict(state, strict=False)
    # The frozen GTR embedder inside the inversion model is loaded by __init__, not the checkpoint.
    real_missing = [k for k in missing if not k.startswith("embedder.")]
    if real_missing or unexpected:
        raise RuntimeError(f"{repo}: missing={real_missing[:5]} unexpected={unexpected[:5]}")
    return model.eval()


def attacker_invert(vectors: np.ndarray, steps: int) -> list[str]:
    import torch
    import vec2text

    corrector = vec2text.load_corrector(
        _load_vec2text_model(vec2text.models.InversionModel, "jxm/gtr__nq__32"),
        _load_vec2text_model(vec2text.models.CorrectorEncoderModel, "jxm/gtr__nq__32__correct"),
    )
    # vec2text loads its internal GTR embedder in fp16 but the rest in fp32, which
    # breaks its matmuls (on MPS as an assertion, on CPU as a dtype error). Cast
    # everything to fp32 and run on CPU: vec2text reads self.args.device
    # everywhere, so both trainers get CPU-only args. Fast enough for a few dozen chunks.
    import tempfile

    from transformers import TrainingArguments

    cpu_args = TrainingArguments(output_dir=tempfile.mkdtemp(), use_cpu=True, report_to=[])
    for t in (corrector, corrector.inversion_trainer):
        t.args = cpu_args
        t.model.to(cpu_args.device).float()
        # transformers>=5 defaults length_penalty to None (was 1.0); vec2text exponentiates by it.
        t.model.encoder_decoder.generation_config.length_penalty = 1.0
    device = cpu_args.device
    return vec2text.invert_embeddings(
        embeddings=torch.tensor(vectors, device=device),
        corrector=corrector,
        num_steps=steps,
        sequence_beam_width=4 if steps else 0,
    )


def evaluator_truth(workspace_dir: Path, enc_path: str, start: int, end: int) -> str:
    from mindex.crypto import PathCipher, load_or_create_key

    cipher = PathCipher(load_or_create_key(workspace_dir / ".mindex" / "key"))
    rel = cipher.decrypt_path(enc_path)
    lines = (workspace_dir / rel).read_text().splitlines()
    return f"{rel}:{start}-{end}", "\n".join(lines[start - 1 : end])


def token_recall(truth: str, guess: str) -> float:
    t = {x.lower() for x in TOKEN.findall(truth)}
    g = {x.lower() for x in TOKEN.findall(guess)}
    return len(t & g) / len(t) if t else 0.0


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--db", type=Path, required=True)
    ap.add_argument("--workspace", required=True)
    ap.add_argument("--workspace-dir", type=Path, required=True)
    ap.add_argument("-n", type=int, default=8, help="how many stored chunks to attack")
    ap.add_argument("--steps", type=int, default=20, help="vec2text correction steps (0 = one-shot guess)")
    a = ap.parse_args()

    rows = attacker_load(a.db, a.workspace, a.n)
    if not rows:
        sys.exit("no GTR embeddings found; index with MINDEX_EMBEDDER=gtr")
    guesses = attacker_invert(np.stack([r[3] for r in rows]), a.steps)

    recalls = []
    for (enc_path, start, end, _), guess in zip(rows, guesses):
        where, truth = evaluator_truth(a.workspace_dir, enc_path, start, end)
        r = token_recall(truth, guess)
        recalls.append(r)
        print(f"── {where}   token recall {r:.0%}")
        print("   original :", truth.replace("\n", " ⏎ ")[:200])
        print("   recovered:", guess.replace("\n", " ⏎ ")[:200])
        print()
    print(f"mean token recall over {len(recalls)} chunks: {np.mean(recalls):.0%}")


if __name__ == "__main__":
    main()
