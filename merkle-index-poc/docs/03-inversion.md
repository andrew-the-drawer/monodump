# 03 · Embedding-inversion attack

The server keeps no code, only vectors. This doc runs an attack that turns those vectors back into text, using nothing but a copy of `index.db`.

## What an inversion attack is

An embedding model maps text to a vector. People sometimes treat that vector as a one-way hash of meaning, but it isn't one. It is a dense, lossy summary that keeps a lot of the original text: which words appear, names, numbers, word order.

**vec2text** (Morris et al., 2023, *Text Embeddings Reveal (Almost) As Much As Text*) inverts embeddings iteratively:

```
target vector e*
  │
  ├─ 1. inversion model: e*            → first guess  x0
  └─ 2. repeat N times:
        embed(x_t) = e_t
        corrector: (e*, e_t, x_t)      → x_{t+1}       # "move the text so its embedding moves toward e*"
```

The attacker needs only (a) the vectors and (b) the ability to query the same embedding model, to compute `e_t`. For GTR-T5-base the paper reports about 92% exact recovery of 32-token inputs.

## How the demo is set up

`scripts/inversion_demo.sh`:

1. Writes a small victim repo: `app/billing.py` (with a fake Stripe key) and `app/notes.md` (an M&A secret and a password).
2. Runs the normal pipeline with `MINDEX_EMBEDDER=gtr`. `GtrEmbedder` computes vectors the way vec2text expects: T5 encoder plus mean pooling.
3. Runs `scripts/invert_attack.py`, which plays two separate roles:
   - **ATTACKER**: opens `index.db` with `sqlite3` and reads `chunks ⋈ embeddings`. It has no key and no workspace, only ciphertext paths, line numbers and vectors. It runs vec2text with 20 correction steps and beam width 4.
   - **EVALUATOR**: has the key and the workspace. It decrypts each pointer, reads the true lines and scores the attacker. Score = word recall, with identifiers split on `_` and camelCase.
4. Repeats with 1-line chunks, then 30-line chunks.

## Results (CPU, Apple silicon, about 3 minutes for each chunk size)

### 1 line per chunk: mean word recall 81%

| original | recovered from the DB alone |
|---|---|
| `The acquisition of Globex closes on March 3rd, do not tell the sales team.` | `The acquisition of Globex closes on March 3rd, do not tell the sales team .` |
| `Database password for staging is tangerine-falcon-42.` | `Database password for staging is (falcon-tangerine-42` |
| `# Refunds over 500 dollars need manager approval.` | `Refunds over 500 dollars need manager approval` |
| `def charge_customer(customer_id, amount_cents):` | `charge_customer, def_customer_id ( = amount_cents)` |
| `def refund(charge_id, reason):` | `def: refund (charge_id, reason` |
| `STRIPE_KEY = "sk_live_51HfakeKEYforDEMOonly"` | `fake= STRIKE_StP_DESKMO_LIVEonly>/ref>keys` |

### 30 lines per chunk (each file becomes one vector): mean word recall 41%

| original | recovered |
|---|---|
| `notes.md` (2 lines, the M&A note and the password) | `The acquisition of Globex closes on March 3, and do not tell the sales management team. Database password: tar-falcon-59.` |
| `billing.py` (7 lines of code) | `= $1 (stripe)create_key_receiv_order_valid_receiv_detail_valid_back` (9%) |

Runs aren't bit-for-bit reproducible (beam search and float noise), so your numbers will differ by a few points.

## Reading the results

- **Short text is recovered almost verbatim.** This is the regime the public inverter was trained on (32 tokens). Comments and prose are the easiest.
- **Natural-language secrets leak.** The password came back with its words swapped. An attacker who has `falcon`, `tangerine` and `42` needs only a few guesses.
- **High-entropy secrets survive *this* inverter.** The random-looking API key was not recovered, but its structure (`LIVE`, `fake`, `KEY`) partly leaked. Don't count on this: a stronger inverter, or one trained on code, would do better.
- **Longer chunks help, but only somewhat.** A 30-line chunk packs much more text into the same 768 numbers, so recovery falls sharply for code (9%). But a short file is a short chunk however large the chunk size, and `notes.md` still leaked its meaning. The public inverter was trained on 32-token text. An attacker who trains on longer code chunks would recover more.
- **Ciphertext paths didn't help the defender much.** The attacker didn't need a file name to learn about the Globex deal.

So the accurate claims are:

| claim | true? |
|---|---|
| "The server doesn't store your code." | Yes. The DB holds no plaintext. |
| "Your code can't be recovered from what the server stores." | No. Embeddings are sensitive data. |

## Mitigations, roughly from most to least effective

1. **Treat vectors as source code**: encrypt them at rest, restrict access, use short retention, and delete them when the workspace is deleted.
2. **Don't index secrets**: secret scanning before upload, `.gitignore`/`.mindexignore`, and avoiding `.env`-style files.
3. **Keep the embedding model private.** The attacker then has to train a surrogate, which raises the cost but doesn't block the attack. Inversions have been shown to transfer between models after a small alignment step.
4. **Add noise to embeddings** (Gaussian noise, or quantization). This lowers inversion quality, at some cost to retrieval quality.
5. **Use larger, syntax-aware chunks.** This lowers recovery per chunk, but small files and comments still leak.

## Running it

```bash
./scripts/inversion_demo.sh                 # N=6 chunks attacked per size, STEPS=20
N=9 STEPS=50 ./scripts/inversion_demo.sh    # more chunks, more correction steps (slower)
```

## Compatibility notes (vec2text 0.0.13 with transformers 5.x)

`invert_attack.py` works around three incompatibilities rather than pinning old versions:

1. vec2text's model `__init__` calls `from_pretrained`, which transformers 5 forbids (models are now built on the meta device). The script constructs each model normally, then loads the checkpoint shards itself.
2. vec2text loads its internal GTR model in fp16 and the rest in fp32. On MPS this crashes with a matmul assertion. The script casts everything to fp32 and runs on CPU through `TrainingArguments(use_cpu=True)`.
3. `GenerationConfig.length_penalty` now defaults to `None`, but vec2text raises a value to that power. The script sets it to 1.0, the old default.
