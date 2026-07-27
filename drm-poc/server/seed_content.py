#!/usr/bin/env python3
"""Load packaging/content/packaged/keys.json (written by package.sh) into keys.db.

Run this once after (re-)packaging content, before starting the server.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import models  # noqa: E402

CONTENT_ID = "demo"
KEYS_JSON = Path(__file__).resolve().parent.parent / "packaging" / "content" / "packaged" / "keys.json"


def main() -> int:
    if not KEYS_JSON.exists():
        print(f"missing {KEYS_JSON} — run packaging/package.sh first", file=sys.stderr)
        return 1

    models.init_db()
    entries = json.loads(KEYS_JSON.read_text())
    for tier, info in entries.items():
        models.upsert_content_key(CONTENT_ID, info["key_id"], info["key"], tier)
        print(f"seeded {CONTENT_ID}/{tier}: kid={info['key_id']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
