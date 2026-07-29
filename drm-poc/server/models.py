"""SQLite-backed storage for the three record types the license server needs.

Three separate files, matching PLAN.md's repo layout:
  - keys.db      content keys, one row per (content_id, KID).
  - devices.db   provisioned devices: identity pubkey, server-asserted
                 security level, revocation flag.
  - policies.db  per-session state used to enforce expiry, rental windows,
                 and concurrent-stream limits (Phase 4).
"""
from __future__ import annotations

import sqlite3
import time
from contextlib import contextmanager
from pathlib import Path

SERVER_DIR = Path(__file__).resolve().parent
KEYS_DB = SERVER_DIR / "keys.db"
DEVICES_DB = SERVER_DIR / "devices.db"
POLICIES_DB = SERVER_DIR / "policies.db"


@contextmanager
def _connect(path: Path):
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()


def init_db() -> None:
    with _connect(KEYS_DB) as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS content_keys (
                content_id TEXT NOT NULL,
                kid        TEXT NOT NULL,
                key        TEXT NOT NULL,
                tier       TEXT NOT NULL,
                PRIMARY KEY (content_id, kid)
            )
            """
        )

    with _connect(DEVICES_DB) as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS devices (
                device_id      TEXT PRIMARY KEY,
                pubkey_jwk     TEXT NOT NULL,
                security_level TEXT NOT NULL,
                revoked        INTEGER NOT NULL DEFAULT 0,
                created_at     REAL NOT NULL
            )
            """
        )

    with _connect(POLICIES_DB) as conn:
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS sessions (
                session_id     TEXT PRIMARY KEY,
                device_id      TEXT NOT NULL,
                content_id     TEXT NOT NULL,
                created_at     REAL NOT NULL,
                first_play_at  REAL,
                expires_at     REAL NOT NULL,
                renewed_count  INTEGER NOT NULL DEFAULT 0,
                active         INTEGER NOT NULL DEFAULT 1
            )
            """
        )


# --- content_keys -----------------------------------------------------------

def upsert_content_key(content_id: str, kid: str, key: str, tier: str) -> None:
    with _connect(KEYS_DB) as conn:
        conn.execute(
            "INSERT INTO content_keys (content_id, kid, key, tier) VALUES (?, ?, ?, ?) "
            "ON CONFLICT(content_id, kid) DO UPDATE SET key=excluded.key, tier=excluded.tier",
            (content_id, kid.lower(), key.lower(), tier),
        )


def get_content_keys(content_id: str) -> list[sqlite3.Row]:
    with _connect(KEYS_DB) as conn:
        return conn.execute(
            "SELECT * FROM content_keys WHERE content_id = ?", (content_id,)
        ).fetchall()


def get_content_key(content_id: str, kid: str) -> sqlite3.Row | None:
    with _connect(KEYS_DB) as conn:
        return conn.execute(
            "SELECT * FROM content_keys WHERE content_id = ? AND kid = ?",
            (content_id, kid.lower()),
        ).fetchone()


# --- devices -----------------------------------------------------------------

def create_device(device_id: str, pubkey_jwk: str, security_level: str) -> None:
    with _connect(DEVICES_DB) as conn:
        conn.execute(
            "INSERT INTO devices (device_id, pubkey_jwk, security_level, revoked, created_at) "
            "VALUES (?, ?, ?, 0, ?)",
            (device_id, pubkey_jwk, security_level, time.time()),
        )


def get_device(device_id: str) -> sqlite3.Row | None:
    with _connect(DEVICES_DB) as conn:
        return conn.execute(
            "SELECT * FROM devices WHERE device_id = ?", (device_id,)
        ).fetchone()


def set_device_revoked(device_id: str, revoked: bool) -> None:
    with _connect(DEVICES_DB) as conn:
        conn.execute(
            "UPDATE devices SET revoked = ? WHERE device_id = ?",
            (1 if revoked else 0, device_id),
        )


def list_devices() -> list[sqlite3.Row]:
    with _connect(DEVICES_DB) as conn:
        return conn.execute("SELECT * FROM devices ORDER BY created_at").fetchall()


# --- sessions (Phase 4 policy state) -----------------------------------------

def create_session(session_id: str, device_id: str, content_id: str, ttl_seconds: float) -> None:
    now = time.time()
    with _connect(POLICIES_DB) as conn:
        conn.execute(
            "INSERT INTO sessions (session_id, device_id, content_id, created_at, "
            "first_play_at, expires_at, renewed_count, active) "
            "VALUES (?, ?, ?, ?, NULL, ?, 0, 1)",
            (session_id, device_id, content_id, now, now + ttl_seconds),
        )


def get_session(session_id: str) -> sqlite3.Row | None:
    with _connect(POLICIES_DB) as conn:
        return conn.execute(
            "SELECT * FROM sessions WHERE session_id = ?", (session_id,)
        ).fetchone()


def mark_first_play(session_id: str) -> None:
    with _connect(POLICIES_DB) as conn:
        conn.execute(
            "UPDATE sessions SET first_play_at = ? WHERE session_id = ? AND first_play_at IS NULL",
            (time.time(), session_id),
        )


def renew_session(session_id: str, new_expires_at: float) -> None:
    with _connect(POLICIES_DB) as conn:
        conn.execute(
            "UPDATE sessions SET expires_at = ?, renewed_count = renewed_count + 1 "
            "WHERE session_id = ?",
            (new_expires_at, session_id),
        )


def count_active_sessions(exclude_session_id: str | None = None) -> int:
    now = time.time()
    with _connect(POLICIES_DB) as conn:
        rows = conn.execute(
            "SELECT session_id FROM sessions WHERE active = 1 AND expires_at > ?", (now,)
        ).fetchall()
    return len([r for r in rows if r["session_id"] != exclude_session_id])


def deactivate_session(session_id: str) -> None:
    with _connect(POLICIES_DB) as conn:
        conn.execute(
            "UPDATE sessions SET active = 0 WHERE session_id = ?", (session_id,)
        )


def deactivate_all_sessions() -> None:
    """Demo/test seam so tools/demo_policies.py can isolate the concurrency
    check from sessions left active by earlier demo steps."""
    with _connect(POLICIES_DB) as conn:
        conn.execute("UPDATE sessions SET active = 0")
