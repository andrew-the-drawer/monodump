"""Phase 4 (expiry/rental/binding/revocation/concurrency) and Phase 5
(tier gating) policy enforcement for /license.

Every check here either returns normally (license proceeds) or raises
PolicyError with a machine-readable `reason` — license.py turns that into a
clean 4xx. Nothing here silently returns an empty key set; the plan's Phase 4
"Done when" is that each policy is provable by a *failing* playback, so the
rejection has to be visible and specific.
"""
from __future__ import annotations

import os
import time
import uuid

import models

# All three are overridable via env var so the Phase 4 demo scripts don't
# have to wait 48 real hours for a rental window to lapse.
LICENSE_TTL_SECONDS = float(os.environ.get("DRMPOC_LICENSE_TTL", 30))
RENTAL_WINDOW_SECONDS = float(os.environ.get("DRMPOC_RENTAL_WINDOW", 48 * 3600))
MAX_CONCURRENT_SESSIONS = int(os.environ.get("DRMPOC_MAX_CONCURRENT_SESSIONS", 2))

# Phase 5: which content tiers a security level is allowed to receive keys
# for. UHD (our "4K") is withheld from SW exactly like Widevine L1-vs-L3
# gates real 4K behind a TEE (PLAN.md Part 4).
ALLOWED_TIERS = {
    "SW": {"SD", "HD", "FHD", "AUDIO"},
    "TEE": {"SD", "HD", "FHD", "UHD", "AUDIO"},
}


class PolicyError(Exception):
    def __init__(self, reason: str):
        self.reason = reason
        super().__init__(reason)


def select_allowed_keys(security_level: str, requested_kids: list[str], content_id: str):
    allowed_tiers = ALLOWED_TIERS.get(security_level, set())
    requested = {k.lower() for k in requested_kids}
    rows = models.get_content_keys(content_id)
    return [r for r in rows if r["kid"] in requested and r["tier"] in allowed_tiers]


def evaluate_session(device_row, content_id: str, requested_session_id: str | None) -> tuple[str, float, bool]:
    """Returns (session_id, expires_at, is_renewal). Raises PolicyError."""
    if device_row["revoked"]:
        raise PolicyError("device_revoked")

    now = time.time()

    if requested_session_id:
        session = models.get_session(requested_session_id)
        if session is None or not session["active"]:
            raise PolicyError("session_not_found")
        if session["device_id"] != device_row["device_id"]:
            # A license minted for device A, replayed by device B against A's
            # session id. Rejected here; also structurally impossible to
            # decrypt anyway since the response is ECDH-bound (see
            # docs/01-protocol.md), but reject explicitly for a clear error.
            raise PolicyError("device_binding_mismatch")
        if session["first_play_at"] and (now - session["first_play_at"]) > RENTAL_WINDOW_SECONDS:
            raise PolicyError("rental_window_expired")
        new_expiry = now + LICENSE_TTL_SECONDS
        models.renew_session(requested_session_id, new_expiry)
        return requested_session_id, new_expiry, True

    # New session: enforce the concurrent-stream cap before creating it.
    if models.count_active_sessions() >= MAX_CONCURRENT_SESSIONS:
        raise PolicyError("concurrent_stream_limit")

    session_id = uuid.uuid4().hex
    expires_at = now + LICENSE_TTL_SECONDS
    models.create_session(session_id, device_row["device_id"], content_id, LICENSE_TTL_SECONDS)
    models.mark_first_play(session_id)  # PoC simplification: license acquisition == first play
    return session_id, expires_at, False
