"""Phase 2+ FastAPI app: static player/content hosting, plus the ClearKey
license endpoint that closes the EME loop with zero security (Phase 2).

Phase 3 adds /provision and /license (our own protocol) alongside this;
/clearkey-license stays only as the thing that ACTUALLY decrypts (via the
browser's built-in ClearKey CDM) once our protocol has picked which keys a
given device is allowed to have.
"""
from __future__ import annotations

import base64
import json
import sys
from pathlib import Path

from fastapi import FastAPI, HTTPException, Request, Response
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel

sys.path.insert(0, str(Path(__file__).resolve().parent))
import license as license_proto  # noqa: E402  (shadows stdlib `license`, not used elsewhere)
import models  # noqa: E402
import policy  # noqa: E402

SERVER_DIR = Path(__file__).resolve().parent
DRM_POC_DIR = SERVER_DIR.parent
CONTENT_DIR = DRM_POC_DIR / "packaging" / "content" / "packaged"
PLAYER_DIR = DRM_POC_DIR / "player"
CONTENT_ID = "demo"

app = FastAPI(title="drm-poc license server")


@app.on_event("startup")
def _startup() -> None:
    models.init_db()


def _b64url_decode(s: str) -> bytes:
    padded = s + "=" * (-len(s) % 4)
    return base64.urlsafe_b64decode(padded)


def _b64url_encode(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode("ascii")


@app.post("/clearkey-license")
async def clearkey_license(request: Request):
    """Phase 2: trivial, insecure ClearKey license endpoint.

    Implements the W3C ClearKey license format directly: the browser's
    built-in ClearKey CDM sends {"kids": [base64url KID, ...]} and expects
    back a JWK Set with the raw keys. There is no authentication, no policy,
    no encryption of the response — that's the point. Delete this route (or
    stop the server) and playback stops dead, proving the player has no
    fallback key source.
    """
    body = await request.body()
    try:
        payload = json.loads(body)
        requested_kids = payload["kids"]
    except (json.JSONDecodeError, KeyError, TypeError):
        raise HTTPException(status_code=400, detail="malformed ClearKey request")

    jwks = []
    for b64_kid in requested_kids:
        kid_hex = _b64url_decode(b64_kid).hex()
        row = models.get_content_key(CONTENT_ID, kid_hex)
        if row is None:
            continue
        jwks.append(
            {
                "kty": "oct",
                "kid": b64_kid,
                "k": _b64url_encode(bytes.fromhex(row["key"])),
            }
        )

    if not jwks:
        raise HTTPException(status_code=404, detail="no keys available for requested KIDs")

    return Response(
        content=json.dumps({"keys": jwks, "type": "temporary"}),
        media_type="application/json",
    )


# --- Phase 3: our own provisioning + license protocol ------------------------

class ProvisionRequest(BaseModel):
    identity_pubkey_jwk: dict
    requested_security_level: str
    attestation: str | None = None


class LicenseRequest(BaseModel):
    master_token: str
    content_id: str
    kids: list[str]
    nonce: str
    ephemeral_pubkey_jwk: dict
    signature: str
    session_id: str | None = None


@app.post("/provision")
async def provision(req: ProvisionRequest):
    try:
        return license_proto.handle_provision(
            req.identity_pubkey_jwk, req.requested_security_level, req.attestation
        )
    except license_proto.ProtocolError as e:
        raise HTTPException(status_code=e.status_code, detail=e.reason)


@app.post("/license")
async def license_route(req: LicenseRequest):
    try:
        return license_proto.handle_license(
            req.master_token,
            req.content_id,
            req.kids,
            req.nonce,
            req.ephemeral_pubkey_jwk,
            req.signature,
            req.session_id,
        )
    except license_proto.ProtocolError as e:
        raise HTTPException(status_code=e.status_code, detail=e.reason)


# --- admin routes, for the Phase 4 policy demos (revocation) -----------------

@app.post("/admin/devices/{device_id}/revoke")
async def revoke_device(device_id: str):
    if models.get_device(device_id) is None:
        raise HTTPException(status_code=404, detail="unknown_device")
    models.set_device_revoked(device_id, True)
    return {"device_id": device_id, "revoked": True}


@app.post("/admin/devices/{device_id}/unrevoke")
async def unrevoke_device(device_id: str):
    if models.get_device(device_id) is None:
        raise HTTPException(status_code=404, detail="unknown_device")
    models.set_device_revoked(device_id, False)
    return {"device_id": device_id, "revoked": False}


@app.get("/admin/devices")
async def list_devices():
    rows = models.list_devices()
    return [
        {
            "device_id": r["device_id"],
            "security_level": r["security_level"],
            "revoked": bool(r["revoked"]),
            "created_at": r["created_at"],
        }
        for r in rows
    ]


# Phase 4 demo/test seam only — lets tools/demo_policies.py exercise expiry,
# rental-window and concurrency rules on human timescales (seconds) without
# restarting the server. Not part of the device-facing protocol.

class PolicyOverrides(BaseModel):
    license_ttl_seconds: float | None = None
    rental_window_seconds: float | None = None
    max_concurrent_sessions: int | None = None


@app.get("/admin/policy")
async def get_policy():
    return {
        "license_ttl_seconds": policy.LICENSE_TTL_SECONDS,
        "rental_window_seconds": policy.RENTAL_WINDOW_SECONDS,
        "max_concurrent_sessions": policy.MAX_CONCURRENT_SESSIONS,
    }


@app.post("/admin/sessions/reset")
async def reset_sessions():
    """Demo/test seam: deactivate all sessions so tools/demo_policies.py can
    demonstrate the concurrency cap in isolation from earlier demo steps."""
    models.deactivate_all_sessions()
    return {"reset": True}


@app.post("/admin/policy")
async def set_policy(req: PolicyOverrides):
    if req.license_ttl_seconds is not None:
        policy.LICENSE_TTL_SECONDS = req.license_ttl_seconds
    if req.rental_window_seconds is not None:
        policy.RENTAL_WINDOW_SECONDS = req.rental_window_seconds
    if req.max_concurrent_sessions is not None:
        policy.MAX_CONCURRENT_SESSIONS = req.max_concurrent_sessions
    return await get_policy()


# --- static hosting -----------------------------------------------------------
# One origin (http://localhost:8000) serves the player page, the packaged
# DASH content, and the API, so no CORS configuration is needed and EME's
# secure-context requirement is satisfied via `localhost`.

app.mount("/content", StaticFiles(directory=str(CONTENT_DIR)), name="content")
app.mount("/player", StaticFiles(directory=str(PLAYER_DIR), html=True), name="player")
