#!/usr/bin/env python3
"""Phase 4 done-when: each policy demonstrated by a FAILING license request,
not a log line. Run against a live server (see README for how to start it).

Uses /admin/policy to shrink the license TTL and rental window to a few
seconds so this runs in well under a minute instead of requiring a real
48-hour wait — see the comment on that route in server/main.py; it's a
demo/test seam, not part of the device-facing protocol.
"""
import sys
import time

import requests

sys.path.insert(0, "tools")
sys.path.insert(0, "server")
from protocol_client import Device, BASE_URL  # noqa: E402
import models  # noqa: E402

PASS = "PASS"
FAIL = "FAIL"


def check(label: str, condition: bool, detail: str = ""):
    status = PASS if condition else FAIL
    print(f"[{status}] {label}" + (f" — {detail}" if detail else ""))
    if not condition:
        raise SystemExit(1)


def main():
    models.init_db()
    all_kids = [r["kid"] for r in models.get_content_keys("demo")]
    if not all_kids:
        print("no content keys seeded — run packaging/package.sh then server/seed_content.py")
        raise SystemExit(1)

    print("=== configuring fast policy windows for this demo ===")
    r = requests.post(
        f"{BASE_URL}/admin/policy",
        json={"license_ttl_seconds": 3, "rental_window_seconds": 4, "max_concurrent_sessions": 2},
    )
    print(r.json())

    # --- 1. Expiry + renewal round-trip ------------------------------------
    print("\n=== policy 1: license expiry + renewal ===")
    d1 = Device()
    d1.provision(requested_level="SW")
    resp = d1.request_license("demo", all_kids)
    check("initial license grant succeeds", resp.status_code == 200)
    session_id = resp._decrypted["session_id"]
    first_expiry = resp._decrypted["policy"]["expires_at"]

    renew = d1.request_license("demo", all_kids, session_id=session_id)
    check(
        "renewal before expiry succeeds and extends expiry",
        renew.status_code == 200
        and renew._decrypted["policy"]["is_renewal"] is True
        and renew._decrypted["policy"]["expires_at"] > first_expiry,
    )

    # --- 2. Rental window ----------------------------------------------------
    print("\n=== policy 2: rental window ===")
    print("sleeping past the 4s rental window (first_play_at was set at session creation)...")
    time.sleep(5)
    late_renew = d1.request_license("demo", all_kids, session_id=session_id)
    check(
        "renewal after rental window is rejected",
        late_renew.status_code == 403 and late_renew.json()["detail"] == "rental_window_expired",
        f"got {late_renew.status_code} {late_renew.json()}",
    )

    # --- 3. Device binding -----------------------------------------------------
    print("\n=== policy 3: device binding ===")
    d2 = Device()
    d2.provision(requested_level="SW")
    d3 = Device()
    d3.provision(requested_level="SW")
    fresh = d2.request_license("demo", all_kids)
    check("device B gets its own session", fresh.status_code == 200)
    d2_session = fresh._decrypted["session_id"]

    hijack = d3.request_license("demo", all_kids, session_id=d2_session)
    check(
        "device C replaying device B's session_id is rejected",
        hijack.status_code == 403 and hijack.json()["detail"] == "device_binding_mismatch",
        f"got {hijack.status_code} {hijack.json()}",
    )

    # --- 4. Revocation -----------------------------------------------------
    print("\n=== policy 4: revocation ===")
    d4 = Device()
    prov = d4.provision(requested_level="SW")
    ok = d4.request_license("demo", all_kids)
    check("device D gets a license before revocation", ok.status_code == 200)

    rv = requests.post(f"{BASE_URL}/admin/devices/{prov['device_id']}/revoke")
    check("revoke admin call succeeds", rv.status_code == 200)

    after_revoke = d4.request_license("demo", all_kids)
    check(
        "revoked device is rejected on its next license request",
        after_revoke.status_code == 403 and after_revoke.json()["detail"] == "device_revoked",
        f"got {after_revoke.status_code} {after_revoke.json()}",
    )

    # --- 5. Concurrent stream limit -----------------------------------------
    print("\n=== policy 5: concurrent stream limit ===")
    requests.post(f"{BASE_URL}/admin/sessions/reset")  # isolate from sessions created above
    requests.post(f"{BASE_URL}/admin/policy", json={"max_concurrent_sessions": 1, "license_ttl_seconds": 60})
    d5 = Device()
    d5.provision(requested_level="SW")
    d6 = Device()
    d6.provision(requested_level="SW")

    first_stream = d5.request_license("demo", all_kids)
    check("first concurrent session (of cap=1) succeeds", first_stream.status_code == 200)

    second_stream = d6.request_license("demo", all_kids)
    check(
        "second concurrent NEW session is rejected while the first is still active",
        second_stream.status_code == 403 and second_stream.json()["detail"] == "concurrent_stream_limit",
        f"got {second_stream.status_code} {second_stream.json()}",
    )

    print("\nall Phase 4 policies demonstrated by failing playback (clean rejections), not log lines.")


if __name__ == "__main__":
    main()
