#!/usr/bin/env bash
# Phase 6b (UNTESTED SCAFFOLD -- see README.md). Boots the images build.sh
# produced. Thin wrapper around OP-TEE's own `qemu_v8.mk run-only` target;
# not a from-scratch QEMU invocation, since the reference build system
# already knows the right flags (memory layout, -bios/-kernel paths,
# the two serial consoles for secure vs. normal world).
set -euo pipefail

OPTEE_ROOT="${OPTEE_ROOT:-$HOME/optee}"
cd "$OPTEE_ROOT/build"

echo "Booting qemu_v8. This opens (at least) two consoles/windows: the QEMU"
echo "monitor and the normal-world serial console (secure world's console, if"
echo "shown separately, only prints OP-TEE core boot logs)."
echo
echo "At the '(qemu)' monitor prompt, type 'c' and Enter to continue boot."
echo "Once you reach a normal-world login/shell (buildroot's default is root,"
echo "no password), run:"
echo "  /drm_poc_ca                   # first pass: provisions, writes device_pubkey.bin"
echo "  # (on the host, in a separate terminal:)"
echo "  #   python3 gen_test_vectors.py <path-to-rootfs-overlay-dir>"
echo "  #   -- then rebuild the rootfs stage so the new vectors are in the image, or"
echo "  #      copy them in via a 9p share if one is configured -- see README.md"
echo "  /drm_poc_ca                   # second pass: real unwrap/decrypt/hash-proof"
echo "  /drm_poc_ca --insecure-debug-dump   # contrast: non-SDP buffer, plaintext visible"
echo

make -f qemu_v8.mk run-only
