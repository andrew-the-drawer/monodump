#!/usr/bin/env bash
# Phase 6b (UNTESTED SCAFFOLD -- see README.md). Builds TF-A + OP-TEE +
# Linux + Buildroot for the qemu_v8 reference target, with
# CFG_SECURE_DATA_PATH enabled, then builds this project's out-of-tree TA
# and CA against the result.
#
# Run inside the Docker image this directory's Dockerfile builds (OP-TEE's
# build system targets Linux hosts):
#   docker build -t drm-poc-optee cdm/tee/optee
#   docker run -it -v drm-poc-optee-src:/home/builder/optee -w /home/builder/optee \
#       -v "$(pwd)/cdm/tee/optee:/home/builder/drm-poc-optee:ro" \
#       drm-poc-optee /home/builder/drm-poc-optee/build.sh
#
# Expect this to take multiple hours on first run (full repo sync of ~10
# git trees, then a from-scratch cross-compiled Linux distribution) and
# ~15-20GB of disk. Not attempted in this session, per the plan's decision
# to scaffold rather than build 6b now -- see README.md's Status line.
set -euo pipefail

OPTEE_ROOT="${OPTEE_ROOT:-$HOME/optee}"
DRM_POC_OPTEE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

mkdir -p "$OPTEE_ROOT"
cd "$OPTEE_ROOT"

if [[ ! -d .repo ]]; then
  echo "== repo init: OP-TEE's qemu_v8 manifest =="
  repo init -u https://github.com/OP-TEE/manifest.git -m qemu_v8.xml
fi

echo "== repo sync (long the first time) =="
repo sync -j"$(nproc)"

cd build

echo "== fetching cross-toolchains =="
make -f qemu_v8.mk toolchains -j"$(nproc)"

# The two config options this whole track exists for:
#   CFG_SECURE_DATA_PATH=y  -- carves out the SDP region + DMA-BUF heap
#                              driver our CA/TA need.
#   CFG_WITH_PAGER=n        -- CFG_WITH_PAGER=y together with
#                              CFG_SECURE_DATA_PATH=y hangs OP-TEE core
#                              init on qemu_v8 (optee_os#1656, cited in
#                              PLAN.md). Do not turn the pager on here.
echo "== building TF-A + OP-TEE + Linux + Buildroot (CFG_SECURE_DATA_PATH=y, CFG_WITH_PAGER=n) =="
make -f qemu_v8.mk CFG_SECURE_DATA_PATH=y CFG_WITH_PAGER=n all -j"$(nproc)"

# --- out-of-tree TA + CA ---
# TA_DEV_KIT_DIR and the CA's TEEC_EXPORT/CROSS_COMPILE come from this
# build tree's layout, which has shifted across OP-TEE releases -- verify
# these paths against $OPTEE_ROOT/build/qemu_v8.mk's own TA_DEV_KIT_DIR and
# related variables for whatever manifest revision `repo sync` actually
# pulled, rather than trusting this script blindly.
export TA_DEV_KIT_DIR="$OPTEE_ROOT/optee_os/out/arm/export-ta_arm64"
export TEEC_EXPORT="$OPTEE_ROOT/optee_client/out/export/usr"
export CROSS_COMPILE="$OPTEE_ROOT/toolchains/aarch64/bin/aarch64-linux-gnu-"
export CROSS_COMPILE_TA="$OPTEE_ROOT/toolchains/aarch64/bin/aarch64-linux-gnu-"

echo "== building drm_poc TA =="
make -C "$DRM_POC_OPTEE_DIR/ta" CROSS_COMPILE="$CROSS_COMPILE_TA" \
     TA_DEV_KIT_DIR="$TA_DEV_KIT_DIR"

echo "== building drm_poc CA =="
make -C "$DRM_POC_OPTEE_DIR/host" CROSS_COMPILE="$CROSS_COMPILE" \
     TEEC_EXPORT="$TEEC_EXPORT"

echo
echo "Built. TA: $DRM_POC_OPTEE_DIR/ta/<uuid>.ta"
echo "       CA: $DRM_POC_OPTEE_DIR/host/drm_poc_ca"
echo "Copy both into the QEMU rootfs (see run.sh) before booting."
