# Phase 6b (UNTESTED SCAFFOLD -- see README.md). Linux build environment for
# OP-TEE's qemu_v8 reference target, since OP-TEE's build system targets
# Linux hosts, not macOS. Package list follows OP-TEE's documented
# prerequisites (https://optee.readthedocs.io/en/latest/building/gits/build.html
# "Prerequisites"); OP-TEE's own `make toolchains` step fetches the actual
# aarch64 cross-compilers, so this image only needs the native build tools
# and `repo`.
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    android-tools-adb android-tools-fastboot autoconf automake bc bison \
    build-essential ccache codespell cscope curl device-tree-compiler \
    expect flex ftp-upload gdisk git libattr1-dev libcap-dev libfdt-dev \
    libftdi-dev libglib2.0-dev libgmp3-dev libhidapi-dev libmpc-dev \
    libncurses5-dev libpixman-1-dev libssl-dev libtool libz1 make \
    mtools netcat ninja-build python3 python3-crypto python3-cryptography \
    python3-pip python3-pyelftools python3-serial python-is-python3 rsync \
    unzip uuid-dev wget xdg-user-dirs xterm xz-utils zlib1g-dev \
    ca-certificates sudo \
    && rm -rf /var/lib/apt/lists/*

# Google's `repo` tool, used to fetch OP-TEE's multi-repository qemu_v8
# manifest (build.git, optee_os.git, optee_client.git, edk2.git,
# trusted-firmware-a.git, linux.git, buildroot.git, ...).
RUN curl -o /usr/local/bin/repo https://storage.googleapis.com/git-repo-downloads/repo \
    && chmod +x /usr/local/bin/repo

RUN useradd -m -s /bin/bash builder
USER builder
WORKDIR /home/builder

RUN git config --global user.email "builder@drm-poc.local" \
    && git config --global user.name "drm-poc builder"

# build.sh (bind-mounted or copied in at run time) does the actual
# repo init/sync + make. Not run automatically by this image so the very
# long first sync/build can be observed, interrupted, and resumed.
CMD ["/bin/bash"]
