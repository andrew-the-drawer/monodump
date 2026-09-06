# Phase 3 lab: standalone libbpf + CO-RE build, no BCC/LLVM-at-runtime.
#
# Layout mirrors libbpf/libbpf-bootstrap's examples/c, but against the
# system libbpf-dev package instead of a vendored submodule, and generates
# vmlinux.h from the *running* kernel's own BTF (bpftool btf dump), which is
# the actual CO-RE workflow: build once against this kernel's BTF layout,
# then rely on libbpf's BTF relocation at load time to adapt to whatever
# kernel the binary actually runs on.
CLANG ?= clang
BPFTOOL ?= bpftool
ARCH := $(shell uname -m | sed 's/x86_64/x86/;s/aarch64/arm64/;s/ppc64le/powerpc/;s/mips.*/mips/')

CFLAGS := -g -O2 -Wall
BPF_CFLAGS := -g -O2 -target bpf -D__TARGET_ARCH_$(ARCH) -I.

LIBS := $(shell pkg-config --libs libbpf) -lelf -lz

.PHONY: all clean run

all: syscount

vmlinux.h:
	$(BPFTOOL) btf dump file /sys/kernel/btf/vmlinux format c > $@

syscount.bpf.o: syscount.bpf.c vmlinux.h
	$(CLANG) $(BPF_CFLAGS) -c $< -o $@

syscount.skel.h: syscount.bpf.o
	$(BPFTOOL) gen skeleton $< > $@

syscount.o: syscount.c syscount.skel.h
	$(CLANG) $(CFLAGS) $(shell pkg-config --cflags libbpf) -c $< -o $@

syscount: syscount.o
	$(CLANG) $(CFLAGS) $^ $(LIBS) -o $@

run: syscount
	sudo ./syscount

clean:
	rm -f *.o *.skel.h vmlinux.h syscount
