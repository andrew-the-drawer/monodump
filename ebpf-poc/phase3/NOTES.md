# Phase 3 notes: libbpf + CO-RE

Environment: same VM as Phases 1-2 (`joyful-chihuahua`, Multipass, Ubuntu 24.04, kernel
6.8.0-generic, aarch64). BTF is built into this kernel already
(`/sys/kernel/btf/vmlinux` exists, ~6.9MB) — no `CONFIG_DEBUG_INFO_BTF` fiddling needed.

Toolchain added on top of Phase 1/2's BCC setup: `clang`, `llvm`, `libelf-dev`,
`libbpf-dev`, `pkg-config`, `linux-tools-$(uname -r)` (for a `bpftool` that matches the
running kernel). `libbpf-dev` on Ubuntu 24.04 ships a real static+shared libbpf
(`libbpf.a`/`.so`, `v1.4`) plus all the `bpf/*.h` headers — no need to vendor libbpf as a
submodule the way `libbpf-bootstrap` itself does for portability across distros.

Setup snag, kept because it wasted real time: the VM's clock had drifted ~8.5 hours
behind real time (multipass/QEMU RTC drift after the host slept), which made every
`apt-get update` fail with "Release file ... is not valid yet" — apt refusing repo
metadata that appears to be signed in the future from the VM's point of view.
`timedatectl set-ntp true` alone didn't fix it (`systemd-timesyncd` reported
"synchronized: yes" while still showing the stale time); the fix was
`sudo systemctl restart systemd-timesyncd`, which forced an immediate re-sync instead of
waiting for its poll interval.

## Working through libbpf-bootstrap

Cloned `libbpf/libbpf-bootstrap` with `--recurse-submodules` (pulls in `libbpf`,
`bpftool`, `vmlinux.h`, `blazesym` as pinned submodules — this is the "vendor everything"
approach production CO-RE projects use so a build isn't at the mercy of whatever
`libbpf-dev` version happens to be installed). Built and ran, in the prescribed order,
from `examples/c`:

- **`minimal`** — a single tracepoint (`tp/syscalls/sys_enter_write`) filtered by PID,
  `bpf_printk`'d to `trace_pipe`. Confirmed via `sudo cat /sys/kernel/debug/tracing/trace_pipe`:
  fires only for the `minimal` process's own PID, nothing else — the in-kernel filter from
  Phase 2's Lab 3 lesson, now compiled ahead-of-time instead of interpreted by BCC at
  startup.
- **`bootstrap`** — full process exec/exit tracking (`sys_enter_execve` +
  `sched_process_exit`), pushed to userspace over a BPF ring buffer instead of a polled
  hash map. Ran it and watched real shell activity stream through: forked `bash`, `cat`,
  `cut`, `awk`, `grep` children, each EXEC followed by its matching EXIT and wall-clock
  duration. This is the shape a real exec-monitoring tool takes — push events out as they
  happen rather than polling and losing short-lived processes (the exact `?`-comm gap Lab 2
  hit in Phase 2).
- **`uprobe`** — self-contained: it uprobes its own `uprobed_add`/`uprobed_sub` functions
  in `/proc/self/exe` and calls them in a loop, so no external trigger was needed. Notable
  in the debug log: CO-RE relocating `struct user_pt_regs` (the arm64 register-access
  struct) against the *kernel's* BTF, i.e. even reading userspace-probe function arguments
  goes through the CO-RE relocation machinery on this architecture.
- **`tc`** — attaches an ingress classifier to `lo` and prints IP packet `tot_len`/`ttl`
  for every packet. `sudo tc filter show dev lo ingress` confirmed the classifier attached
  (`tc_ingress:[178] ... jited`); `ping -c 3 127.0.0.1` while watching `trace_pipe` produced
  matching `Got IP packet: tot_len: 84, ttl: 64` lines. Left a stray `clsact` qdisc on `lo`
  after killing the process early (`tc` doesn't remove the qdisc on exit unless it created
  it and reaches its own cleanup path) — removed manually with
  `sudo tc qdisc del dev lo clsact`. Lesson: TC hooks (unlike kprobes/tracepoints) attach a
  persistent kernel object independent of the loading process's lifetime; killing the
  loader isn't enough to detach.

All four are CO-RE binaries: no Clang/LLVM invoked at load time, verified in the
`libbpf: loaded kernel BTF from '/sys/kernel/btf/vmlinux'` + `CO-RE relocating [...]`
lines in every run's debug log — the struct-layout patching Phase 2's NOTES predicted
would replace BCC's runtime compilation.

## Lab: rewriting Phase 2's syscall counter as CO-RE (`syscount/`)

Rewrote [`phase2/lab2_syscall_count.py`](../phase2/lab2_syscall_count.py) (BCC, hash map,
`bpf_get_current_pid_tgid()`, `lookup_or_try_init`) as a standalone libbpf CO-RE program:
[`syscount.bpf.c`](syscount/syscount.bpf.c) + [`syscount.c`](syscount/syscount.c) +
[`Makefile`](syscount/Makefile).

Build pipeline in the Makefile (the concrete answer to "what does `bpftool gen skeleton`
actually do"):

```
bpftool btf dump file /sys/kernel/btf/vmlinux format c > vmlinux.h   # this kernel's types, as C
clang -target bpf -D__TARGET_ARCH_arm64 -c syscount.bpf.c -o syscount.bpf.o
bpftool gen skeleton syscount.bpf.o > syscount.skel.h                # embeds the .o, generates open/load/attach/destroy
clang -c syscount.c -o syscount.o                                     # userspace, against the skeleton
clang syscount.o -lbpf -lelf -lz -o syscount                          # static link, no LLVM/Clang needed at runtime
```

`vmlinux.h` generated at 183k lines (every type in this kernel's BTF); `syscount.skel.h`
at ~600 lines is the interesting one — a `struct syscount_bpf` wrapping the embedded
`.bpf.o` bytes plus generated `syscount_bpf__open/load/attach/destroy()` functions, so
`syscount.c` never touches raw `bpf()` syscalls for object lifecycle, only for map I/O
(`bpf_map_get_next_key`/`lookup_elem`/`delete_elem` from `<bpf/bpf.h>`, the fd-based API —
distinct from `<bpf/libbpf.h>`'s object-based `bpf_map__*` wrappers, a distinction the
compiler enforces the hard way: `bpf_map_lookup_elem` and `bpf_map__lookup_elem` are two
different functions, and only the header split makes that obvious).

Two intentional improvements over the original BCC version, made possible by moving logic
into the kernel-side program instead of leaving it to userspace polling:

1. **`?`-comm fixed.** Phase 2's NOTES documented a TOCTOU gap: BCC read
   `/proc/{pid}/comm` from userspace *after* the syscall, so short-lived processes showed
   up as `?`. Here `bpf_get_current_comm()` runs inside the kprobe/tracepoint handler at
   the moment of the syscall and stores `comm` directly in the map value — confirmed live:
   `cat /etc/hostname` invocations that exited before the 1s poll interval still showed up
   as `cat`, never `?`.
2. **Increment race fixed.** The BCC version's `(*val)++` is a plain non-atomic
   read-modify-write on a value multiple CPUs can reach concurrently (two threads of the
   same process — same PID after the `>>32` truncation — calling `read()` on different
   cores at once). Swapped for `__sync_fetch_and_add(&val->count, 1)`, an atomic add. The
   *first* touch per PID still has the same benign race BCC's `lookup_or_try_init` has
   (two CPUs both miss and both try to insert; `BPF_NOEXIST` makes the loser's count-of-1
   silently vanish instead of corrupting state) — noted as a comment in the source rather
   than "fixed," since fixing it needs a spinlock or per-CPU map and isn't worth it for a
   top-N counter.

Verified live against `cat /etc/hostname` run several times over: output correctly
attributed counts to `bash`, `sshd` (from driving it over `multipass exec`/SSH), `cat`,
`awk`, `grep`, `free`, `uptime`, `df`, all resolved to a real `comm` string, none dropped
to `?`. `Ctrl-C`/`SIGTERM` handling (`sig_handler` + `exiting` flag) exits the poll loop
and calls `syscount_bpf__destroy()`, detaching the tracepoint cleanly — confirmed no
leftover `syscount` process or attached program survives the run.

## Checkpoint: why CO-RE runs unmodified across kernel versions

A normal BPF program compiled against one kernel's headers hardcodes struct field
*offsets* — e.g. "PID is 12 bytes into `struct task_struct`." If a different kernel
reorders or adds fields, that offset is wrong and the program reads garbage (or the
verifier rejects nonsense, in the better case).

CO-RE fixes this by never hardcoding the offset. Clang emits special relocation records
(visible as `.BTF.ext` in the object) for every "field X of type Y" access instead of a
raw offset. At load time, libbpf reads BTF describing the *actual running kernel's* type
layout (`/sys/kernel/btf/vmlinux`) and patches each relocation to the real offset on that
machine — the `CO-RE relocating [...] found target candidate [...] patched insn` lines
seen in every debug log above. The compiled `.o` byte-for-byte is portable; only the
patching step, done once at load, adapts it. That's why `bpftool gen skeleton` + static
linking against `libbpf` produces a single binary with no LLVM/Clang dependency, unlike
BCC's compile-on-every-launch model from Phase 2 — the "compile once against BTF-described
types, relocate at load" split is the entire trick.

**`vmlinux.h` is compile-time-only and needn't match the target kernel.** It exists so
`clang` has type declarations to compile against — `task->pid` needs `struct task_struct`
to exist as a *name* at compile time, nothing more. The offsets it implies never survive
compilation: they're immediately turned into by-name relocation records, then thrown away
and re-derived from the target's own BTF at load time. So the kernel this header was
generated from (here, the build VM's own running kernel, since that's the path of least
resistance) doesn't need to be the kernel the binary actually loads on — that decoupling
*is* CO-RE's entire value proposition. The only thing that has to hold is "the fields my
program touches still exist, by name, on whatever kernel loads it." Concretely: no need to
regenerate `vmlinux.h` when moving this binary to a different kernel version or machine;
only regenerate it if writing *new* code that references a field the current header
doesn't know about yet. This is also why `libbpf-bootstrap` ships a pre-generated
`vmlinux.h` as a pinned submodule instead of running `bpftool btf dump` at every build —
it decouples "what the compiler needs to see" from whatever kernel the CI box happens to
be running.

**A relocation that can't be resolved fails the load, loudly, not silently.** If the
target kernel genuinely lacks a type/field a program references, that specific `SEC()`
program fails `bpf_object__load()` (surfaced through the skeleton's `__load()` returning
an error) before it ever runs — not a runtime crash or garbage read, a clean load-time
rejection. `syscount.c` never had to write error-recovery for this because with one
program in the object, "the program's relocation failed" and "the whole loader failed"
are the same event here; in an object with several independent programs, only the ones
touching the missing type fail, siblings that don't reference it still load. The
deliberate escape hatch for code that needs to *tolerate* a missing field rather than
fail outright is `bpf_core_field_exists()` / `bpf_core_type_exists()` /
`bpf_core_enum_value_exists()` — relocations explicitly marked "absence is not an error,"
which resolve to `0`/`false` at load time instead of failing, letting a program branch on
kernel version/feature support in-line:

```c
if (bpf_core_field_exists(struct task_struct, some_new_field)) {
	/* newer kernels */
} else {
	/* fallback */
}
```

`syscount.bpf.c` doesn't use this — every field it touches (`bpf_get_current_pid_tgid()`,
`bpf_get_current_comm()`) is a stable helper, not a raw struct-field CO-RE access, so
there's nothing version-dependent to guard.
