# Phase 2 notes: BCC/Python labs

Environment: same VM as Phase 1 (`joyful-chihuahua`, Ubuntu 24.04, kernel 6.8.0, aarch64).
Run any lab with `sudo python3 -u <script>` — the `-u` matters: BCC's Python stdout is
block-buffered when not attached to a TTY, so `timeout`'s SIGTERM can kill the process before
buffered output ever gets flushed. Learned this the hard way when several early test runs
produced *zero* output despite the program clearly running and generating events.

## Lab 1 — hello-world kprobe ([lab1_hello.py](lab1_hello.py))

```c
int hello(void *ctx) {
    bpf_trace_printk("Hello, eBPF! execve called.\n");
    return 0;
}
```

Attached via `b.attach_kprobe(event=b.get_syscall_fnname("execve"), fn_name="hello")` —
`get_syscall_fnname` resolves the real kernel symbol for a syscall name, which differs by
architecture (`__x64_sys_execve` on x86_64 vs the arm64 equivalent here) and BCC hides that
lookup. `trace_print()` reads from the shared `/sys/kernel/debug/tracing/trace_pipe`, which is
why unrelated kprobes/tracepoints writing to the same pipe would also show up here — it's a
global, shared debug channel, not scoped to this program.

Live: fired on every exec, including the `multipassd` poll-script tree from Phase 1.

## Lab 2 — syscall counter with a BPF hash map ([lab2_syscall_count.py](lab2_syscall_count.py))

```c
BPF_HASH(counts, u32, u64);
int count_syscall(void *ctx) {
    u32 pid = bpf_get_current_pid_tgid() >> 32;
    u64 zero = 0, *val;
    val = counts.lookup_or_try_init(&pid, &zero);
    if (val) { (*val)++; }
    return 0;
}
```

`BPF_HASH` declares a map visible to both kernel and userspace (`b["counts"]` from Python).
`lookup_or_try_init` does an atomic get-or-insert — necessary because two CPUs could hit this
kprobe for different PIDs simultaneously; a plain lookup-then-insert would race. Userspace polls
`counts.items()` every second, prints top 10 by count, then `counts.clear()`.

Live: caught `?`-comm entries — PIDs whose owning process had already exited by the time
userspace tried to read `/proc/{pid}/comm` to resolve a name. Real illustration of a TOCTOU gap
between what the kernel-side map captured (PID at syscall time) and what userspace can still see
a moment later (the process may be long gone). `bpftrace`'s `comm` builtin avoids this because it
reads `current->comm` *inside* the kernel probe itself, not from `/proc` afterward.

## Lab 3 — per-PID file-open filter, in-kernel ([lab3_open_by_pid.py](lab3_open_by_pid.py))

```c
TRACEPOINT_PROBE(syscalls, sys_enter_openat) {
    u32 pid = bpf_get_current_pid_tgid() >> 32;
    if (pid != TARGET_PID) { return 0; }   // filtered in-kernel, not in userspace
    struct data_t data = {};
    bpf_probe_read_user_str(&data.fname, sizeof(data.fname), args->filename);
    events.perf_submit(args, &data, sizeof(data));
    return 0;
}
```

The point of the lab: the `if (pid != TARGET_PID) return 0;` check runs *in the kernel*, before
any data crosses into userspace via the perf ring buffer — the alternative (submit every open,
filter in the Python callback) would burn a ring-buffer slot and a context switch per irrelevant
event system-wide. `TARGET_PID` is baked in via Python string substitution into the C source
before `BPF(text=program)` compiles it, so the filter is a compile-time constant, not a runtime
map lookup.

Debugging note (kept because the failure mode is a real lesson): first two attempts filtered on
a PID captured from a `bash -c '...'` worker script — no events ever matched. The bug: `cat`
inside that script forks a *child* process to do the actual `openat()`, so the syscall fired
under the child's PID, not the parent shell's PID being filtered on. Switching the worker to use
bash's own `exec 3<file` redirection (a builtin, no fork) should have fixed it but still produced
nothing, for reasons not fully isolated (likely a timing/orchestration issue specific to driving
the VM over many short-lived `multipass exec` SSH calls, not the eBPF logic itself). Root-caused
by writing a minimal self-contained repro — `os.fork()` a child that loops `os.open()`, trace it
from the same Python process — which worked immediately and proved the kprobe/filter logic was
correct all along. Confirmed a second time against [lab3_target.py](lab3_target.py), a small
standalone process that loops opening `/tmp/foo.txt`, traced as a genuinely separate external
process: 68 events captured, all `/tmp/foo.txt`, all from the target PID, nothing else leaking
through from the rest of the (busy) system.

**Lesson for future debugging**: when a tracer "sees nothing," don't assume the eBPF logic is
wrong — first confirm events are flowing at all with the filter disabled, then check that the
process actually doing the work has the PID you think it does (forks are invisible from the
outside; a shell script's own PID is not necessarily the PID that calls a given syscall).

## Why BCC compiles at runtime, and why that's a problem

Every `BPF(text=program)` call above triggers on-the-fly compilation: BCC embeds a full Clang/LLVM
toolchain, compiles the C source to eBPF bytecode, and loads it via `bpf()` syscalls — all inside
the running Python process, every single time the script starts. This is *why* `tcplife-bpfcc` in
Phase 1 took a few seconds after launch before it caught its first event: that startup latency was
Clang/LLVM compiling the tool's C source, not the kernel being slow to attach.

Costs this creates for production use:
- **Runtime dependency**: every machine running a BCC tool needs the full LLVM/Clang toolchain and
  kernel headers installed — heavy, and a larger attack surface than shipping a binary.
  `python3-bpfcc` on this VM pulled in `libbpfcc` and friends specifically for this.
- **Startup latency**: unacceptable for a tool that needs to attach instantly (e.g., in response
  to a security event) or that gets invoked frequently (e.g., a CLI run thousands of times/day).
  A few seconds is fine for a `curl` in a lab; it's a real service latency in production.
  Kernel headers also have to match the running kernel — a version mismatch means the BCC
  program simply fails to compile, at runtime, in production, rather than at build time.
- **Compilation surface at runtime**: a real security/robustness concern for anything running as
  root — you're loading and running a compiler in production for tools that themselves need
  elevated privileges.

This is exactly the setup for Phase 3: libbpf + CO-RE compiles once (via `bpftool gen skeleton`)
against `vmlinux.h`/BTF, producing a binary with no LLVM dependency at runtime, and relies on the
kernel's BTF relocation to run correctly across kernel versions without recompiling.
