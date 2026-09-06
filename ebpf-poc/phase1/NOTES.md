# Phase 1 notes: reading the existing tools

Environment: multipass VM `joyful-chihuahua`, Ubuntu 24.04.4 LTS, kernel 6.8.0-138-generic,
BTF present (`/sys/kernel/btf/vmlinux`), bpftrace 0.20.2, bpfcc-tools 0.29.1.

Each tool below: what it does, its bpftrace source (`/usr/sbin/<name>.bt`), and what live output on
the VM actually showed. One-liners for the lab are in [oneliners.bt](oneliners.bt).

## execsnoop — trace new processes via exec()

```c
tracepoint:syscalls:sys_enter_exec*
{
	$task = (struct task_struct *)curtask;
	printf("%15s %-7d %-7d ", strftime("%H:%M:%S.%f", nsecs), pid, $task->real_parent->pid);
	join(args.argv);
}
```

One probe, no map: every `execve`/`execveat` tracepoint firing prints immediately (PID, parent PID via
`curtask->real_parent`, and argv joined into one line). Cheapest possible tool shape — pure event log.

Live: caught the host's `multipassd` health-poll script forking `bash -c "..."` every second, which in
turn execs a whole tree of `cat`/`cut`/`free`/`grep`/`awk`/`df`/`tail`/`nproc`/`head`/`uptime`/`ip` to
gather loadavg/mem/disk stats — none of it anything we ran deliberately. execsnoop sees literally every
exec on the system, unprompted.

## opensnoop — trace open()/openat()

```c
tracepoint:syscalls:sys_enter_open,
tracepoint:syscalls:sys_enter_openat
{
	@filename[tid] = args.filename;
}

tracepoint:syscalls:sys_exit_open,
tracepoint:syscalls:sys_exit_openat
/@filename[tid]/
{
	$ret = args.ret;
	$fd = $ret >= 0 ? $ret : -1;
	$errno = $ret >= 0 ? 0 : - $ret;
	printf("%-6d %-16s %4d %3d %s\n", pid, comm, $fd, $errno, str(@filename[tid]));
	delete(@filename[tid]);
}
```

The **entry/exit correlation pattern**: the filename argument is only visible at syscall entry, the
return value (fd or -errno) only at exit. `@filename[tid]` is a BPF hash map keyed by thread ID that
survives between the two probe firings; the exit probe's predicate (`/@filename[tid]/`) skips threads
with nothing stashed, and `delete()` cleans up once the pair is consumed.

Live: ran while `cat /etc/hostname` and a write+read of `/tmp/foo.txt` executed. Output was dominated by
`sshd` opening ~20 shared libraries and config files just to service the SSH session used to run the
command — proof it traces every process, not a targeted one. Also caught a real failure:
`5974 sshd -1 2 /proc/sys/crypto/fips_enabled` — fd -1, errno 2 (ENOENT), captured cleanly because the
map correlates the failing exit back to its entry.

## tcplife — TCP session lifespans

```c
kprobe:tcp_set_state
{
	$sk = (struct sock *)arg0;
	$newstate = arg1;
	// records timestamp + byte counters keyed by socket on connect,
	// prints one summary line when state transitions to CLOSE
}
```

Uses a **kprobe** (`tcp_set_state`), not a tracepoint — there's no stable tracepoint exposing internal
`struct sock` state transitions, so it hooks the kernel function directly. This is more powerful (raw
struct access) but more fragile (tied to that function's existence/signature across kernel versions) —
the same trade-off named in the plan's Phase 2→3 transition.

Live: took a few seconds after launch before it caught anything — that startup latency is BCC compiling
the C source to eBPF bytecode via LLVM *at attach time*. Once attached, three `curl` calls to
example.com/ebpf.io showed up as real TCP sessions (~94-116ms each, via Cloudflare IPs), alongside the
long-lived SSH connection carrying the exec session itself:

```
PID   COMM       LADDR           LPORT RADDR           RPORT TX_KB RX_KB MS
9842  curl       192.168.2.2     46382 104.20.23.154   443       0     5 94.11
9891  curl       192.168.2.2     49424 172.66.147.243  443       0     5 115.96
9940  curl       192.168.2.2     52488 104.20.23.154   443       0     5 104.38
```

## biolatency — block I/O latency histogram

```c
tracepoint:block:block_bio_queue
{
	@start[args.sector] = nsecs;
}

tracepoint:block:block_rq_complete,
tracepoint:block:block_bio_complete
/@start[args.sector]/
{
	@usecs = hist((nsecs - @start[args.sector]) / 1000);
	delete(@start[args.sector]);
}
```

Same entry/exit correlation pattern as opensnoop (keyed by sector instead of tid), but instead of
printing per-event it feeds a **histogram map** (`hist()`), which bpftrace auto-prints on exit for any
`@`-map still holding data — that's why `END` clears `@start` (the correlation map) but leaves `@usecs`
alone.

Live: ran during a 200MB `dd ... oflag=direct` write; the histogram came back empty. Likely explanation:
the VM's virtio-blk backing (writes measured at ~1.7GB/s) doesn't route through the
`block_bio_queue`/`block_rq_complete` tracepoints the way a real disk controller would — a good reminder
that tool source and live behavior can diverge under virtualization, and that's worth checking rather
than assuming.

## Concepts checkpoint

- **Probe** — a kernel attach point. Tracepoints (`sys_enter_execve`) are stable, versioned kernel APIs
  built for tracing. kprobes (`vfs_open`, `tcp_set_state`) hook any kernel function by name — more
  access, less stability across kernel versions.
- **Map** — kernel-resident key/value storage that outlives one probe firing. Used here to correlate
  entry↔exit across two separate probe invocations (opensnoop, biolatency, and the latency one-liner),
  and to aggregate into histograms or per-key counts. Cost: entries for calls still in-flight when the
  program exits never get matched/deleted — observed directly as a stray `@start[12560]` leftover from
  our own read()-latency one-liner (a blocked `read()`, presumably sshd waiting on terminal input).
- **Verifier** — the kernel's static analyzer that rejects a program at load time unless it can prove
  bounded loops and safe memory access. Not triggered today; worth deliberately breaking in Phase 2 to
  see the rejection message once.
