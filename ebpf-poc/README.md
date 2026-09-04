# eBPF Learning Plan

Hands-on plan for learning eBPF, from first principles to a capstone project.
Scaffolding (VM setup, libbpf-bootstrap skeleton, labs) to be added in a follow-up session.

## 0. Dev environment

eBPF needs a Linux kernel (5.x+, ideally 6.x for full CO-RE/BTF support) — macOS needs a VM.

- **Multipass or UTM** → Ubuntu 22.04/24.04 VM locally (recommended — free, full control, persists)
- **Lima** (`limactl start`) — lighter weight, good Docker-Desktop-alternative feel
- A cheap cloud VM (Hetzner/DigitalOcean Ubuntu box) if you want to poke at real network traffic later

Avoid Docker-for-Mac alone — its LinuxKit kernel is often stripped down and BTF/kprobes support is inconsistent.

## Phase 1 (Days 1-3): Use eBPF before writing it

Goal: build intuition for *what* eBPF programs do before touching code.

- Install `bpftrace` and BCC tools (`sudo apt install bpftrace bpfcc-tools`)
- Run and read the source of: `execsnoop`, `opensnoop`, `tcplife`, `biolatency`
- Write 5 one-liners in bpftrace: count syscalls by process, trace `execve`, histogram of read() sizes, latency of a syscall, print stack on a kprobe
- Read: Brendan Gregg's bpftrace one-liners cheatsheet (ebpf.io has a curated list)

Checkpoint: explain **probe**, **map**, and **verifier** in your own words.

## Phase 2 (Days 4-7): Write your first programs (BCC/Python, fast iteration)

Goal: lowest-friction path to "I wrote and loaded a real eBPF program."

- BCC's Python tutorial (`tutorial.md` in iovisor/bcc repo) — do it fully, don't skim
- Labs:
  1. Hello-world kprobe on `sys_clone`/`execve` that prints via `bpf_trace_printk`
  2. Syscall counter using a BPF hash map, read from userspace every second
  3. Track file opens per-process, filter by PID in the eBPF program itself (not in userspace)
- Understand *why* BCC compiles at runtime (and why that's a problem — sets up Phase 3)

## Phase 3 (Week 2): Modern path - libbpf + CO-RE

This is how production eBPF is written today (BCC is now considered legacy for new projects).

- Clone `libbpf/libbpf-bootstrap` — designed as a teaching scaffold
- Work through examples in order: `minimal` -> `bootstrap` (process exec/exit tracking) -> `uprobe` -> `tc`
- Learn: BTF, `vmlinux.h`, the skeleton codegen workflow (`bpftool gen skeleton`), `libbpf_open`/`load`/`attach`
- Lab: rewrite one Phase 2 BCC program as a libbpf CO-RE program with a proper Makefile

Checkpoint: understand why CO-RE programs run unmodified across kernel versions without recompiling.

## Phase 4 (Week 3): Networking - XDP and TC

- Read the XDP intro on the Cilium/ebpf.io docs
- Lab: XDP packet counter/drop-by-IP program (`xdp-project/xdp-tutorial` is excellent)
- Lab: TC-based traffic shaping or redirect example
- Understand XDP (pre-network-stack, driver level) vs TC (post-stack, more flexible but slower)

## Phase 5 (Week 4): Pick a userspace language and go deeper

- **Go**: `cilium/ebpf` library — idiomatic, no cgo/libbpf dependency, great for building real tools. Port one Phase 3 program to Go.
- Or stay in C/libbpf if you want closer-to-kernel understanding first, then add Go later.

## Phase 6 (Week 5-6): Capstone project

Pick one that's genuinely useful, not a toy:

- A syscall-based security monitor (detect suspicious `execve` chains)
- A network-latency profiler for a service you run
- A lightweight process/container resource tracker (cgroup-aware)
- An eBPF-based profiler for GPU/CPU syscall bottlenecks during chess-dl-engine training runs

## Core resources

- Book: *Learning eBPF* by Liz Rice (free chapters + O'Reilly) — best linear intro
- `ebpf.io` — official docs hub, links to bpftrace, libbpf, cilium/ebpf
- `github.com/iovisor/bcc` — tutorial.md + tools source as read material
- `github.com/libbpf/libbpf-bootstrap` — Phase 3 spine
- `github.com/xdp-project/xdp-tutorial` — Phase 4 spine
- `github.com/cilium/ebpf` — Go library + examples
- Brendan Gregg's blog — deep dives once you hit performance-tracing questions

## Suggested pace

~6 weeks at a few hours/week, front-loaded toward Phase 1-3 since that's where the mental model forms.
Phases 4-6 move faster once the fundamentals click.
