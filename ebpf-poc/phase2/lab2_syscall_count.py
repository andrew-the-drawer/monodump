#!/usr/bin/env python3
# Phase 2, Lab 2: count syscalls per-PID in a BPF hash map, polled from userspace every second.
import time
from bcc import BPF

program = r"""
BPF_HASH(counts, u32, u64);

int count_syscall(void *ctx) {
    u32 pid = bpf_get_current_pid_tgid() >> 32;
    u64 zero = 0, *val;
    val = counts.lookup_or_try_init(&pid, &zero);
    if (val) {
        (*val)++;
    }
    return 0;
}
"""

b = BPF(text=program)
b.attach_kprobe(event=b.get_syscall_fnname("read"), fn_name="count_syscall")

print("Counting read() syscalls per PID, every 1s. Ctrl-C to end.")
counts = b["counts"]
try:
    while True:
        time.sleep(1)
        print("---")
        for pid, count in sorted(counts.items(), key=lambda kv: kv[1].value, reverse=True)[:10]:
            try:
                comm = open(f"/proc/{pid.value}/comm").read().strip()
            except FileNotFoundError:
                comm = "?"
            print(f"{pid.value:8d} {comm:16s} {count.value}")
        counts.clear()
except KeyboardInterrupt:
    pass
