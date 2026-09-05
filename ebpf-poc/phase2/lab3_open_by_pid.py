#!/usr/bin/env python3
# Phase 2, Lab 3: track file opens for one target PID, filtered inside the eBPF program itself.
import sys
from bcc import BPF

if len(sys.argv) != 2:
    print(f"usage: {sys.argv[0]} <pid>")
    sys.exit(1)

target_pid = int(sys.argv[1])

program = r"""
struct data_t {
    char fname[128];
};
BPF_PERF_OUTPUT(events);

TRACEPOINT_PROBE(syscalls, sys_enter_openat) {
    u32 pid = bpf_get_current_pid_tgid() >> 32;
    if (pid != TARGET_PID) {
        return 0;   // filtering happens in-kernel: only TARGET_PID's events reach userspace
    }

    struct data_t data = {};
    bpf_probe_read_user_str(&data.fname, sizeof(data.fname), args->filename);
    events.perf_submit(args, &data, sizeof(data));
    return 0;
}
"""
program = program.replace("TARGET_PID", str(target_pid))

b = BPF(text=program)

def handle_event(cpu, data, size):
    event = b["events"].event(data)
    print(f"pid {target_pid} opened: {event.fname.decode('utf-8', 'replace')}")

b["events"].open_perf_buffer(handle_event)

print(f"Tracing openat() for PID {target_pid} only (filtered in-kernel). Ctrl-C to end.")
try:
    while True:
        b.perf_buffer_poll()
except KeyboardInterrupt:
    pass
