#!/usr/bin/env python3
# Phase 2, Lab 1: hello-world kprobe on execve, printing via bpf_trace_printk.
from bcc import BPF

program = r"""
int hello(void *ctx) {
    bpf_trace_printk("Hello, eBPF! execve called.\n");
    return 0;
}
"""

b = BPF(text=program)
b.attach_kprobe(event=b.get_syscall_fnname("execve"), fn_name="hello")

print("Tracing execve... Ctrl-C to end.")
b.trace_print()
