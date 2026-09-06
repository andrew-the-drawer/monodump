// SPDX-License-Identifier: GPL-2.0 OR BSD-3-Clause
// Phase 3 lab: CO-RE rewrite of Phase 2's lab2_syscall_count.py (BCC).
#include "vmlinux.h"
#include <bpf/bpf_helpers.h>

char LICENSE[] SEC("license") = "Dual BSD/GPL";

#define TASK_COMM_LEN 16

struct syscall_count {
	__u64 count;
	char comm[TASK_COMM_LEN];
};

struct {
	__uint(type, BPF_MAP_TYPE_HASH);
	__uint(max_entries, 8192);
	__type(key, u32);
	__type(value, struct syscall_count);
} counts SEC(".maps");

SEC("tp/syscalls/sys_enter_read")
int count_read(void *ctx)
{
	u32 pid = bpf_get_current_pid_tgid() >> 32;
	struct syscall_count *val, zero = {};

	val = bpf_map_lookup_elem(&counts, &pid);
	if (!val) {
		bpf_get_current_comm(&zero.comm, sizeof(zero.comm));
		zero.count = 1;
		/* BPF_NOEXIST: if another CPU won the race to insert this pid
		 * first, drop this increment rather than clobber their entry.
		 * Same one-count-lost-on-first-touch tradeoff BCC's
		 * lookup_or_try_init has; harmless for a top-N counter. */
		bpf_map_update_elem(&counts, &pid, &zero, BPF_NOEXIST);
		return 0;
	}

	/* Unlike the Phase 2 BCC version's plain `(*val)++` (a data race
	 * when two threads of the same PID hit read() on different CPUs
	 * at once), this increment is atomic. */
	__sync_fetch_and_add(&val->count, 1);
	return 0;
}
