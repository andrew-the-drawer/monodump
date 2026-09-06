// SPDX-License-Identifier: GPL-2.0 OR BSD-3-Clause
// Userspace loader for the Phase 3 CO-RE rewrite of Phase 2's syscall counter.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <bpf/libbpf.h>
#include <bpf/bpf.h>
#include "syscount.skel.h"

#define TASK_COMM_LEN 16
#define TOP_N 10

struct syscall_count {
	__u64 count;
	char comm[TASK_COMM_LEN];
};

struct entry {
	__u32 pid;
	struct syscall_count val;
};

static volatile sig_atomic_t exiting;

static void sig_handler(int sig)
{
	exiting = 1;
}

static int libbpf_print_fn(enum libbpf_print_level level, const char *format, va_list args)
{
	return vfprintf(stderr, format, args);
}

static int cmp_count_desc(const void *a, const void *b)
{
	const struct entry *ea = a, *eb = b;

	if (eb->val.count != ea->val.count)
		return (eb->val.count > ea->val.count) - (eb->val.count < ea->val.count);
	return 0;
}

int main(int argc, char **argv)
{
	struct syscount_bpf *skel;
	int err, map_fd;
	struct entry *entries = NULL;
	size_t cap = 0, n;

	libbpf_set_print(libbpf_print_fn);
	signal(SIGINT, sig_handler);
	signal(SIGTERM, sig_handler);

	skel = syscount_bpf__open_and_load();
	if (!skel) {
		fprintf(stderr, "Failed to open/load BPF skeleton\n");
		return 1;
	}

	err = syscount_bpf__attach(skel);
	if (err) {
		fprintf(stderr, "Failed to attach BPF skeleton: %d\n", err);
		goto cleanup;
	}

	map_fd = bpf_map__fd(skel->maps.counts);

	printf("Counting read() syscalls per PID, every 1s. Ctrl-C to end.\n");

	while (!exiting) {
		sleep(1);
		if (exiting)
			break;

		printf("---\n");

		n = 0;
		__u32 key, next_key;
		int have_key = 0;

		while (bpf_map_get_next_key(map_fd, have_key ? &key : NULL, &next_key) == 0) {
			struct syscall_count val;

			if (bpf_map_lookup_elem(map_fd, &next_key, &val) == 0) {
				if (n == cap) {
					cap = cap ? cap * 2 : 64;
					entries = realloc(entries, cap * sizeof(*entries));
				}
				entries[n].pid = next_key;
				entries[n].val = val;
				n++;
			}
			key = next_key;
			have_key = 1;
		}

		qsort(entries, n, sizeof(*entries), cmp_count_desc);

		for (size_t i = 0; i < n && i < TOP_N; i++)
			printf("%8u %-16s %llu\n", entries[i].pid, entries[i].val.comm,
			       (unsigned long long)entries[i].val.count);

		/* clear the map, mirroring counts.clear() in the BCC version */
		for (size_t i = 0; i < n; i++)
			bpf_map_delete_elem(map_fd, &entries[i].pid);
	}

	printf("\nDetaching and exiting.\n");

cleanup:
	free(entries);
	syscount_bpf__destroy(skel);
	return err < 0 ? -err : 0;
}
