#!/usr/bin/env python3
import os, time
print(os.getpid(), flush=True)
for _ in range(300):
    fd = os.open("/tmp/foo.txt", os.O_RDONLY)
    os.close(fd)
    time.sleep(0.1)
