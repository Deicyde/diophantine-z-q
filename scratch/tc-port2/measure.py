#!/usr/bin/env python3
"""Run a command under /usr/bin/time -v and record the cgroup memory.peak before/after, plus a
per-fd reset peak (Linux >= 6.12: writing to memory.peak resets the peak seen through that fd).
usage: measure.py LOGFILE CMD...
"""
import os, subprocess, sys, time
log, cmd = sys.argv[1], sys.argv[2:]
cg = '/sys/fs/cgroup' + open('/proc/self/cgroup').read().strip().split(':', 2)[2]
peakf = os.path.join(cg, 'memory.peak')
before = open(peakf).read().strip()
fd = None
try:
    fd = os.open(peakf, os.O_RDWR); os.write(fd, b'reset\n')
except OSError as e:
    print('per-fd reset unavailable:', e)
t0 = time.time()
with open(log, 'w') as out:
    r = subprocess.run(['/usr/bin/time', '-v'] + cmd, stdout=out, stderr=subprocess.STDOUT)
t1 = time.time()
after = open(peakf).read().strip()
reset_peak = None
if fd is not None:
    os.lseek(fd, 0, 0); reset_peak = os.read(fd, 100).decode().strip()
summary = (f'exit {r.returncode}; wall {t1-t0:.1f} s; cgroup {cg}\n'
           f'memory.peak before {before} B ({int(before)/2**30:.2f} GiB), after {after} B ({int(after)/2**30:.2f} GiB)\n'
           f'memory.peak since per-fd reset: {reset_peak} B' + (f' ({int(reset_peak)/2**30:.2f} GiB)' if reset_peak else '') + '\n')
with open(log, 'a') as out: out.write('\n=== measure.py ===\n' + summary)
print(summary)
