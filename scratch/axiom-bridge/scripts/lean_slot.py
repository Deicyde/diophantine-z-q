#!/usr/bin/env python3
"""A Lean subprocess slot gate used by measure.py; never edits the real toolchain."""
import hashlib
import os
from pathlib import Path
import subprocess
import sys

real = os.environ["AXIOM_REAL_LEAN"]
# Toolchain-discovery commands do not elaborate modules.
if any(a in sys.argv[1:] for a in ("--print-prefix", "--print-libdir", "--version", "--githash")):
    os.execv(real, [real, *sys.argv[1:]])
fd = os.open(os.environ["AXIOM_SLOT_FIFO"], os.O_RDWR)
token = os.read(fd, 1)
try:
    args = sys.argv[1:]
    source = next((a for a in args if a.endswith(".lean")), "unknown")
    key = hashlib.sha256((os.getcwd() + "\0" + source).encode()).hexdigest()[:16]
    stats = Path(os.environ["AXIOM_STATS_DIR"])
    (stats / (key + ".source")).write_text(os.getcwd() + "\n" + source + "\n")
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    proc = subprocess.Popen(["/usr/bin/time", "-v", "-o", str(stats / (key + ".time")),
                             real, *args], env=env)
    (stats / (key + ".pid")).write_text(str(proc.pid))
    rc = proc.wait()
    (stats / (key + ".exit")).write_text(str(rc))
    (stats / (key + ".pid")).unlink(missing_ok=True)
finally:
    os.write(fd, token)
    os.close(fd)
sys.exit(rc)
