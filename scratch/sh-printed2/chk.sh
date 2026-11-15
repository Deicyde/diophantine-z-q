#!/bin/bash
# Re-check the deliverable in a built worktree (kernel modules built, e.g. a copy of ~/dzq-check2's .lake/build
# and lean/.lake/build at b5ff0474), one Lean process.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
scratch/sh-printed2/mk.sh PartB PartS PartU PartF
/usr/bin/time -f "%e s %M KB" lake env lean scratch/sh-printed2/ShPrinted2.lean 2>&1 | grep "depends on axioms\|error\| s .*KB\|sorry"
