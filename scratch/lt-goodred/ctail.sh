#!/bin/bash
# compile olean/Tail.lean (= "import LGPrefix" + parts/*.lean) against LGPrefix.olean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/lt-goodred/olean
S=scratch/lt-goodred
{ echo "import LGPrefix"; echo; for p in $S/parts/*.lean; do cat $p; echo; done; } > $D/Tail.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $D/Tail.lean" > $D/Tail_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
awk '/error/{c=14} c>0{print; c--}' $D/Tail_out.txt | head -${1:-80}; grep -c "error" $D/Tail_out.txt; grep "depends on axioms" $D/Tail_out.txt | head -20
