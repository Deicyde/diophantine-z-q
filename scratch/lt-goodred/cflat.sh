#!/bin/bash
# compile the flat file GoodRed.lean with lake env lean (one Lean process)
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
S=scratch/lt-goodred
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean $S/GoodRed.lean > $S/olean/flat_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -c "error" $S/olean/flat_out.txt; grep -c "sorry" $S/olean/flat_out.txt
grep "depends on axioms" $S/olean/flat_out.txt | grep -c "\[propext, Classical.choice, Quot.sound\]"
grep "depends on axioms" $S/olean/flat_out.txt | grep -v "\[propext, Classical.choice, Quot.sound\]"
grep "depends on axioms" $S/olean/flat_out.txt | grep "LTGoodRed"
