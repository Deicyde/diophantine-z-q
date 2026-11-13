#!/bin/bash
# Integration check against linked-tate's committed files (read only), olean chain, one Lean process
# at a time:  LTPrefix = linked-tate's Leaves.lean + imports_extra.txt (as its build_prefix.sh);
# LTTail = import LTPrefix + scratch/linked-tate/parts/*.lean; Integ = import LTTail + 99d + 99e.
# Usage: build.sh prefix | tail | integ
cd "$(dirname "$0")/../../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/lt-goodred/integ/olean; mkdir -p $D
LT=scratch/linked-tate
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
case $1 in
prefix)
  { sed -n 1,3p $LT/Leaves.lean; cat $LT/imports_extra.txt; sed -n '4,$p' $LT/Leaves.lean; } > $D/LTPrefix.lean
  lake env lean -o $D/LTPrefix.olean -i $D/LTPrefix.ilean $D/LTPrefix.lean > $D/prefix_out.txt 2>&1; F=prefix_out;;
tail)
  { echo "import LTPrefix"; echo; for p in $LT/parts/*.lean; do cat $p; echo; done; } > $D/LTTail.lean
  lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean -o $D/LTTail.olean -i $D/LTTail.ilean $D/LTTail.lean" > $D/tail_out.txt 2>&1; F=tail_out;;
integ)
  python3 scratch/lt-goodred/integ/make_proofs.py
  { echo "import LTTail"; echo; cat scratch/lt-goodred/integ/99d_proofs.lean; echo; cat scratch/lt-goodred/integ/99e_bundle4.lean; } > $D/Integ.lean
  lake env bash -c "LEAN_PATH=$D:\$LEAN_PATH lean $D/Integ.lean" > $D/integ_out.txt 2>&1; F=integ_out;;
esac
echo "exit $? in $(( $(date +%s) - start ))s"
awk '/error/{c=14} c>0{print; c--}' $D/$F.txt | head -80; grep -c "error" $D/$F.txt
grep "depends on axioms" $D/$F.txt | grep -c "\[propext, Classical.choice, Quot.sound\]"
grep "depends on axioms" $D/$F.txt | grep -v "\[propext, Classical.choice, Quot.sound\]" | head
