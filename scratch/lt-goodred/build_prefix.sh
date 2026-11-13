#!/bin/bash
# olean/LGPrefix.lean = lines 1-14993 of scratch/linked-tate/Leaves.lean (a byte-identical copy of the
# pin-applied scratch/h-decomposition/Leaves.lean) + the four closers of the blocks open at line 14993
# (namespace LeafQM.AV, namespace LeafQM, noncomputable section, section LeafQMSec). Compiled to an olean.
cd "$(dirname "$0")/../.."
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
D=$PWD/scratch/lt-goodred/olean
{ sed -n 1,14993p scratch/linked-tate/Leaves.lean; printf '\nend AV\n\nend LeafQM\n\nend\n\nend LeafQMSec\n'; } > $D/LGPrefix.lean
uptime | sed 's/.*load/load/'; free -g | sed -n 2p
start=$(date +%s)
lake env lean -o $D/LGPrefix.olean -i $D/LGPrefix.ilean $D/LGPrefix.lean > $D/prefix_out.txt 2>&1
echo "exit $? in $(( $(date +%s) - start ))s"
grep -E "error" $D/prefix_out.txt | head -20
