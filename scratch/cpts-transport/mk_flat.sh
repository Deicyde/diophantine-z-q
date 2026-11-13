#!/bin/bash
# Flat file: g0-assemble3's G0Assemble3.lean, regenerated exactly as its assemble.sh does (from the merged
# scratch/g0-assemble3/ sources, read-only), + this task's sections and GluePieces5 (the part of Bundle5.lean after
# the TailD body). Output: scratch/cpts-transport/Flat5.lean (not committed; regenerate with this script).
cd "$(dirname "$0")"
G=../g0-assemble3
wrap() { for p in "$@"; do n=$(basename $p .lean); echo "section G0A3_$n"; cat $p; echo; echo "end G0A3_$n"; echo; done; }
( cd $G
B=$(ls parts/a[0-3]*.lean parts/a4[0-4]*.lean 2>/dev/null); D=$(ls parts/z*.lean); C=$(ls parts/a*.lean | grep -v -F "$B")
E=$(ls parts/[b-c]*.lean); F=$(ls parts/[d-y]*.lean)
{ sed -n 1,3p Leaves.lean; cat imports_extra.txt; sed -n '4,$p' Leaves.lean; echo; for p in parts/[0-9]*.lean; do cat $p; echo; done; wrap $B $C $E $F $D; } ) > Flat5_base.lean
md5sum Flat5_base.lean; cat $G/flat_md5.txt
n=$(grep -n '^section CPtsTransportSec' Bundle5.lean | cut -d: -f1)
{ cat Flat5_base.lean; tail -n +$n Bundle5.lean; } > Flat5.lean
rm Flat5_base.lean
wc -l Flat5.lean
