#!/bin/bash
# assemble-port: g0-assemble3's assembly ported onto leaf-fold2's base: LeavesP.lean = scratch/h-decomposition/Leaves.lean
# (copied verbatim to Leaves.lean here) with leaf-fold2's prefix edit (ten unused TextbookLeaves fields deleted; made by
# mk/mk_prefix.py; its body is contained verbatim in scratch/leaf-fold2/Leaves2.lean). Every part is inside `namespace HDec`.
# olean/LPrefix.lean = LeavesP.lean (a complete module ending in `end HDec`)
# olean/TailA.lean = "import LPrefix" + imports_extra.txt + PRE + parts/[0-9]*.lean + "end HDec"
# olean/TailB = "import TailA" + PRE + parts a10-a44; TailC = a45-a99; TailE = b*-c*; TailF = d*-y*; TailD = z*
#   (after TailA each part is wrapped in its own `section G0A3_<name> … end G0A3_<name>`)
# PRE = `namespace HDec`, Leaves.lean's `set_option maxHeartbeats 1000000` and its TauCeti `attribute [-instance]` line
# imports_tailD.txt: extra kernel imports needed only by the z* parts (TailD header; flat file header)
# AssemblePort.lean (flat) = LeavesP.lean minus its last line `end HDec`, imports_extra.txt + imports_tailD.txt after its first 3 lines,
#   + all parts in the same order + `end HDec`
cd "$(dirname "$0")"
python3 -I mk/mk_prefix.py >/dev/null || exit 1
PRE='namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension
'
wrap() { for p in "$@"; do n=$(basename $p .lean); echo "section G0A3_$n"; cat $p; echo; echo "end G0A3_$n"; echo; done; }
B=$(ls parts/a[0-3]*.lean parts/a4[0-4]*.lean 2>/dev/null); D=$(ls parts/z*.lean); C=$(ls parts/a*.lean | grep -v -F "$B")
E=$(ls parts/[b-c]*.lean); F=$(ls parts/[d-y]*.lean)
N=$(wc -l < LeavesP.lean); [ "$(tail -1 LeavesP.lean)" = "end HDec" ] || { echo "LeavesP.lean must end in 'end HDec'"; exit 1; }
{ echo "import LPrefix"; cat imports_extra.txt; echo; echo "$PRE"; for p in parts/[0-9]*.lean; do cat $p; echo; done; echo "end HDec"; } > olean/TailA.lean
{ echo "import TailA"; echo; echo "$PRE"; wrap $B; echo "end HDec"; } > olean/TailB.lean
{ echo "import TailB"; echo; echo "$PRE"; wrap $C; echo "end HDec"; } > olean/TailC.lean
{ echo "import TailC"; echo; echo "$PRE"; wrap $E; echo "end HDec"; } > olean/TailE.lean
{ echo "import TailE"; echo; echo "$PRE"; wrap $F; echo "end HDec"; } > olean/TailF.lean
{ echo "import TailF"; cat imports_tailD.txt; echo; echo "$PRE"; wrap $D; echo "end HDec"; } > olean/TailD.lean
{ sed -n 1,3p LeavesP.lean; cat imports_extra.txt imports_tailD.txt; sed -n "4,$((N-1))p" LeavesP.lean; echo; for p in parts/[0-9]*.lean; do cat $p; echo; done; wrap $B $C $E $F $D; echo "end HDec"; } > AssemblePort.lean
wc -l olean/TailA.lean olean/TailB.lean olean/TailC.lean olean/TailE.lean olean/TailF.lean olean/TailD.lean AssemblePort.lean
