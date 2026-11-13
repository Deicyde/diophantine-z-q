#!/bin/bash
# olean/TailA.lean = "import LPrefix" + imports_extra.txt + g0-assemble's parts (parts/[0-9]*.lean)
# olean/TailB.lean = "import TailA" + g0-assemble2's parts a10-a44; olean/TailC.lean = "import TailB" + parts
#   a45-a99; olean/TailE.lean = "import TailC" + g0-assemble3's parts b*-y*; olean/TailD.lean = "import TailE"
#   + parts z*; each part after TailA is wrapped in its own `section G0A3_<name> … end G0A3_<name>`
#   so that its `open`s do not leak into later parts
# G0Assemble3.lean = Leaves.lean (verbatim copy of g0-assemble2's copy of scratch/h-decomposition/Leaves.lean)
#   with the imports of imports_extra.txt added after its three imports, + all parts in the same order
cd "$(dirname "$0")"
wrap() { for p in "$@"; do n=$(basename $p .lean); echo "section G0A3_$n"; cat $p; echo; echo "end G0A3_$n"; echo; done; }
B=$(ls parts/a[0-3]*.lean parts/a4[0-4]*.lean 2>/dev/null); D=$(ls parts/z*.lean); C=$(ls parts/a*.lean | grep -v -F "$B")
E=$(ls parts/[b-y]*.lean)
{ echo "import LPrefix"; cat imports_extra.txt; echo; for p in parts/[0-9]*.lean; do cat $p; echo; done; } > olean/TailA.lean
{ echo "import TailA"; echo; wrap $B; } > olean/TailB.lean
{ echo "import TailB"; echo; wrap $C; } > olean/TailC.lean
{ echo "import TailC"; echo; wrap $E; } > olean/TailE.lean
{ echo "import TailE"; echo; wrap $D; } > olean/TailD.lean
{ sed -n 1,3p Leaves.lean; cat imports_extra.txt; sed -n '4,$p' Leaves.lean; echo; for p in parts/[0-9]*.lean; do cat $p; echo; done; wrap $B $C $E $D; } > G0Assemble3.lean
wc -l olean/TailA.lean olean/TailB.lean olean/TailC.lean olean/TailE.lean olean/TailD.lean G0Assemble3.lean
