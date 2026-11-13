#!/bin/bash
# olean/TailA.lean = "import LPrefix" + imports_extra.txt + g0-assemble's parts (parts/[0-9]*.lean)
# olean/TailB.lean = "import TailA" + g0-assemble2's parts (parts/[a-z]*.lean)
# G0Assemble2.lean = Leaves.lean (verbatim copy of scratch/h-decomposition/Leaves.lean) with the
#   imports of imports_extra.txt added after its three imports, + all parts in order
cd "$(dirname "$0")"
{ echo "import LPrefix"; cat imports_extra.txt; echo; for p in parts/[0-9]*.lean; do cat $p; echo; done; } > olean/TailA.lean
{ echo "import TailA"; echo; for p in parts/[a-z]*.lean; do cat $p; echo; done; } > olean/TailB.lean
{ sed -n 1,3p Leaves.lean; cat imports_extra.txt; sed -n '4,$p' Leaves.lean; echo; for p in parts/[0-9]*.lean parts/[a-z]*.lean; do cat $p; echo; done; } > G0Assemble2.lean
wc -l olean/TailA.lean olean/TailB.lean G0Assemble2.lean
