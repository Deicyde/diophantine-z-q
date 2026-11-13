#!/bin/bash
# olean/Tail.lean = "import LPrefix" + imports_extra.txt + parts/*.lean (iteration against the Leaves.lean olean)
# G0Assemble.lean = Leaves.lean (verbatim copy of scratch/h-decomposition/Leaves.lean) with the
#   imports of imports_extra.txt added after its three imports, + parts/*.lean
cd "$(dirname "$0")"
{ echo "import LPrefix"; cat imports_extra.txt; echo; for p in parts/*.lean; do cat $p; echo; done; } > olean/Tail.lean
{ sed -n 1,3p Leaves.lean; cat imports_extra.txt; sed -n '4,$p' Leaves.lean; echo; for p in parts/*.lean; do cat $p; echo; done; } > G0Assemble.lean
wc -l olean/Tail.lean G0Assemble.lean
