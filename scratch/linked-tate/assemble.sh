#!/bin/bash
# olean/Tail.lean = "import LPrefix" + parts/*.lean (iteration against the Leaves.lean olean)
# LinkedTate.lean = Leaves.lean (verbatim copy of scratch/h-decomposition/Leaves.lean) with the
#   imports of imports_extra.txt added after its three imports, + parts/*.lean (the flat file)
cd "$(dirname "$0")"
{ echo "import LPrefix"; echo; for p in parts/*.lean; do cat $p; echo; done; } > olean/Tail.lean
{ sed -n 1,3p Leaves.lean; cat imports_extra.txt; sed -n '4,$p' Leaves.lean; echo; for p in parts/*.lean; do cat $p; echo; done; } > LinkedTate.lean
wc -l olean/Tail.lean LinkedTate.lean
