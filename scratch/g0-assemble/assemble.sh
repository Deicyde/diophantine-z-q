#!/bin/bash
# olean/Tail.lean = "import LPrefix" + parts/*.lean (for iteration against the Leaves.lean olean)
# G0Assemble.lean = Leaves.lean (verbatim copy of scratch/h-decomposition/Leaves.lean) + parts/*.lean
cd "$(dirname "$0")"
{ echo "import LPrefix"; echo; for p in parts/*.lean; do cat $p; echo; done; } > olean/Tail.lean
{ cat Leaves.lean; echo; for p in parts/*.lean; do cat $p; echo; done; } > G0Assemble.lean
wc -l olean/Tail.lean G0Assemble.lean
