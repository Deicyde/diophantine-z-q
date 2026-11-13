#!/bin/bash
# olean/Tail.lean = "import LPrefix" + imports_extra.txt + parts/*.lean
# parts/ = scratch/g0-assemble/parts/ verbatim, except 40_fibresimple.lean (§5 demo lemmas take the
# two pin clauses for the twisted Φ as a hypothesis). LPrefix = post-pin-apply Leaves.lean.
cd "$(dirname "$0")"
{ echo "import LPrefix"; cat imports_extra.txt; echo; for p in parts/*.lean checks/*.lean; do cat $p; echo; done; } > olean/Tail.lean
wc -l olean/Tail.lean
