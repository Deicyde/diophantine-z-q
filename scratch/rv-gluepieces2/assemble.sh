#!/bin/bash
# olean/TailBase.lean = "import LPrefix" + imports_extra.txt + parts/*.lean   (compile with: ctail.sh TailBase.lean TailBase)
# olean/Check_<name>.lean = "import TailBase" + checks/<name>.lean          (compile with: ctail.sh Check_<name>.lean)
# parts/ = scratch/g0-assemble/parts/ verbatim, except 40_fibresimple.lean (§5 demo lemmas take the
# two pin clauses for the twisted Φ as a hypothesis). LPrefix = post-pin-apply Leaves.lean.
cd "$(dirname "$0")"
{ echo "import LPrefix"; cat imports_extra.txt; echo; for p in parts/*.lean; do cat $p; echo; done; } > olean/TailBase.lean
for c in checks/*.lean; do b=$(basename $c .lean); { echo "import TailBase"; echo; cat $c; } > olean/Check_$b.lean; done
cp final/c12_bundle.lean olean/Check_c12_bundle.lean
wc -l olean/TailBase.lean olean/Check_*.lean
