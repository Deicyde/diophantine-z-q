#!/bin/bash
# Generate the library modules ZInQKernel/OneProof/H/*.lean from scratch/assemble-port (the H assembly
# HDec.HSyn.sixContactMin_of_leaves5) and ZInQKernel/OneProof/TopChain.lean from scratch/frontier/TopChain.lean.
# The module split is assemble-port's olean chain (assemble.sh): Prefix = LeavesP.lean; TailA = parts/[0-9]*;
# TailB = parts a00-a44; TailC = the other a*; TailE = b*-c*; TailF = d*-y*; TailD = z*. After TailA each part is wrapped
# in `section G0A3_<name> ... end G0A3_<name>`, exactly as assemble.sh does. Sources are copied verbatim; only the
# import lines naming the chain's own modules change.
set -euo pipefail
cd "$(dirname "$0")/../.."
S=scratch/assemble-port
O=ZInQKernel/OneProof
mkdir -p "$O/H"
PRE='namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension
'
wrap() { for p in "$@"; do n=$(basename "$p" .lean); echo "section G0A3_$n"; cat "$p"; echo; echo "end G0A3_$n"; echo; done; }
[ "$(tail -1 $S/LeavesP.lean)" = "end HDec" ] || { echo "LeavesP.lean must end in 'end HDec'"; exit 1; }
B=$(ls $S/parts/a[0-3]*.lean $S/parts/a4[0-4]*.lean 2>/dev/null)
C=$(ls $S/parts/a*.lean | grep -v -F "$B")
E=$(ls $S/parts/[b-c]*.lean); F=$(ls $S/parts/[d-y]*.lean); D=$(ls $S/parts/z*.lean)
cp $S/LeavesP.lean $O/H/Prefix.lean
{ echo "import ZInQKernel.OneProof.H.Prefix"; cat $S/imports_extra.txt; echo; echo "$PRE"; for p in $S/parts/[0-9]*.lean; do cat "$p"; echo; done; echo "end HDec"; } > $O/H/TailA.lean
{ echo "import ZInQKernel.OneProof.H.TailA"; echo; echo "$PRE"; wrap $B; echo "end HDec"; } > $O/H/TailB.lean
{ echo "import ZInQKernel.OneProof.H.TailB"; echo; echo "$PRE"; wrap $C; echo "end HDec"; } > $O/H/TailC.lean
{ echo "import ZInQKernel.OneProof.H.TailC"; echo; echo "$PRE"; wrap $E; echo "end HDec"; } > $O/H/TailE.lean
{ echo "import ZInQKernel.OneProof.H.TailE"; echo; echo "$PRE"; wrap $F; echo "end HDec"; } > $O/H/TailF.lean
{ echo "import ZInQKernel.OneProof.H.TailF"; cat $S/imports_tailD.txt; echo; echo "$PRE"; wrap $D; echo "end HDec"; } > $O/H/TailD.lean
grep -v -E '^#print' scratch/frontier/TopChain.lean > $O/TopChain.lean
wc -l $O/H/*.lean $O/TopChain.lean
