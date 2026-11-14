#!/bin/bash
# leaf-fold5: chain sources for the modules after leaf-fold4's TailK, and the flat file Leaves5.lean.
#   olean/TailL.lean = import TailK + kernel SmoothFibre + parts/e10_vertmodel.lean (mk_e10.py: vert-witness + model-glue), inside `namespace HDec`
#   olean/TailM.lean = import TailL + kernel AVB1, CurvesG, NeronC + parts/e20_*.lean (av-b2's AVB2Main body and the
#                      transports of the kernel's av-b1/curves-g/neron-c theorems), inside `namespace HDec`
#   olean/TailN.lean = import TailM + parts/e90_fold5.lean (hand-written: the bundles and sixContactMin_of_open5)
#   Leaves5.lean     = scratch/leaf-fold4/Leaves4.lean with the new imports added to its header, then the three bodies
cd "$(dirname "$0")"
HDR='namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension
'
wrapF() { for p in "$@"; do n=$(basename $p .lean); echo "section G0A2_$n"; cat $p; echo; k=$(python3 py/balance.py $p); for i in $(seq 1 $k); do echo "end"; done; echo "end G0A2_$n"; echo; done; }
L=$(ls parts/e1*.lean); M=$(ls parts/e[2-8]*.lean 2>/dev/null); N=$(ls parts/e9*.lean 2>/dev/null)
LIMP='import ZInQKernel.Contrib.SmoothFibre.Basic'
MIMP='import ZInQKernel.Contrib.AVB2.SerreLemma
import ZInQKernel.Contrib.AVB1.AlgClosed
import ZInQKernel.Contrib.AVB1.Poincare
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.NeronC.NMPInjective
import ZInQKernel.Contrib.NeronC.NeronGroup
import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.HomUnify.Corr
import ZInQKernel.HDecomp.ModCurves.C9'
body() { echo "$HDR"; wrapF "$@"; echo "end HDec"; }
{ echo "import TailK"; echo "$LIMP"; echo; body $L; } > olean/TailL.lean
[ -n "$M" ] && { echo "import TailL"; echo "$MIMP"; echo; body $M; } > olean/TailM.lean
[ -n "$N" ] && { echo "import TailM"; echo; body $N; } > olean/TailN.lean
# flat file: Leaves4.lean's header imports, the new imports, the rest of Leaves4.lean, then the new bodies
F4=../leaf-fold4/Leaves4.lean
NI=$(grep -n -v '^import ' $F4 | head -1 | cut -d: -f1)
{ head -n $((NI-1)) $F4; echo "$LIMP"; [ -n "$M" ] && echo "$MIMP";
  tail -n +$NI $F4; echo;
  echo "/-! ## leaf-fold5: the parts after leaf-fold4 (modules TailL, TailM, TailN of the olean chain) -/"
  body $L; [ -n "$M" ] && body $M; [ -n "$N" ] && body $N; } > Leaves5.lean
wc -l olean/*.lean Leaves5.lean
