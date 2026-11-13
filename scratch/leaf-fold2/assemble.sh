#!/bin/bash
# leaf-fold2: build the olean chain sources and the flat file Leaves2.lean.
#   olean/LPrefix.lean   = mk_prefix.py (h-decomposition/Leaves.lean, HDec-wrapped by leaf-fold; ten unused fields deleted)
#   olean/TailA.lean     = import LPrefix + g0-assemble's 18 parts (parts/[0-9]*.lean), inside `namespace HDec`
#   olean/TailB/C/D.lean = g0-assemble2's parts a10-a44 / a45-a95 / z*, each part in its own section, inside `namespace HDec`
#   olean/LF2ImagePlane.lean = scratch/image-plane/ImagePlaneFinal.lean, verbatim (root namespace, kernel objects)
#   olean/LF2Stalks.lean = LF2Stalks.lean.src (infra-stalks' general stalk lemmas, root namespace)
#   olean/LF2UnifRoot.lean, LF2SmoothDim.lean = mk_unifdims.py outputs (root namespace)
#   olean/LF2UnramConj.lean = scratch/inner-twist/UnramConj.lean verbatim (root namespace)
#   olean/TailE.lean     = import TailD + kernel T14/T28/RLeaf + LF2ImagePlane + parts b*, inside `namespace HDec`
#   Leaves2.lean         = all of the above in one file (LF2ImagePlane's body at root level, before TailE's body)
cd "$(dirname "$0")"
python3 mk_prefix.py >/dev/null
HDR='namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension
'
wrap() { for p in "$@"; do n=$(basename $p .lean); echo "section G0A2_$n"; cat $p; echo; echo "end G0A2_$n"; echo; done; }
A=$(ls parts/[0-9]*.lean); B=$(ls parts/a[0-3]*.lean parts/a4[0-4]*.lean); C=$(ls parts/a*.lean | grep -v -F "$B"); D=$(ls parts/z*.lean); E=$(ls parts/b*.lean)
EIMP='import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.X1ConstantField'
IPIMP=$( (grep '^import ' ../image-plane/ImagePlaneFinal.lean; echo 'import ZInQKernel.HDecomp.Objects'; grep '^import ' LF2UnramConj.lean.src) )
rootbody() { echo "section LF2Root_$2"; grep -v '^import ' $1; echo;
  k=$(( $(grep -c '^noncomputable section' $1) - $(grep -c '^end *$' $1) )); for i in $(seq 1 $k); do echo "end"; done
  echo "end LF2Root_$2"; echo; }
bodyA() { echo "$HDR"; for p in $A; do cat $p; echo; done; echo "end HDec"; }
bodyB() { echo "$HDR"; wrap $B; echo "end HDec"; }
bodyC() { echo "$HDR"; wrap $C; echo "end HDec"; }
bodyD() { echo "$HDR"; wrap $D; echo "end HDec"; }
bodyE() { echo "$HDR"; wrap $E; echo "end HDec"; }
{ echo "import LPrefix"; echo; bodyA; } > olean/TailA.lean
{ echo "import TailA"; echo; bodyB; } > olean/TailB.lean
{ echo "import TailB"; echo; bodyC; } > olean/TailC.lean
{ echo "import TailC"; echo; bodyD; } > olean/TailD.lean
cp ../image-plane/ImagePlaneFinal.lean olean/LF2ImagePlane.lean
cp LF2Stalks.lean.src olean/LF2Stalks.lean
cp LF2UnifRoot.lean.src olean/LF2UnifRoot.lean
cp LF2SmoothDim.lean.src olean/LF2SmoothDim.lean
cp LF2UnramConj.lean.src olean/LF2UnramConj.lean
{ echo "import TailD"; echo "$EIMP"; echo "import LF2ImagePlane"; echo "import LF2Stalks"; echo "import LF2UnifRoot"; echo "import LF2SmoothDim"; echo "import LF2UnramConj"; echo; bodyE; } > olean/TailE.lean
# flat file
NIMP=$(grep -c '^import ' olean/LPrefix.lean)
{ grep '^import ' olean/LPrefix.lean; echo "$EIMP"; echo "$IPIMP" | grep -v -x -F "$(grep '^import ' olean/LPrefix.lean)";
  grep -v '^import ' olean/LPrefix.lean; echo;
  bodyA; bodyB; bodyC; bodyD;
  echo "/-! ## leaf-fold2: the root-namespace modules (image-plane's ImagePlaneFinal.lean verbatim, LF2Stalks, LF2UnifRoot, LF2SmoothDim, LF2UnramConj), each in its own section so that its file-level opens do not leak -/"
  rootbody ../image-plane/ImagePlaneFinal.lean ImagePlane
  rootbody LF2Stalks.lean.src Stalks
  rootbody LF2UnifRoot.lean.src UnifRoot
  rootbody LF2SmoothDim.lean.src SmoothDim
  rootbody LF2UnramConj.lean.src UnramConj
  bodyE; } > Leaves2.lean
wc -l olean/*.lean Leaves2.lean
