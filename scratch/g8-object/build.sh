#!/bin/bash
# Assemble G8Object.lean (one environment for the whole check):
#  imports (union of the sources' imports) +
#  scratch/g0-mod-field/ModField.lean L16-1036 verbatim, inside `section ModFieldCopy` (so that its
#    file-level `open`s do not leak) +
#  scratch/g14-trace/part_bridge.lean verbatim (G14Bridge: TateBridge35), with ModField's opens +
#  scratch/g14-trace/G14Trace.lean L10-end verbatim (C9, E1 copies, g0-mod-newform's part_new,
#    g14-trace's part_g14) +
#  scratch/g15-ram/G15Ram.lean: `namespace G0Galois` block and §1-§3, verbatim (as g15-ram's
#    build_tail.sh) +
#  scratch/g0-mod-galois/part_galois.lean L27-152 and part_matrix.lean L11-21 verbatim +
#  part_obj.lean +
#  scratch/g0-assemble/parts/87_afterg7.lean L27-123 verbatim (ModelG3G6, LocalRamWild, G15RamWild,
#    g15RamG_of_wild, LinkedTateData), with ModField's file-level `open`s re-issued inside +
#  part_ltcopy.lean (linked-tate's RhoRamWild, LinkedTateCore, LinkedTateCoreDR at dae5b706) +
#  part_link.lean.
cd "$(dirname "$0")"
{
  { sed -n '1,8p' ../g14-trace/G14Trace.lean; sed -n '1,15p' ../g0-mod-field/ModField.lean;
    sed -n '1,7p' ../g15-ram/G15Ram.lean;
    echo "import ZInQKernel.HDecomp.Descent.ProjRep"; echo "import ZInQKernel.HDecomp.I3Linalg.C2"; } \
    | awk '!seen[$0]++'
  echo
  echo "/-! Copied verbatim from scratch/g0-mod-field/ModField.lean L16-1036. -/"
  echo "section ModFieldCopy"
  sed -n '16,1036p' ../g0-mod-field/ModField.lean
  echo "end ModFieldCopy"
  echo
  echo "/-! Copied verbatim from scratch/g14-trace/part_bridge.lean (without its #print axioms), inside a"
  echo "section re-issuing ModField's file-level opens (active where g14-trace appended it). -/"
  echo "section G14BridgeCopy"
  echo "open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj"
  echo "open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q"
  sed -n '/^\/-!/,/^end G14Bridge/p' ../g14-trace/part_bridge.lean
  echo "end"
  echo "end G14BridgeCopy"
  echo
  echo "/-! Copied verbatim from scratch/g14-trace/G14Trace.lean L10-end. -/"
  sed -n '10,$p' ../g14-trace/G14Trace.lean
  echo
  echo "/-! Copied verbatim from scratch/g15-ram/G15Ram.lean (G0Galois block, §1-§3). -/"
  echo "noncomputable section"
  sed -n '/^namespace G0Galois/,/^end G0Galois/p' ../g15-ram/G15Ram.lean
  sed -n '/^\/-! ## §1. The smaller named Props/,/^end G15Ram/p' ../g15-ram/G15Ram.lean
  echo "end"
  echo
  echo "/-! Copied verbatim from scratch/g0-mod-galois/part_galois.lean L27-152 and part_matrix.lean L11-21. -/"
  echo "noncomputable section"
  sed -n '27,152p' ../g0-mod-galois/part_galois.lean
  echo
  sed -n '11,21p' ../g0-mod-galois/part_matrix.lean
  echo
  echo "end G0Galois"
  echo "end"
  cat part_obj.lean
  echo
  echo "/-! Copied verbatim from scratch/g0-assemble/parts/87_afterg7.lean L27-123 (the first \`open\`"
  echo "line re-issues ModField's file-level opens, which were active there). -/"
  echo "section G0AssembleAfterG7Sec"
  echo "open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q"
  sed -n '27,123p' ../g0-assemble/parts/87_afterg7.lean
  echo "end HSyn.G0AssembleMod"
  echo "end G0AssembleAfterG7Sec"
  cat part_ltcopy.lean
  cat part_link.lean
} > G8Object.lean
