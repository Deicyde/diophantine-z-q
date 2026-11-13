#!/bin/bash
# LtLocal.lean =
#   imports of scratch/lg-kerwild/KerWild.lean + three Mathlib imports (cardinality, Classification)
# + scratch/lg-kerwild/KerWild.lean body, verbatim minus its imports and `#print axioms` lines
#   (itself verbatim copies of local-glue, frob-trace (g0-mod-field, unram-tate, g14-trace),
#   g0-dim, plus lg-kerwild's own parts)
# + part_tools.lean (new + two lemmas copied from g8-tate)
# + part_g7.lean (new + `T_prime` copied from g8-tate)
# + part_copy.lean (verbatim copies from scratch/g0-assemble2/G0Assemble2.lean, incl. LinkedTateLocal)
# + part_main.lean (new: LinkedTateLocalD, ModelEndRank4, G7DegreeBound, main theorem)
# + part_rank.lean (verbatim copies from scratch/linked-tate/LinkedTate.lean + new)
# + part_axioms.lean (#print axioms of the new theorems)
cd "$(dirname "$0")"
KW=../lg-kerwild/KerWild.lean
{
  grep '^import' $KW
  echo 'import Mathlib.Analysis.Complex.Cardinality'
  echo 'import Mathlib.Topology.Algebra.Module.Cardinality'
  echo 'import Mathlib.FieldTheory.IsAlgClosed.Classification'
  echo
  echo "-- BEGIN verbatim body of scratch/lg-kerwild/KerWild.lean (minus imports, #print axioms)"
  grep -v '^import' $KW | grep -v '^#print axioms'
  echo "-- END verbatim body of scratch/lg-kerwild/KerWild.lean"
  echo
  for f in part_tools part_g7 part_copy part_main part_rank; do cat $f.lean; echo; done
  cat part_axioms.lean
} > LtLocal.lean
