#!/bin/bash
# LtLocal4.lean (GluePieces4 variant) = LtLocal.lean's construction with Base4 in place of the
# verbatim KerWild body: Base.lean (= scratch/lg-kerwild/KerWild.lean minus `#print axioms`) with
# g0-assemble3's `G7Data` fix ported by mk_base4.py; then parts 1-5, their axiom lines, and
# part_gp4.lean (LinkedTateLocal itself over the fixed G7Data).
cd "$(dirname "$0")"
grep -v '^#print axioms' ../lg-kerwild/KerWild.lean > Base.lean
python3 mk_base4.py || exit 1
{
  grep '^import' Base4.lean
  echo 'import Mathlib.Analysis.Complex.Cardinality'
  echo 'import Mathlib.Topology.Algebra.Module.Cardinality'
  echo 'import Mathlib.FieldTheory.IsAlgClosed.Classification'
  echo
  echo "-- BEGIN scratch/lg-kerwild/KerWild.lean body with g0-assemble3's G7Data fix (mk_base4.py)"
  grep -v '^import' Base4.lean
  echo "-- END"
  echo
  for f in part_tools part_g7 part_copy part_main part_rank; do cat $f.lean; echo; done
  cat part_axioms.lean
  echo
  cat part_gp4.lean
} > LtLocal4.lean
