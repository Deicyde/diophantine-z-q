module

import all ZInQKernel.Contrib.SqrtTwoDuplicationCancellation
import Lean.Util.CollectAxioms

/-! Axiom audit for the standalone contribution, outside the accepted snapshot. -/

#print axioms ZInQ.ModelDuplicationCancellation.primitive_duplication_local

open Lean Elab Command in
run_cmd do
  let name := ``ZInQ.ModelDuplicationCancellation.primitive_duplication_local
  let axioms ← collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
      throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"DUPLICATION_AXIOM_AUDIT_PASS {name}: {axioms.toList}"
