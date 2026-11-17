module

/- SPDX-License-Identifier: Apache-2.0
See docs/lean-applications/V15Application.LICENSE for the license text. -/

import all ZInQKernel.Contrib.V15TraceQuotient
import Lean.Util.CollectAxioms

/-! Scoped axiom audit of the three V15 application modules and every declaration they contain. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`ZInQKernel.Contrib.V15RetainedContact, `ZInQKernel.Contrib.V15RawRows,
    `ZInQKernel.Contrib.V15TraceQuotient]
  let mut seen : Nat := 0
  let mut checked : Nat := 0
  for idx in [:env.header.modules.size] do
    let owner := env.header.modules[idx]!.module
    if owners.contains owner then
      seen := seen + 1
      for decl in env.header.moduleData[idx]!.constNames do
        let axioms ← collectAxioms decl
        for ax in axioms do
          unless ax == ``propext || ax == ``Quot.sound || ax == ``Classical.choice do
            throwError "Unaccepted axiom {ax} in {owner}:{decl}"
        checked := checked + 1
  unless seen == 3 do
    throwError "Expected three V15 application modules, found {seen}"
  logInfo m!"V15_AXIOM_AUDIT_PASS modules={seen} declarations={checked}"

#print axioms V15RetainedContact.contact_nonzero
#print axioms V15RetainedContact.contact_product_nonzero
#print axioms V15RetainedContact.raw224_q_nonzero
#print axioms V15RetainedContact.raw224_family_q_nonzero
#print axioms V15RetainedContact.raw223_q_nonzero
#print axioms V15RetainedContact.raw223_Q_nonzero
#print axioms V15RetainedContact.row_substitution
#print axioms V15RetainedContact.solutionEquiv

example : (1+(-1 : ℚ))*V15RetainedContact.P5 (((1 : ℚ)-1)^2) =
    (((1 : ℚ)-1)^2)^5 := by norm_num [V15RetainedContact.P5]
