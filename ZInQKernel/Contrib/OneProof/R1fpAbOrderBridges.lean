import ZInQKernel.Contrib.HDecomp.QM.Structures
import ZInQKernel.Contrib.CloudB4W28FineModuli.MaximalOrder
import ZInQKernel.Contrib.CloudB4W28FineModuli.Ramification

/-!
# R1fpAb: proved order prerequisites, not a fine-moduli witness

The intended witness is the unchanged `LeafQM.AV.R1UnivRigid.R1fpAb` defined
in `TailZ16` at `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`.
This file imports the actual defining order module for the proved prerequisites,
but does NOT claim the existential witness. The bounded FLT fine-moduli port
encountered broad Mathlib drift, so this contribution supplies only the exact
order and ramification bridges. Full-Main discharge checking is separate from
these closed arithmetic statements.

No part of the other clauses of Baba–Granath, González–Rotger, Elkies,
Deligne components, or Shimura reciprocity is assumed or proved here.
The helper/vendor directory preserves the upstream source and license notices.
-/

namespace ZInQ.Contrib.CloudB4W28

/-- The maximal-order prerequisite, on the original project order's literal carrier. -/
theorem r1fpAb_maximalOrder_bridge : QuaternionAlgebra.IsMaximalOrder orderLattice :=
  isMaximalOrder_orderLattice

/-- The indefinite and exactly-at-2,3 ramification prerequisite, with no extra hypotheses. -/
theorem r1fpAb_ramification_bridge :
    QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3 : ℚ) 2 3 :=
  isIndefiniteRamifiedExactlyAt_two_neg_three

/-- Both prerequisites, without supplying or assuming the missing moduli witness. -/
theorem r1fpAb_order_bridges :
    QuaternionAlgebra.IsMaximalOrder orderLattice ∧
      QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3 : ℚ) 2 3 :=
  ⟨r1fpAb_maximalOrder_bridge, r1fpAb_ramification_bridge⟩

end ZInQ.Contrib.CloudB4W28
