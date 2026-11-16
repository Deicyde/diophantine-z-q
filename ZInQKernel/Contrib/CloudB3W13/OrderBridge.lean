/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.OrderMaximal
import ZInQKernel.Contrib.CloudB3W13.OrderRamification

/-!
# W13 order bridge: the kernel's QM order in the form the Anthropic-FLT fine-moduli theorems take

`CerednikDrinfeld.QM.exists_isFineModuli_of_isUnit_two_of_isUnit_three` (and its companions)
take `hB : IsIndefiniteRamifiedExactlyAt a b q q'` and `hΛ : IsMaximalOrder Λ` for
`Λ : Submodule ℤ ℍ[ℚ, a, b]`. With `a = 2`, `b = -3`, `q = 2`, `q' = 3` and `Λ = oLattice`
(the kernel's `LeafQM.O`), both inputs are proved here.
-/

open scoped Quaternion

namespace ZInQ.Contrib.CloudB2Shimura

/-- **Order bridge.** -/
theorem order_bridge :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3) 2 3 ∧
      ZInQ.Contrib.CloudW03NeronSurj.FLT.QuaternionAlgebra.IsMaximalOrder oLattice ∧
      (∀ x : ℍ[ℚ, 2, -3], x ∈ oLattice ↔ x ∈ LeafQM.O) :=
  ⟨isIndefiniteRamifiedExactlyAt_two_negThree, oLattice_isMaximalOrder, fun _ => Iff.rfl⟩

end ZInQ.Contrib.CloudB2Shimura

#print axioms ZInQ.Contrib.CloudB2Shimura.order_bridge
