/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_poleDivisor_of_transcendental (git blob da6a1c15e3f6889deaa5fe9cac975e01b3eebac1, sha256 9e0449655bb7dc06422deaf78fe35bf297956adb35ccddedf56d6b7ce05f5408).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_poleDivisor_of_transcendental

set_option autoImplicit false

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (-v.ord x) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) x hx0
  refine ⟨(-P) ⊔ 0, fun v => ?_⟩
  show max ((-P) v) ((0 : Divisor K F) v) = max 0 (-v.ord x)
  rw [Finsupp.neg_apply, hP v, Finsupp.coe_zero, Pi.zero_apply, max_comm]
