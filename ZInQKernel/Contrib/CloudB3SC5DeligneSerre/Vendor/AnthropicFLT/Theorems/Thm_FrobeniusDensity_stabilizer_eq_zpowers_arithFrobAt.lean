/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt (git blob fd3b6a05d5b469dbbcaadbc6388d7d6a7b8e510d, sha256 9022810acc27c22cddd3d4fab9b4816aef46b7de77902c75521469220d0abf3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.GroupTheory.GroupAction.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField Ideal
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction
theorem FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    MulAction.stabilizer (L ≃ₐ[ℚ] L) Q
      = Subgroup.zpowers (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q) := by
  revert L ℓ hℓ Q hinertia
  exact @_root_.P2MW.S_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt.solution
