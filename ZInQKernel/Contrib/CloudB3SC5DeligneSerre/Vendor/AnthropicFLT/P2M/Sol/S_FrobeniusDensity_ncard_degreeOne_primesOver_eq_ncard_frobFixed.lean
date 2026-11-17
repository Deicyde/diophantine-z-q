/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed (git blob 0d724e06c62b14c4156ab525f62ea18192d4cce7, sha256 e60ba948bd6bab33860369881643eba44a1320253d5aead83dc38d74ee456d48).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_stabilizer_eq_zpowers_arithFrobAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_ncard_degreeOne_primesOver_under
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Fixed
import Mathlib.GroupTheory.GroupAction.Quotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace NumberField
end NumberField
namespace Ideal
end Ideal
namespace NumberField.Ideal
end NumberField.Ideal

namespace P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed

set_option autoImplicit false

open _root_.NumberField
open _root_.Ideal
open _root_.NumberField.Ideal
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction

private theorem forall_mem_zpowers_smul_eq_iff {G α : Type*} [Group G] [MulAction G α]
    (σ : G) (x : α) :
    (∀ d ∈ Subgroup.zpowers σ, d • x = x) ↔ σ • x = x := by
  constructor
  · exact fun h ↦ h σ (Subgroup.mem_zpowers σ)
  · intro h d hd
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer G x := Subgroup.zpowers_le.mpr h
    exact this hd

theorem solution
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    haveI : Finite ((𝓞 L) ⧸ Q₀) :=
      FrobeniusDensity.finite_quotient_of_ne_bot
        (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H | arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q₀ • x = x}.ncard := by
  haveI : Finite ((𝓞 L) ⧸ Q₀) :=
    FrobeniusDensity.finite_quotient_of_ne_bot
      (FrobeniusDensity.ne_bot_of_liesOver_ratPrimeIdeal hℓ)
  rw [FrobeniusDensity.ncard_degreeOne_primesOver_under (H := H) (E := E) hℓ Q₀ hinertia]
  congr 1
  ext x
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
    FrobeniusDensity.stabilizer_eq_zpowers_arithFrobAt hℓ Q₀ hinertia,
    forall_mem_zpowers_smul_eq_iff]
