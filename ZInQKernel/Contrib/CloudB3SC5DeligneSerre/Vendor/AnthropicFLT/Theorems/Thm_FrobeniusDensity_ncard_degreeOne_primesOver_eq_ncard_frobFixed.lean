/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed (git blob 6d06048ac1e678f4fefad33a1791f780b127d74a, sha256 27bb797b0374d9b201367b4d8fdac46f515256e860732f2aa80e5c575f0c7374).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Fixed
import Mathlib.GroupTheory.GroupAction.Quotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField Ideal
theorem FrobeniusDensity.ncard_degreeOne_primesOver_eq_ncard_frobFixed
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
  revert L H E ℓ hℓ Q₀ hinertia
  exact @_root_.P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_eq_ncard_frobFixed.solution
