/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_ncard_degreeOne_primesOver_under (git blob 80efd322c4f743eb02c865252ae2c1cb5ce0ae36, sha256 41754307a677b16d12e58f789bb0169ae976b2a8f056e6a5751bffdac61e080d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.Fixed
import Mathlib.GroupTheory.GroupAction.Quotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_ncard_degreeOne_primesOver_under

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField Ideal
open scoped Pointwise
attribute [local instance 1001] NumberField.RingOfIntegers.instMulSemiringAction
theorem FrobeniusDensity.ncard_degreeOne_primesOver_under
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {H : Subgroup (L ≃ₐ[ℚ] L)} {E : IntermediateField ℚ L} [IsGaloisGroup H E L]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime]
    [Q₀.LiesOver (FrobeniusDensity.ratPrimeIdeal ℓ)] (hinertia : Q₀.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    {𝔮 ∈ (FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (𝓞 E) |
      Nat.card ((𝓞 E) ⧸ 𝔮) = ℓ}.ncard
      = {x : (L ≃ₐ[ℚ] L) ⧸ H |
          ∀ d ∈ MulAction.stabilizer (L ≃ₐ[ℚ] L) Q₀, d • x = x}.ncard := by
  revert L H E ℓ hℓ Q₀ hinertia
  exact @_root_.P2MW.S_FrobeniusDensity_ncard_degreeOne_primesOver_under.solution
