/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound (git blob 6c79882ec2d23fd146433574b5f1b5415cfd94c7, sha256 8a77933658c83270f01d5de6b548dd95a7ce0740a914b52c80034717a0a5a3dc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal

open scoped Classical in

theorem NumberField.exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (Y : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact Y →
      ∃ U' : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U' ∧
        ∀ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (σ₁ σ₂ c' : ℝ) (N : ℕ), 0 < c' →
          ∃ Nd : ℕ, ∀ c : ℝ, ∃ M : ℝ,
            ∀ (G : {ξ : F // ξ ≠ 0} → (AdeleRing (𝓞 F) F)ˣ → ℝ) (σ : ℝ), σ₁ ≤ σ → σ ≤ σ₂ →
              (∀ ξ y, 0 ≤ G ξ y) →
              (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (y : (AdeleRing (𝓞 F) F)ˣ),
                G ξ (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
                  = G ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ y) →
              (∀ u ∈ U', ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → G ξ (z * u) = 0) ∧
                  G ξ (z * u) ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - σ)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(Nd : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * Nd : ℝ))) →
              ∀ (y₁ y₀ : (AdeleRing (𝓞 F) F)ˣ), y₀ ∈ Y → c' ≤ ((α y₁ : ℝˣ) : ℝ) →
                Summable (fun ξ : {ξ : F // ξ ≠ 0} => G ξ (y₁ * y₀)) ∧
                ∑' ξ : {ξ : F // ξ ≠ 0}, G ξ (y₁ * y₀) ≤ M * ((α y₁ : ℝˣ) : ℝ) ^ (-(N : ℝ)) := by
  revert F
  exact @_root_.P2MW.S_NumberField_exists_isCompact_forall_tsum_le_mul_rpow_neg_of_principal_equivariant_of_dilation_bound.solution
