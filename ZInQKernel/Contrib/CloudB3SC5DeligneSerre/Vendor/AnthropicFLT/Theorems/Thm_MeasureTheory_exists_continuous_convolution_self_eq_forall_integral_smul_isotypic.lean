/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic (git blob 119a48dffa2796b9f99d39d527950aa887ebaca3, sha256 24ca9d8d16d3212af172dfadfebf4a3daf421c68f211bcfc59c9407d7fa33014).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

theorem MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ e : K → ℂ, Continuous e ∧ (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : K →* (H →L[ℂ] H)), (∀ (k : K) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : K => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) := by
  revert K μ n ρ hρ
  exact @_root_.P2MW.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic.solution
