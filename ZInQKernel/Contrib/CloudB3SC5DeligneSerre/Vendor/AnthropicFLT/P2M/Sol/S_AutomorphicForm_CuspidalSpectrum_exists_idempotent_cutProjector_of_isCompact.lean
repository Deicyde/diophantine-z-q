/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact (git blob 6c60317b6fca6879fcc3b155ced8d5cfab34e441, sha256 98cfaa6c58e652f75f500f57f01403b70e5ba407ad1eb6d1518c145a304a9df7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F) :
    ∃ P : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      P.comp P = P ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M →
        M.map (P : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) → φ ∈ archCutSubmodule F tys →
        P (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∃ tys' : ArchTypeFamily F, φ ∈ archCutSubmodule F tys') →
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧ φ' ∈ archCutSubmodule F tys ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ ψ ∈ V, rightTranslate F g ψ ∈ V) →
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ ψ ∈ V,
              rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V) →
            φ ∈ V → φ' ∈ V) ∧
          P (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ u ∈ U, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F u) S → S.comp Tc = Tc.comp S) →
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
          (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → S.comp Tc = Tc.comp S) →
        P.comp Tc = Tc.comp P)  := by
  obtain ⟨A, hA0, hA1, hA2, hA3, hA4, hA5⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact F hΦ₀ σ ξ hσ U hU O hO hUO
  obtain ⟨E, hE0, hE1, hE2, hE3, hE4, hE5⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector F hΦ₀ σ ξ hσ tys
  have hUf : U ≤ finiteAdelicGL2Subgroup F := by rw [hUO]; exact inf_le_right

  have hAE : A.comp E = E.comp A :=
    hA4 E fun u hu S hS => (hE5 u (hUf hu) S hS).symm
  refine ⟨E.comp A, ?_, ?_, ?_, ?_, ?_⟩
  ·
    calc (E.comp A).comp (E.comp A) = E.comp ((A.comp E).comp A) := by
          simp only [ContinuousLinearMap.comp_assoc]
      _ = E.comp ((E.comp A).comp A) := by rw [hAE]
      _ = (E.comp E).comp (A.comp A) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = E.comp A := by rw [hE0, hA0]
  ·
    intro M hM
    rintro _ ⟨v, hv, rfl⟩
    exact hE1 M hM ⟨A v, hA1 M hM ⟨v, hv, rfl⟩, rfl⟩
  ·
    intro φ hφ hφU hφt
    show E (A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩
    rw [hA2 φ hφ hφU, hE2 φ hφ hφt]
  ·
    rintro φ hφ ⟨tys', htys'⟩
    obtain ⟨φ₁, hφ₁, hφ₁U, hφ₁t, hφ₁V, hAφ⟩ := hA3 φ hφ
    obtain ⟨φ₂, hφ₂, hφ₂t, hφ₂U, hφ₂V, hEφ⟩ := hE3 φ₁ hφ₁ ⟨tys', hφ₁t tys' htys'⟩
    refine ⟨φ₂, hφ₂, hφ₂U U hUf hφ₁U, hφ₂t, fun V hVf hVa hφV => ?_, ?_⟩
    · exact hφ₂V V hVa (hφ₁V V hVf hφV)
    · show E (A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ₂, hφ₂⟩
      rw [hAφ, hEφ]
  ·
    intro Tc hTU hTK
    calc (E.comp A).comp Tc = E.comp (A.comp Tc) := by simp only [ContinuousLinearMap.comp_assoc]
      _ = E.comp (Tc.comp A) := by rw [hA4 Tc hTU]
      _ = (E.comp Tc).comp A := by simp only [ContinuousLinearMap.comp_assoc]
      _ = (Tc.comp E).comp A := by rw [hE4 Tc hTK]
      _ = Tc.comp (E.comp A) := by simp only [ContinuousLinearMap.comp_assoc]
