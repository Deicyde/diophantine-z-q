/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous (git blob d5077330ddddcc5092b5dcf592f4b85992e0a176, sha256 52e63f9e4f4cc0eeef5979dc1126dca3a3805825498240022404939a80ff3296).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous

open NumberField

namespace CentralCharFromInvariance

variable (K : Type) [Field K] [NumberField K]

private theorem globalPoints_scalar (u : Kˣ) :
    AutomorphicForm.globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = AutomorphicForm.centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) := by
  apply Units.ext
  change (algebraMap K (AdeleRing (𝓞 K) K)).mapMatrix (Matrix.scalar (Fin 2) (u : K))
      = Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (u : K))
  rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

private theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → _) := by
  have hsc : Continuous fun r : AdeleRing (𝓞 K) K => Matrix.scalar (Fin 2) r := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      exact continuous_id
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact continuous_const
  exact Continuous.units_map (Matrix.scalar (Fin 2) : AdeleRing (𝓞 K) K →+* _).toMonoidHom hsc

end CentralCharFromInvariance

open CentralCharFromInvariance in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    (∀ u : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ := by
  obtain ⟨g₀, hg₀⟩ := hne

  have hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
        = φ (AutomorphicForm.centralScalar (𝓞 K) K z * g₀) * (φ g₀)⁻¹ := by
    intro z
    have h := hφ.central_transform ⟨z, Subgroup.mem_top z⟩ g₀
    change φ (AutomorphicForm.centralScalar (𝓞 K) K z * g₀)
        = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g₀ at h
    rw [h, mul_inv_cancel_right₀ hg₀]
  refine ⟨fun u => ?_, ?_⟩
  ·
    have h1 := hφ.left_invariant (Matrix.GeneralLinearGroup.scalar (Fin 2) u) g₀
    rw [globalPoints_scalar] at h1
    have h2 := hχ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u)
    rw [h1, mul_inv_cancel₀ hg₀] at h2
    exact Units.val_eq_one.mp h2
  ·
    have hF : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      simp_rw [hχ]
      exact ((hcont.comp ((continuous_centralScalar K).mul continuous_const)).mul continuous_const)
    refine Units.continuous_iff.2 ⟨hF, ?_⟩
    have hinv : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (((χ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ) = ((χ ⟨z⁻¹, Subgroup.mem_top z⁻¹⟩ : ℂˣ) : ℂ) := by
      intro z
      rw [← map_inv]
      rfl
    simp_rw [hinv]
    exact hF.comp continuous_inv
