/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_peterssonOn_add_smul_conj (git blob 0ee7d34e4f7803100cefcfba65cc5823acafd869, sha256 3587078ce7b0a144eb6e21923e5f18767c991eaf76c1e4b918534ae851d73cbb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PeterssonOn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP
end P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP

namespace P2MW.S_CuspForm_peterssonOn_add_smul_conj

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace PetOnIP

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}



scoped instance sl2zContinuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

scoped instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def cosum (Φ : ℍ → ℂ) (x : ℍ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Φ ((q.out⁻¹ : SL(2, ℤ)) • x)

theorem integrand_eq (F G : ℍ → ℂ) :
    CuspForm.peterssonOnIntegrand Γ k F G = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) := by
  funext x
  unfold CuspForm.peterssonOnIntegrand cosum
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_slash_SL k F G _ x

theorem petersson_add_right (F G H : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (G + H) x
      = UpperHalfPlane.petersson k F G x + UpperHalfPlane.petersson k F H x := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply]; ring

theorem petersson_smul_right (F G : ℍ → ℂ) (c : ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F (c • G) x = c * UpperHalfPlane.petersson k F G x := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem cosum_add (Φ Ψ : ℍ → ℂ) : cosum (Γ := Γ) (Φ + Ψ) = cosum (Γ := Γ) Φ + cosum (Γ := Γ) Ψ := by
  funext x; simp [cosum, Finset.sum_add_distrib]

theorem cosum_const_mul (c : ℂ) (Φ : ℍ → ℂ) :
    cosum (Γ := Γ) (fun x => c * Φ x) = fun x => c * cosum (Γ := Γ) Φ x := by
  funext x; simp [cosum, Finset.mul_sum]

theorem measurable_smul_SL (γ : SL(2, ℤ)) : Measurable (fun x : ℍ => γ • x) :=
  (continuous_const_smul γ).measurable

theorem continuous_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) : Continuous (cosum (Γ := Γ) Φ) :=
  continuous_finsetSum _ fun _ _ => hΦ.comp (continuous_const_smul _)

theorem integrable_cosum {Φ : ℍ → ℂ} (hΦ : Continuous Φ) (hbd : ∃ C, ∀ x, ‖Φ x‖ ≤ C) :
    Integrable (cosum (Γ := Γ) Φ) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := hbd
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_cosum hΦ).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hC _)

theorem petersson_bounded (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ∃ C, ∀ x, ‖UpperHalfPlane.petersson k ⇑f ⇑g x‖ ≤ C :=
  CuspFormClass.petersson_bounded_left k ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) f g

omit [Γ.FiniteIndex] in
theorem petersson_continuous' (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) : Continuous (UpperHalfPlane.petersson k ⇑f ⇑g) :=
  UpperHalfPlane.petersson_continuous k (CuspFormClass.holo f).continuous (CuspFormClass.holo g).continuous

theorem integrable_integrand (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    Integrable (CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g) (volume.restrict (𝒟 : Set ℍ)) := by
  rw [integrand_eq]
  exact integrable_cosum (petersson_continuous' f g) (petersson_bounded f g)

theorem peterssonOn_add_right (f g h : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, CuspForm.peterssonOn_def,
    ← integral_add (integrable_integrand f g) (integrable_integrand f h)]
  congr 1
  rw [integrand_eq, integrand_eq, integrand_eq]
  change _ = cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g) + cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑h)
  rw [← cosum_add]
  congr 1
  funext x
  exact petersson_add_right _ _ _ x

theorem peterssonOn_smul_right (c : ℂ) (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, ← integral_const_mul]
  congr 1
  rw [integrand_eq, integrand_eq]
  change _ = fun x => c * cosum (Γ := Γ) (UpperHalfPlane.petersson k ⇑f ⇑g) x
  rw [← cosum_const_mul]
  congr 1
  funext x
  exact petersson_smul_right _ _ c x

theorem cosum_conj (F G : ℍ → ℂ) (x : ℍ) :
    conj (cosum (Γ := Γ) (UpperHalfPlane.petersson k G F) x)
      = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) x := by
  unfold cosum
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [UpperHalfPlane.petersson_symm k F G, Complex.conj_conj]

theorem integrand_conj (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (x : ℍ) :
    conj (CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f x) = CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑g x := by
  rw [integrand_eq, integrand_eq]
  exact cosum_conj ⇑f ⇑g x

theorem peterssonOn_conj_symm (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    conj (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g := by
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def]
  have h := integral_conj (μ := volume.restrict (𝒟 : Set ℍ)) (𝕜 := ℂ)
    (f := CuspForm.peterssonOnIntegrand Γ k ⇑g ⇑f)
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => integrand_conj f g x)

end PetOnIP
open scoped _root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP

end
open scoped _root_.P2MW.S_CuspForm_peterssonOn_add_smul_conj.PetOnIP

open scoped MatrixGroups in
theorem solution (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) :
    CuspForm.peterssonOn Γ k f (g + h) = CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h ∧
    CuspForm.peterssonOn Γ k f (c • g) = c * CuspForm.peterssonOn Γ k f g ∧
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g :=
  ⟨PetOnIP.peterssonOn_add_right f g h, PetOnIP.peterssonOn_smul_right c f g,
    PetOnIP.peterssonOn_conj_symm f g⟩
