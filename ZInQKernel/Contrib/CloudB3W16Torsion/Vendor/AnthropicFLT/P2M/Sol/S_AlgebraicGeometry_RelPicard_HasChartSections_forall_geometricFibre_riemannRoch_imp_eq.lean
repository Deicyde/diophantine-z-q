/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_nonempty_algEquiv_functionField_of_iso
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_HasChartSections_forall_geometricFibre_riemannRoch_imp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicCurve

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} {γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    (hγ : HasChartSections c γ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  intro k _ _ s L _ _ M e he Kc g' hRR
  obtain ⟨L₀, iF, iA, M₀, e₀, he₀, ⟨Kc₀, hRR₀⟩, -⟩ := hγ k s

  have h1 : g' = genusFF k L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
  have h0 : g = genusFF k L₀ := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M₀ hRR₀

  have hφ : (e ≪≫ e₀.symm).hom ≫ M₀.toBase = M.toBase := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he₀, e₀.inv_hom_id_assoc, he]
  obtain ⟨ψ⟩ := AlgebraicCurve.nonempty_algEquiv_functionField_of_iso M.toBase M₀.toBase (e ≪≫ e₀.symm) hφ

  letI := M.functionFieldAlgebra
  letI := M₀.functionFieldAlgebra
  have σ : L ≃ₐ[k] L₀ := (M.ffAlgEquiv.trans ψ).trans M₀.ffAlgEquiv.symm
  rw [h1, h0]
  exact genusFF_eq_of_algEquiv σ
