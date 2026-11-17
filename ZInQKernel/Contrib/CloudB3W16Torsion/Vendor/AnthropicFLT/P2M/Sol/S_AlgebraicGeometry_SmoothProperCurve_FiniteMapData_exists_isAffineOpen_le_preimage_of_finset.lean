/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_hom_proj_preimage_basicOpen_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_isAffineOpen_le_preimage_of_finset

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (V : (Spec (CommRingCat.of R)).affineOpens) (F : Finset C)
    (hF : ∀ x ∈ F, c x ∈ (V : (Spec (CommRingCat.of R)).Opens)) :
    ∃ U : C.Opens, IsAffineOpen U ∧ U ≤ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨π, h0, h1, -, -, -⟩ := 𝔉.exists_hom_proj_preimage_basicOpen_eq

  have hX : ∀ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) R) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) R 1 :=
    fun i => ProjSpace.X_mem_one R 1 i
  have hcovP : (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _ (ProjSpace.irrelevant_le_span_X R 1)
  haveI : IsAffineHom π := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun y => ?_
    have hy : y ∈ (⨆ i : Fin 2, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R) (MvPolynomial.X i)) := by
      rw [hcovP]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ (hX i) one_pos, ?_⟩
    fin_cases i
    · simpa [h0] using 𝔉.isAffineOpen_U
    · simpa [h1] using 𝔉.isAffineOpen_V

  obtain ⟨W, hW, hFW⟩ := AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj (MvPolynomial.homogeneousSubmodule (Fin 2) R) π F

  haveI : IsAffine W := hW
  refine ⟨W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)), ?_, ?_, ?_⟩
  · exact (V.2.preimage (W.ι ≫ c)).image_of_isOpenImmersion W.ι
  · have : W.ι ''ᵁ ((W.ι ≫ c) ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens)) =
        W ⊓ c ⁻¹ᵁ (V : (Spec (CommRingCat.of R)).Opens) := by
      rw [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    rw [this]; exact inf_le_right
  · intro x hx
    refine ⟨⟨x, hFW x hx⟩, ?_, rfl⟩
    show c (W.ι ⟨x, hFW x hx⟩) ∈ (V : (Spec (CommRingCat.of R)).Opens)
    simpa using hF x hx
