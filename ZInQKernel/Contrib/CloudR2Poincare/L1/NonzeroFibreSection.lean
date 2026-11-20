import ZInQKernel.Contrib.CloudR2Poincare.L1.OriginalCechKernel
import ZInQKernel.Contrib.CloudR2Poincare.L1.IsomorphismNeighborhood
import ZInQKernel.Contrib.CloudR2Poincare.L2.LineBundleNonzero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.HomSection

/-! Lift a nonzero residue-fibre section through the ACTUAL coefficient map,
prove the ACTUAL fibre morphism invertible, and remove its proper zero image.
This proves local seesaw without choosing an arbitrary cohomology isomorphism
or assuming any positive-degree vanishing. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Surjectivity of the actual tensor coefficient map forces some original
section to have nonzero actual pullback whenever the target section module
is nontrivial. -/
theorem exists_nonzero_pullbackSection_of_surjective_coefficientMap
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [Algebra Γ(Y, ⊤) Γ(Y', ⊤)] (hg : algebraMap Γ(Y, ⊤) Γ(Y', ⊤) = g.appTop.hom)
    [Nontrivial (Scheme.Modules.sectionsModule f' ((Scheme.Modules.pullback g').obj M) (g' ⁻¹ᵁ ⊤))]
    (hsur : Function.Surjective (Scheme.Modules.sectionsModuleBaseChange square M hg ⊤)) :
    ∃ s : Γ(M, ⊤), Scheme.Modules.pullbackSection g' s ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have hz (v : Γ(Y', ⊤) ⊗[Γ(Y, ⊤)] Scheme.Modules.sectionsModule f M ⊤) :
      Scheme.Modules.sectionsModuleBaseChange square M hg ⊤ v = 0 := by
    induction v using TensorProduct.induction_on with
    | zero => exact map_zero _
    | tmul b s =>
        rw [Scheme.Modules.sectionsModuleBaseChange_tmul,
          Scheme.Modules.pullbackSectionAddHom_apply, hn, smul_zero]
    | add v w hv hw => rw [map_add, hv, hw, add_zero]
  obtain ⟨t, ht⟩ := exists_ne (0 : Scheme.Modules.sectionsModule f'
    ((Scheme.Modules.pullback g').obj M) (g' ⁻¹ᵁ ⊤))
  obtain ⟨v, hv⟩ := hsur t
  exact ht (hv.symm.trans (hz v))

/-- A nonzero ACTUAL morphism between trivial line bundles over a proper
integral field-scheme is invertible. The scalar-isomorphism supplier is L2's
certified theorem; this lemma identifies the ACTUAL morphism, not merely the objects. -/
theorem isIso_nonzero_morphism_of_trivial_lines
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    [IsProper p] [IsIntegral X] {M N : X.Modules} (φ : M ⟶ N)
    (eM : M ≅ Scheme.Modules.unit X) (eN : N ≅ Scheme.Modules.unit X) (hφ : φ ≠ 0) :
    IsIso φ := by
  let ψ : Scheme.Modules.unit X ⟶ Scheme.Modules.unit X := eM.inv ≫ φ ≫ eN.hom
  have hback : eM.hom ≫ ψ ≫ eN.inv = φ := by simp [ψ]
  have hψ : ψ ≠ 0 := by
    intro h
    apply hφ
    rw [← hback, h, zero_comp, comp_zero]
  obtain ⟨c, hc⟩ := Scheme.Modules.exists_eq_smulHom (Scheme.Modules.unit X) ψ
  have hc0 : c ≠ 0 := by
    intro h
    apply hψ
    rw [hc, h, Scheme.Modules.smulHom_zero]
  letI : Field Γ(X, ⊤) := (isField_of_universallyClosed K p).toField
  haveI : IsIso ψ := by
    rw [hc]
    exact ZInQ.Contrib.CloudR2Poincare.L2.isIso_smulHom_of_isUnit
      (Scheme.Modules.unit X) c (isUnit_iff_ne_zero.mpr hc0)
  rw [← hback]
  infer_instance

/-- Strong affine local seesaw: residue-fibre triviality alone supplies an
ACTUAL local isomorphism to the structure sheaf near each base point. -/
theorem exists_open_iso_unit_of_trivial_residue_fibres_affine
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hFibres : ∀ y : Spec (.of R), Scheme.Pic.map
      (f.fiberι y) (Scheme.Pic.mk M) = 1)
    (y : Spec (.of R)) :
    ∃ V : (Spec (.of R)).Opens, y ∈ V ∧
      Nonempty ((Scheme.Modules.pullback ((f ⁻¹ᵁ V).ι)).obj M ≅
        Scheme.Modules.unit (f ⁻¹ᵁ V).toScheme) := by
  classical
  let Y := Spec (.of R)
  let p := Y.fromSpecResidueField y
  let px := pullback.fst f p
  let pf := pullback.snd f p
  let M' := (Scheme.Modules.pullback px).obj M
  haveI : IsIntegral (pullback f p) := GeometricallyIntegral.isIntegral_of_subsingleton pf
  have hm : Scheme.Pic.mk M' = 1 := by
    rw [← Scheme.Pic.map_mk]
    exact hFibres y
  obtain ⟨eM'⟩ : Nonempty (M' ≅ Scheme.Modules.unit (pullback f p)) := by
    rw [Scheme.Pic.one_eq_mk_unit] at hm
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mp hm
  haveI : Nontrivial Γ(Scheme.Modules.unit (pullback f p), ⊤) :=
    inferInstanceAs (Nontrivial Γ(pullback f p, ⊤))
  haveI : Nontrivial Γ(M', ⊤) := (Scheme.Modules.appLinearEquivOfIso eM' ⊤).toEquiv.nontrivial
  haveI : Nontrivial (Scheme.Modules.sectionsModule pf M' ⊤) :=
    inferInstanceAs (Nontrivial Γ(M', ⊤))
  let top := Scheme.Modules.sectionsModuleEqLinearEquiv (p := pf) M' px.preimage_top.symm
  haveI : Nontrivial (Scheme.Modules.sectionsModule pf M' (px ⁻¹ᵁ ⊤)) := top.toEquiv.nontrivial
  letI : Algebra Γ(Y, ⊤) Γ(Spec (Y.residueField y), ⊤) := p.appTop.hom.toAlgebra
  have hb := bijective_canonicalResidueSectionsBaseChange R f M hFibres y
  obtain ⟨s, hs⟩ := exists_nonzero_pullbackSection_of_surjective_coefficientMap
    (IsPullback.of_hasPullback f p) M rfl hb.2
  let φ : Scheme.Modules.unit X ⟶ M := Scheme.Modules.homOfGlobalSection M s
  have hφ : (Scheme.Modules.pullback px).map φ ≠ 0 := by
    intro h
    apply hs
    have hsection := Scheme.Modules.pullbackSection_app_one px φ
    rw [Scheme.Modules.homOfGlobalSection_app_top_one] at hsection
    rw [h, comp_zero, Scheme.Modules.Hom.zero_app] at hsection
    change Scheme.Modules.pullbackSection px s = 0 at hsection
    exact hsection
  have hi : IsIso ((Scheme.Modules.pullback px).map φ) :=
    isIso_nonzero_morphism_of_trivial_lines pf ((Scheme.Modules.pullback px).map φ)
      (Scheme.Modules.pullbackObjUnitIso px) eM' hφ
  obtain ⟨V, hyV, hV⟩ := exists_open_isIso_of_residue_fibre_isIso f φ y hi
  haveI := hV
  exact ⟨V, hyV, ⟨(asIso ((Scheme.Modules.pullback ((f ⁻¹ᵁ V).ι)).map φ)).symm ≪≫
    Scheme.Modules.pullbackObjUnitIso ((f ⁻¹ᵁ V).ι)⟩⟩

end ZInQ.Contrib.CloudR2Poincare.L1
