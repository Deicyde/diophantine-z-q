import ZInQKernel.Contrib.CloudR2Poincare.L1.ScalarFreeMatrix

/-!
# Canonical scalar kernels of fieldwise constant-rank matrices over a reduced ring

The actual field map factors through a flat affine neighborhood on which the
matrix kernel is explicitly split. This is the genuine ring-side specialization
needed to apply the retained universally quasi-isomorphic Čech model.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The canonical scalar-extension kernel map is invertible for a fieldwise
constant-rank matrix over a reduced ring. All maps are the actual kernel comparisons. -/
theorem isIso_matrix_kernelComparison_of_constant_fieldRank
    (R : Type u) [CommRing R] [_root_.IsReduced R]
    {m n : Type u} [Fintype m] [Fintype n]
    (A : Matrix m n R) (ρ : ℕ)
    (hρ : ∀ (K : Type u) [Field K] (ψ : R →+* K), (A.map ψ).rank = ρ)
    (K : Type u) [Field K] (ψ : R →+* K) :
    IsIso (kernelComparison (ModuleCat.ofHom A.mulVecLin) (ModuleCat.extendScalars ψ)) := by
  classical
  let Y := Spec (CommRingCat.of R)
  let er : R →+* Γ(Y, ⊤) := (Scheme.ΓSpecIso (.of R)).inv.hom
  let AΓ := A.map er
  have hr : ∀ y : Y, (AΓ.map (Y.fromSpecResidueField y).appTop).rank = ρ := by
    intro y
    letI : Field Γ(Spec (Y.residueField y), ⊤) :=
      (Scheme.Modules.isField_Γ_Spec_residueField y).toField
    have h := hρ Γ(Spec (Y.residueField y), ⊤)
      ((Y.fromSpecResidueField y).appTop.hom.comp er)
    change (A.map ((Y.fromSpecResidueField y).appTop.hom.comp er)).rank = ρ
    exact h
  let g : Spec (.of K) ⟶ Y := Spec.map (CommRingCat.ofHom ψ)
  obtain ⟨x⟩ : Nonempty (Spec (.of K)) := inferInstance
  let y : Y := g x
  obtain ⟨W, hyW, split⟩ := exists_opens_split_kernel_of_constant_residueRank
    (a := ULift.{u} (Fin 0)) AΓ ρ hr y
  obtain ⟨V₀, hV₀, hyV₀, hV₀W⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens) hyW
  let V : Y.Opens := V₀
  have hV : IsAffineOpen V := hV₀
  have hyV : y ∈ V := hyV₀
  have hVW : V ≤ W := hV₀W
  letI : IsAffine V.toScheme := hV
  have hgRange : Set.range g ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro z ⟨z', rfl⟩
    have heq : g z' = y := congrArg g (Subsingleton.elim z' x)
    rw [heq]
    exact hyV
  let gV := IsOpenImmersion.lift V.ι g hgRange
  have gV_fac : gV ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  let S := Γ(V.toScheme, ⊤)
  let α : R →+* S := V.ι.appTop.hom.comp er
  let β : S →+* K := (Scheme.ΓSpecIso (.of K)).hom.hom.comp gV.appTop.hom
  have hβα : β.comp α = ψ := by
    have htri : (Scheme.ΓSpecIso (.of R)).inv ≫ V.ι.appTop ≫ gV.appTop ≫
        (Scheme.ΓSpecIso (.of K)).hom = CommRingCat.ofHom ψ := by
      calc
        (Scheme.ΓSpecIso (.of R)).inv ≫ V.ι.appTop ≫ gV.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom =
          (Scheme.ΓSpecIso (.of R)).inv ≫ (gV ≫ V.ι).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
            rw [Scheme.Hom.comp_appTop]
            simp only [Category.assoc]
        _ = (Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by rw [gV_fac]
        _ = CommRingCat.ofHom ψ := by
          change (Scheme.ΓSpecIso (.of R)).inv ≫
            (Spec.map (CommRingCat.ofHom ψ)).appTop ≫ (Scheme.ΓSpecIso (.of K)).hom = _
          rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ),
            Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact congrArg CommRingCat.Hom.hom htri
  letI : Algebra R S := α.toAlgebra
  letI : Algebra S K := β.toAlgebra
  have hflatα : α.Flat :=
    (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp
      V.ι.flat_appTop
  haveI : Module.Flat R S := hflatα
  have hs := split V.ι (by
    rw [Scheme.Opens.range_ι]
    exact hVW)
  have hs' : Matrix.HasSplitHomology (0 : Matrix n (ULift.{u} (Fin 0)) S)
      (A.map (algebraMap R S)) (Fin (Fintype.card n - ρ)) := by
    have hmap : AΓ.map V.ι.appTop = A.map (algebraMap R S) := by
      ext i j
      rfl
    rw [hmap] at hs
    exact hs
  let E := ModuleCat.extendScalars (algebraMap R S)
  let F := ModuleCat.extendScalars (algebraMap S K)
  have hE : IsIso (kernelComparison (ModuleCat.ofHom A.mulVecLin) E) :=
    isIso_kernelComparison_extendScalars_of_flat R S _
  have hsU := hs'.of_equiv (Equiv.ulift.symm : Fin (Fintype.card n - ρ) ≃ ULift.{u} (Fin (Fintype.card n - ρ)))
  have hF : IsIso (kernelComparison (E.map (ModuleCat.ofHom A.mulVecLin)) F) :=
    isIso_kernelComparison_extended_matrix_of_split R S K A hsU
  haveI := hE
  haveI := hF
  have hEF : IsIso (kernelComparison (ModuleCat.ofHom A.mulVecLin) (E ⋙ F)) := by
    rw [kernelComparison_comp_functor]
    infer_instance
  let iso : E ⋙ F ≅ ModuleCat.extendScalars ψ :=
    (ModuleCat.extendScalarsComp α β).symm ≪≫ eqToIso (congrArg ModuleCat.extendScalars hβα)
  exact isIso_kernelComparison_of_functor_iso (ModuleCat.ofHom A.mulVecLin) (E ⋙ F) _ iso hEF

end ZInQ.Contrib.CloudR2Poincare.L1
