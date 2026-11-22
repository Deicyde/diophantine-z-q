import ZInQKernel.Contrib.CloudR2Poincare.L1.CechKernelFromModel
import ZInQKernel.Contrib.CloudR2Poincare.L1.RetainedCechModel
import ZInQKernel.Contrib.CloudR2Poincare.L1.CoefficientBaseChangeFromKernel
import ZInQKernel.Contrib.CloudR2Poincare.L1.CanonicalResidueSections
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Canonical degree-zero kernel preservation for the ORIGINAL Čech complex

The retained map is universally quasi-isomorphic. The P-side ACTUAL scalar
kernel comparison is derived from reduced rank one. Naturality transports
it through the retained map, and flat localization gives the original
residue-field extension. There is no caller-supplied model, kernel-preservation
hypothesis, or desired seesaw Fact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The ORIGINAL module-valued Čech d0 canonical comparison is invertible
under actual residue-field scalar extension for a reduced proper family
whose invertible coefficient sheaf is trivial on every residue fibre. -/
theorem isIso_originalCech_residueKernelComparison
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hFibres : ∀ y : Spec (.of R), Scheme.Pic.map
      (pullback.fst f ((Spec (.of R)).fromSpecResidueField y)) (Scheme.Pic.mk M) = 1)
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    (y : Spec (.of R)) :
    IsIso (kernelComparison ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1)
      (ModuleCat.extendScalars (((Spec (.of R)).fromSpecResidueField y).appTop.hom))) := by
  classical
  let Y := Spec (.of R)
  let A := Γ(Y, ⊤)
  letI : _root_.IsReduced A := isReduced_of_injective (Scheme.ΓSpecIso (.of R)).hom.hom
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
  let q : PrimeSpectrum A := Y.toSpecΓ.base y
  haveI : q.asIdeal.IsPrime := q.isPrime
  have hflat : M.IsFlatOver f := Scheme.Modules.isFlatOver_of_isInvertible f M
  obtain ⟨d, hd, P, hPlo, hPhi, hfree, φ, hφ, universal⟩ :=
    exists_retained_universal_cech_comparison R f M hflat U hU hcover q.asIdeal
  let S := Localization.Away d
  let B := Γ(Spec (Y.residueField y), ⊤)
  letI : Field B := (Scheme.Modules.isField_Γ_Spec_residueField y).toField
  let p := Y.fromSpecResidueField y
  have hy : y ∈ Y.basicOpen d := by
    rw [← Y.toSpecΓ_preimage_basicOpen]
    exact hd
  obtain ⟨x⟩ : Nonempty (Spec (Y.residueField y)) := inferInstance
  have hne : p.appTop d ≠ 0 :=
    (p.appTop_ne_zero_iff_mem_basicOpen (Scheme.Modules.isField_Γ_Spec_residueField y) d x).mpr
      (by
        change p.base x ∈ Y.basicOpen d
        dsimp only [p]
        rw [Scheme.Modules.fromSpecResidueField_base_apply]
        exact hy)
  let β : S →+* B := Localization.awayLift p.appTop.hom d (isUnit_iff_ne_zero.mpr hne)
  let α : A →+* S := algebraMap A S
  have hβα : β.comp α = p.appTop.hom := IsLocalization.Away.lift_comp _ _
  letI : Algebra S B := β.toAlgebra
  letI : Nontrivial S := nontrivial_of_ne (0 : S) 1 (by
    intro hs
    have h := congrArg β hs
    rw [map_zero, map_one] at h
    exact zero_ne_one h)
  haveI : P.IsStrictlyGE 0 := hPlo
  letI (i : ℤ) : Module.Free S (P.X i) := (hfree i).1
  letI (i : ℤ) : Module.Finite S (P.X i) := (hfree i).2
  let b (i : ℤ) : Module.Basis (ULift.{u} (Fin (Module.finrank S (P.X i)))) S (P.X i) :=
    (Module.finBasis S (P.X i)).reindex Equiv.ulift.symm
  let C := Scheme.Modules.cechModuleComplex f M U
  haveI : QuasiIso φ := hφ
  have hComp := isIso_originalScalarCechKernel_of_retainedComparison f M hFibres U hcover
    (Scheme.Modules.isAffineOpen_iInf_of_isSeparated f U hU) S P (b 0) (b 1) φ universal B β
  let G := ModuleCat.extendScalars p.appTop.hom
  have hG : IsIso (kernelComparison (C.d 0 1) G) := by
    change IsIso (kernelComparison (C.d 0 1) (ModuleCat.extendScalars (β.comp α))) at hComp
    rw [hβα] at hComp
    exact hComp
  let N := Scheme.Modules.cechModuleComplexNat f M U
  let e0 := N.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl
  let e1 := N.extendXIso ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl
  have h : C.d 0 1 ≫ e1.hom = e0.hom ≫ N.d 0 1 := by
    change (N.extend ComplexShape.embeddingUpNat).d 0 1 ≫ e1.hom = e0.hom ≫ N.d 0 1
    rw [N.extend_d_eq ComplexShape.embeddingUpNat (i := 0) (j := 1)
      (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    simp only [e0, e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact isIso_kernelComparison_of_universal_model_map G (C.d 0 1) (N.d 0 1)
    e0.hom e1.hom h (by infer_instance) (by infer_instance) hG

/-- The actual canonical residue coefficient-sections map is bijective,
with no additional kernel-comparison or model hypothesis. -/
theorem bijective_canonicalResidueSectionsBaseChange
    (R : Type u) [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hFibres : ∀ y : Spec (.of R), Scheme.Pic.map
      (pullback.fst f ((Spec (.of R)).fromSpecResidueField y)) (Scheme.Pic.mk M) = 1)
    (y : Spec (.of R)) :
    Function.Bijective (canonicalResidueSectionsBaseChange f M y) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨U, hUfinite, hcover⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).mp
      (by simpa using isCompact_univ)
  letI : Finite U := hUfinite
  let I := Option U
  letI : Fintype I := Fintype.ofFinite I
  let cover : I → X.Opens := fun i ↦ i.elim ⊥ (fun a ↦ a.val.val)
  have ha : ∀ i, IsAffineOpen (cover i) := by
    rintro (_ | a)
    · exact isAffineOpen_bot X
    · exact a.val.property
  have hc : ⨆ i, cover i = ⊤ := by
    apply le_antisymm le_top
    rw [hcover]
    exact iSup₂_le fun a ha ↦ le_iSup_of_le (some ⟨a, ha⟩) le_rfl
  let p := (Spec (.of R)).fromSpecResidueField y
  letI : Algebra Γ(Spec (.of R), ⊤) Γ(Spec ((Spec (.of R)).residueField y), ⊤) := p.appTop.hom.toAlgebra
  have hK := isIso_originalCech_residueKernelComparison R f M hFibres cover ha hc y
  exact bijective_coefficientBaseChange_of_cech_kernelComparison (IsPullback.of_hasPullback f p) M rfl
    cover hc (Scheme.Modules.isAffineOpen_iInf_of_isSeparated f cover ha) hK

end ZInQ.Contrib.CloudR2Poincare.L1
