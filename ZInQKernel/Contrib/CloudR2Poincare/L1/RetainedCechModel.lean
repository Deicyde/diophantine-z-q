import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeModel

/-!
# Retaining an actual universally quasi-isomorphic Čech model map

This uses the unchanged published bounded-flat/perfect and Čech-truncation
suppliers to construct an ACTUAL map into the original Čech complex. Unlike
the objectwise higher-direct-image existential, the map itself remains in the
output and can be used in canonical kernel-comparison naturality squares.
No W07 file is copied/modified; no desired canonical sections assertion is
assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- A bounded flat perfect complex has a retained finite-free model map, with
an ACTUAL quasi-isomorphism after every further extension of scalars. -/
theorem exists_retained_universal_free_comparison
    {A : Type u} [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (lo hi : ℤ)
    [C.IsStrictlyGE lo] [C.IsStrictlyLE hi]
    (hflat : ∀ q, Module.Flat A (C.X q))
    (hperfect : (DerivedCategory.Q.obj C).IsPerfect) (p : Ideal A) [p.IsPrime] :
    ∃ d ∉ p,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away d)) ℤ)
        (_ : P.IsStrictlyGE lo) (_ : P.IsStrictlyLE hi),
        (∀ q, Module.Free (Localization.Away d) (P.X q) ∧ Module.Finite (Localization.Away d) (P.X q)) ∧
        ∃ φ : P ⟶ ((ModuleCat.extendScalars (algebraMap A (Localization.Away d))).mapHomologicalComplex _).obj C,
          QuasiIso φ ∧ ∀ (B : Type u) [CommRing B] [Algebra (Localization.Away d) B],
            QuasiIso (((ModuleCat.extendScalars (algebraMap (Localization.Away d) B)).mapHomologicalComplex _).map φ) := by
  obtain ⟨d, hd, P, hPlo, hPhi, hPfree, φ, hφ⟩ :=
    DerivedCategory.exists_quasiIso_free_away_of_isPerfect C lo hi hflat hperfect p
  refine ⟨d, hd, P, hPlo, hPhi, hPfree, φ, hφ, ?_⟩
  intro B _ _
  let S := Localization.Away d
  haveI : P.IsStrictlyLE hi := hPhi
  let E := ModuleCat.extendScalars (algebraMap A S)
  haveI : CochainComplex.IsStrictlyLE ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj C) hi := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact E.map_isZero (C.isZero_of_isStrictlyLE hi q hq)
  have hpflat (q : ℤ) : Module.Flat S (P.X q) := by
    haveI := (hPfree q).1
    infer_instance
  have hcflat (q : ℤ) : Module.Flat S (((E.mapHomologicalComplex _).obj C).X q) := by
    haveI := hflat q
    exact Module.Flat.of_linearEquiv (ModuleCat.tensorEquivExtendScalars A S (C.X q)).symm
  exact CochainComplex.quasiIso_extendScalars_of_boundedAbove_flat φ hi hpflat hcflat hφ (algebraMap S B)

/-- The actual proper-family Čech complex has a finite-free model with a
RETAINED map to the original complex, universally quasi-isomorphic after every
base change. The target is the original complex, not a chosen H0 object. -/
theorem exists_retained_universal_cech_comparison
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (M : X.Modules) [M.IsFinitePresentation] (hflat : M.IsFlatOver f)
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : ⨆ i, U i = ⊤)
    (p : Ideal Γ(Spec (.of R), ⊤)) [p.IsPrime] :
    ∃ d ∉ p,
      ∃ (P : CochainComplex (ModuleCat.{u} (Localization.Away d)) ℤ)
        (_ : P.IsStrictlyGE 0) (_ : P.IsStrictlyLE ((Fintype.card ι : ℤ) - 1)),
        (∀ q, Module.Free (Localization.Away d) (P.X q) ∧ Module.Finite (Localization.Away d) (P.X q)) ∧
        ∃ φ : P ⟶ ((ModuleCat.extendScalars (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).mapHomologicalComplex _).obj
            (Scheme.Modules.cechModuleComplex f M U),
          QuasiIso φ ∧ ∀ (B : Type u) [CommRing B] [Algebra (Localization.Away d) B],
            QuasiIso (((ModuleCat.extendScalars (algebraMap (Localization.Away d) B)).mapHomologicalComplex _).map φ) := by
  let A := Γ(Spec (.of R), ⊤)
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let full := Scheme.Modules.cechModuleComplex f M U
  let C := Scheme.Modules.cechModuleComplexTrunc f M U
  let hi : ℤ := (Fintype.card ι : ℤ) - 1
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  haveI : C.IsStrictlyGE 0 := inferInstance
  haveI : C.IsStrictlyLE hi := inferInstance
  have flatC (q : ℤ) : Module.Flat A (C.X q) :=
    Scheme.Modules.flat_cechModuleComplexTrunc_X f M U hU hcover hflat q
  have finiteH (q : ℤ) : Module.Finite A (C.homology q) :=
    Scheme.Modules.finite_homology_cechModuleComplexTrunc_of_isProper f M U hU hcover q
  have finiteDerived (q : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (DerivedCategory.Q.obj C)) := by
    haveI := finiteH q
    exact Module.Finite.equiv (R := A) (M := C.homology q)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) q).app C).toLinearEquiv.symm
  have perfect : (DerivedCategory.Q.obj C).IsPerfect :=
    DerivedCategory.isPerfect_of_flat_of_finite_homology C 0 hi flatC (Iso.refl _) finiteDerived
  obtain ⟨d, hd, P, hPlo, hPhi, hPfree, φ, hφ, universal⟩ :=
    exists_retained_universal_free_comparison C 0 hi flatC perfect p
  let S := Localization.Away d
  let E := ModuleCat.extendScalars (algebraMap A S)
  let inc : C ⟶ full := full.ιTruncLE hi
  have hinc : QuasiIso ((E.mapHomologicalComplex _).map inc) :=
    Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex f M U hU hcover hflat S
  haveI := hinc
  haveI := hφ
  let ψ : P ⟶ ((E.mapHomologicalComplex _).obj full) := φ ≫ (E.mapHomologicalComplex _).map inc
  refine ⟨d, hd, P, hPlo, hPhi, hPfree, ψ, inferInstance, ?_⟩
  intro B _ _
  letI : Algebra A B := ((algebraMap S B).comp (algebraMap A S)).toAlgebra
  let F := ModuleCat.extendScalars (algebraMap S B)
  haveI : QuasiIso ((F.mapHomologicalComplex _).map φ) := universal B
  have hsingle : QuasiIso (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex _).map inc) :=
    Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex f M U hU hcover hflat B
  let assoc := Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp (algebraMap A S) (algebraMap S B)).symm (ComplexShape.up ℤ)
  haveI : QuasiIso ((F.mapHomologicalComplex _).map ((E.mapHomologicalComplex _).map inc)) :=
    (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (assoc.app C) (assoc.app full) (assoc.hom.naturality inc).symm)).mpr hsingle
  dsimp only [ψ]
  rw [Functor.map_comp]
  infer_instance

end ZInQ.Contrib.CloudR2Poincare.L1
