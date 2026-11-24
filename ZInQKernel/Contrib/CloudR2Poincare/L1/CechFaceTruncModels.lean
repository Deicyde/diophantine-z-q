import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceMaps
import ZInQKernel.Contrib.CloudR2Poincare.L1.FaceCompatibleModels

/-!
# Retained models of the ORIGINAL native Čech two-face diagram

The original non-alternating complexes are NOT termwise bounded. Their native
good truncations are proved bounded, flat and perfect from proper-family data.
Actual truncation naturality and the universally quasi-isomorphic native
inclusions transport the ACTUAL retained chain/homotopy diagram back to the
ORIGINAL Čech complexes, including every nonflat residue-field extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Proper Noetherian native Čech good truncation is perfect, from its actual
flat terms and finite homology; no boundedness of the original complex is assumed. -/
theorem isPerfect_nativeCechTrunc_of_isProper
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (M : X.Modules) [M.IsFinitePresentation] (flatM : M.IsFlatOver q)
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} Γ(Spec (.of R), ⊤))] :
    (DerivedCategory.Q.obj (Scheme.Modules.cechModuleComplexTrunc q M U)).IsPerfect := by
  let A := Γ(Spec (.of R), ⊤)
  letI : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let C := Scheme.Modules.cechModuleComplexTrunc q M U
  let b : ℤ := (Fintype.card ι : ℤ) - 1
  haveI : C.IsStrictlyGE 0 := inferInstance
  haveI : C.IsStrictlyLE b := inferInstance
  have flatC (n : ℤ) : Module.Flat A (C.X n) :=
    Scheme.Modules.flat_cechModuleComplexTrunc_X q M U affineU coverU flatM n
  have finiteH (n : ℤ) : Module.Finite A (C.homology n) :=
    Scheme.Modules.finite_homology_cechModuleComplexTrunc_of_isProper q M U affineU coverU n
  have finiteDerived (n : ℤ) : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj (DerivedCategory.Q.obj C)) := by
    haveI := finiteH n
    exact Module.Finite.equiv (R := A) (M := C.homology n)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app C).toLinearEquiv.symm
  exact DerivedCategory.isPerfect_of_flat_of_finite_homology C 0 b flatC (Iso.refl _) finiteDerived

/-- Postcomposition transports a retained actual homotopy through an ACTUAL
commuting inclusion square, not through an equality merely in D(A). -/
def retainedFaceHomotopy_postcompose
    {A : Type u} [CommRing A]
    {P PX C DX CF DXF : CochainComplex (ModuleCat.{u} A) ℤ}
    {ψ : P ⟶ PX} {eX : PX ⟶ DX} {eC : P ⟶ C} {Φ : C ⟶ DX}
    (ιC : C ⟶ CF) (ιX : DX ⟶ DXF) (ΦF : CF ⟶ DXF)
    (square : Φ ≫ ιX = ιC ≫ ΦF) (h : Homotopy (ψ ≫ eX) (eC ≫ Φ)) :
    Homotopy (ψ ≫ (eX ≫ ιX)) ((eC ≫ ιC) ≫ ΦF) := by
  have h' := h.compRight ιX
  have hl : (ψ ≫ eX) ≫ ιX = ψ ≫ (eX ≫ ιX) := Category.assoc _ _ _
  have hr : (eC ≫ Φ) ≫ ιX = (eC ≫ ιC) ≫ ΦF := by
    rw [Category.assoc, square, ← Category.assoc]
  exact (Homotopy.ofEq hl.symm).trans (h'.trans (Homotopy.ofEq hr))

/-- Scalar extension of the native good-truncation inclusion is ACTUALLY a
quasi-isomorphism after TWO consecutive extensions, even if the final ring is nonflat. -/
theorem quasiIso_doubleScalar_nativeCechTrunc_inclusion
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (M : X.Modules) [M.IsFinitePresentation] (flatM : M.IsFlatOver q)
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (S B : Type u) [CommRing S] [CommRing B] [Algebra Γ(Spec (.of R), ⊤) S] [Algebra S B] :
    let E := (ModuleCat.extendScalars (algebraMap Γ(Spec (.of R), ⊤) S)).mapHomologicalComplex (.up ℤ)
    let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (.up ℤ)
    QuasiIso (F.map (E.map ((Scheme.Modules.cechModuleComplex q M U).ιTruncLE
      ((Fintype.card ι : ℤ) - 1)))) := by
  let A := Γ(Spec (.of R), ⊤)
  let C := Scheme.Modules.cechModuleComplexTrunc q M U
  let CF := Scheme.Modules.cechModuleComplex q M U
  let b : ℤ := (Fintype.card ι : ℤ) - 1
  let inc : C ⟶ CF := CF.ιTruncLE b
  let E := (ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex (.up ℤ)
  let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (.up ℤ)
  letI : Algebra A B := ((algebraMap S B).comp (algebraMap A S)).toAlgebra
  have single := Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex q M U affineU coverU flatM B
  let assoc := Functor.mapHomologicalComplexCompIso
    (ModuleCat.extendScalarsComp (algebraMap A S) (algebraMap S B)).symm (.up ℤ)
  exact (quasiIso_iff_of_arrow_mk_iso (F.map (E.map inc)) _
    (Arrow.isoMk (assoc.app C) (assoc.app CF) (assoc.hom.naturality inc).symm)).mpr single

/-- Proper native two-face families admit ACTUAL retained models of their
ORIGINAL Čech diagram. Boundedness/perfectness are proved on good truncations;
all scalar comparisons and stored homotopies survive when returning to the
original non-alternating complexes. -/
theorem exists_retained_nativeCechFace_models
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X Y Z : Scheme.{u}} (q : X ⟶ Spec (.of R)) (jX : Y ⟶ X) (jY : Z ⟶ X)
    [IsProper q] [Flat q] [IsProper (jX ≫ q)] [Flat (jX ≫ q)]
    [IsProper (jY ≫ q)] [Flat (jY ≫ q)] [IsAffineHom jX] [IsAffineHom jY]
    (M : X.Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (p : Ideal Γ(Spec (.of R), ⊤)) [p.IsPrime] :
    ∃ d ∉ p,
      let A := Γ(Spec (.of R), ⊤)
      let S := Localization.Away d
      let E := (ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex (.up ℤ)
      let C := Scheme.Modules.cechModuleComplex q M U
      let DX := Scheme.Modules.cechModuleComplex (jX ≫ q) ((Scheme.Modules.pullback jX).obj M)
        (fun i ↦ jX ⁻¹ᵁ U i)
      let DY := Scheme.Modules.cechModuleComplex (jY ≫ q) ((Scheme.Modules.pullback jY).obj M)
        (fun i ↦ jY ⁻¹ᵁ U i)
      let b : ℤ := (Fintype.card ι : ℤ) - 1
      ∃ (P PX PY : CochainComplex (ModuleCat.{u} S) ℤ),
        P.IsStrictlyGE 0 ∧ P.IsStrictlyLE b ∧
        PX.IsStrictlyGE 0 ∧ PX.IsStrictlyLE b ∧
        PY.IsStrictlyGE 0 ∧ PY.IsStrictlyLE b ∧
        (∀ n, Module.Free S (P.X n) ∧ Module.Finite S (P.X n)) ∧
        (∀ n, Module.Free S (PX.X n) ∧ Module.Finite S (PX.X n)) ∧
        (∀ n, Module.Free S (PY.X n) ∧ Module.Finite S (PY.X n)) ∧
        ∃ (eC : P ⟶ E.obj C) (eX : PX ⟶ E.obj DX) (eY : PY ⟶ E.obj DY),
          QuasiIso eC ∧ QuasiIso eX ∧ QuasiIso eY ∧
          (∀ (B : Type u) [CommRing B] [Algebra S B],
            let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (.up ℤ)
            QuasiIso (F.map eC) ∧ QuasiIso (F.map eX) ∧ QuasiIso (F.map eY)) ∧
          ∃ (ψX : P ⟶ PX) (ψY : P ⟶ PY),
            Nonempty (Homotopy (ψX ≫ eX) (eC ≫ E.map (cechModuleFaceMap q jX M U))) ∧
            Nonempty (Homotopy (ψY ≫ eY) (eC ≫ E.map (cechModuleFaceMap q jY M U))) := by
  classical
  let A := Γ(Spec (.of R), ⊤)
  let b : ℤ := (Fintype.card ι : ℤ) - 1
  let MX := (Scheme.Modules.pullback jX).obj M
  let MY := (Scheme.Modules.pullback jY).obj M
  let UX := fun i ↦ jX ⁻¹ᵁ U i
  let UY := fun i ↦ jY ⁻¹ᵁ U i
  have affineX : ∀ i, IsAffineOpen (UX i) := fun i ↦ (affineU i).preimage jX
  have affineY : ∀ i, IsAffineOpen (UY i) := fun i ↦ (affineU i).preimage jY
  have coverX : ⨆ i, UX i = ⊤ := by rw [← jX.preimage_iSup, coverU, jX.preimage_top]
  have coverY : ⨆ i, UY i = ⊤ := by rw [← jY.preimage_iSup, coverU, jY.preimage_top]
  have flatM : M.IsFlatOver q := Scheme.Modules.isFlatOver_of_isInvertible q M
  have flatMX : MX.IsFlatOver (jX ≫ q) := Scheme.Modules.isFlatOver_of_isInvertible (jX ≫ q) MX
  have flatMY : MY.IsFlatOver (jY ≫ q) := Scheme.Modules.isFlatOver_of_isInvertible (jY ≫ q) MY
  let C := Scheme.Modules.cechModuleComplex q M U
  let DX := Scheme.Modules.cechModuleComplex (jX ≫ q) MX UX
  let DY := Scheme.Modules.cechModuleComplex (jY ≫ q) MY UY
  let CT := Scheme.Modules.cechModuleComplexTrunc q M U
  let DXT := Scheme.Modules.cechModuleComplexTrunc (jX ≫ q) MX UX
  let DYT := Scheme.Modules.cechModuleComplexTrunc (jY ≫ q) MY UY
  let ΦX := cechModuleFaceMap q jX M U
  let ΦY := cechModuleFaceMap q jY M U
  let ΦXT : CT ⟶ DXT := CochainComplex.truncLEMap ΦX b
  let ΦYT : CT ⟶ DYT := CochainComplex.truncLEMap ΦY b
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  have flatCT (n) : Module.Flat A (CT.X n) :=
    Scheme.Modules.flat_cechModuleComplexTrunc_X q M U affineU coverU flatM n
  have flatDXT (n) : Module.Flat A (DXT.X n) :=
    Scheme.Modules.flat_cechModuleComplexTrunc_X (jX ≫ q) MX UX affineX coverX flatMX n
  have flatDYT (n) : Module.Flat A (DYT.X n) :=
    Scheme.Modules.flat_cechModuleComplexTrunc_X (jY ≫ q) MY UY affineY coverY flatMY n
  have perfectCT := isPerfect_nativeCechTrunc_of_isProper R q M flatM U affineU coverU
  have perfectDXT := isPerfect_nativeCechTrunc_of_isProper R (jX ≫ q) MX flatMX UX affineX coverX
  have perfectDYT := isPerfect_nativeCechTrunc_of_isProper R (jY ≫ q) MY flatMY UY affineY coverY
  obtain ⟨d, hd, P, PX, PY, loP, hiP, loPX, hiPX, loPY, hiPY,
      freeP, freePX, freePY, eCT, eXT, eYT, qeCT, qeXT, qeYT, universalT,
      ψX, ψY, hψXT, hψYT⟩ :=
    exists_retained_faceCompatible_models CT DXT DYT ΦXT ΦYT b
      flatCT flatDXT flatDYT perfectCT perfectDXT perfectDYT p
  let S := Localization.Away d
  let E := (ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex (.up ℤ)
  let incC : CT ⟶ C := C.ιTruncLE b
  let incX : DXT ⟶ DX := DX.ιTruncLE b
  let incY : DYT ⟶ DY := DY.ιTruncLE b
  let eC := eCT ≫ E.map incC
  let eX := eXT ≫ E.map incX
  let eY := eYT ≫ E.map incY
  haveI : QuasiIso eCT := qeCT
  haveI : QuasiIso eXT := qeXT
  haveI : QuasiIso eYT := qeYT
  haveI : QuasiIso (E.map incC) :=
    Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex q M U affineU coverU flatM S
  haveI : QuasiIso (E.map incX) :=
    Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex (jX ≫ q) MX UX affineX coverX flatMX S
  haveI : QuasiIso (E.map incY) :=
    Scheme.Modules.quasiIso_extendScalars_ιTruncLE_cechModuleComplex (jY ≫ q) MY UY affineY coverY flatMY S
  have sqX : ΦXT ≫ incX = incC ≫ ΦX := cechModuleFaceMap_truncation_square q jX M U b
  have sqY : ΦYT ≫ incY = incC ≫ ΦY := cechModuleFaceMap_truncation_square q jY M U b
  have hX : Nonempty (Homotopy (ψX ≫ eX) (eC ≫ E.map ΦX)) :=
    ⟨retainedFaceHomotopy_postcompose (E.map incC) (E.map incX) (E.map ΦX)
      (by rw [← E.map_comp, ← E.map_comp, sqX]) hψXT.some⟩
  have hY : Nonempty (Homotopy (ψY ≫ eY) (eC ≫ E.map ΦY)) :=
    ⟨retainedFaceHomotopy_postcompose (E.map incC) (E.map incY) (E.map ΦY)
      (by rw [← E.map_comp, ← E.map_comp, sqY]) hψYT.some⟩
  refine ⟨d, hd, P, PX, PY, loP, hiP, loPX, hiPX, loPY, hiPY,
    freeP, freePX, freePY, eC, eX, eY, inferInstance, inferInstance, inferInstance, ?_, ψX, ψY, hX, hY⟩
  intro B _ _
  let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (.up ℤ)
  obtain ⟨hC, hX, hY⟩ := universalT B
  haveI : QuasiIso (F.map eCT) := hC
  haveI : QuasiIso (F.map eXT) := hX
  haveI : QuasiIso (F.map eYT) := hY
  haveI : QuasiIso (F.map (E.map incC)) :=
    quasiIso_doubleScalar_nativeCechTrunc_inclusion R q M flatM U affineU coverU S B
  haveI : QuasiIso (F.map (E.map incX)) :=
    quasiIso_doubleScalar_nativeCechTrunc_inclusion R (jX ≫ q) MX flatMX UX affineX coverX S B
  haveI : QuasiIso (F.map (E.map incY)) :=
    quasiIso_doubleScalar_nativeCechTrunc_inclusion R (jY ≫ q) MY flatMY UY affineY coverY S B
  dsimp only [eC, eX, eY]
  rw [F.map_comp, F.map_comp, F.map_comp]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end ZInQ.Contrib.CloudR2Poincare.L1
