import ZInQKernel.Contrib.CloudR2Poincare.L1.FaceHomotopyLift
import ZInQKernel.Contrib.CloudR2Poincare.L1.FaceModelScalarTransport

/-!
# Common localized finite-free models of the ACTUAL two-face diagram

The three finite-free maps are constructed by the existing native retained
provider. Their actual common localization is the product of the three
nonvanishing denominators. Bounded-projective lifting produces actual chain
arrows and stored homotopies through the actual target quasi-isomorphisms.
Every comparison remains quasi-isomorphic under ALL scalar extensions;
the same homotopies transport by `scalarExtension_faceSquare_homotopy`.
This is exactly L6 §4b, not an assumed face-compatible-model premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Native retained finite-free models of an actual bounded flat perfect
span, with genuine chain/homotopy witnesses and universal scalar comparison. -/
theorem exists_retained_faceCompatible_models
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (C DX DY : CochainComplex (ModuleCat.{u} A) ℤ)
    (ΦX : C ⟶ DX) (ΦY : C ⟶ DY) (b : ℤ)
    [C.IsStrictlyGE 0] [C.IsStrictlyLE b]
    [DX.IsStrictlyGE 0] [DX.IsStrictlyLE b]
    [DY.IsStrictlyGE 0] [DY.IsStrictlyLE b]
    (flatC : ∀ n, Module.Flat A (C.X n))
    (flatX : ∀ n, Module.Flat A (DX.X n))
    (flatY : ∀ n, Module.Flat A (DY.X n))
    (perfectC : (DerivedCategory.Q.obj C).IsPerfect)
    (perfectX : (DerivedCategory.Q.obj DX).IsPerfect)
    (perfectY : (DerivedCategory.Q.obj DY).IsPerfect)
    (p : Ideal A) [p.IsPrime] :
    ∃ d ∉ p,
      let S := Localization.Away d
      let E := (ModuleCat.extendScalars (algebraMap A S)).mapHomologicalComplex (.up ℤ)
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
            Nonempty (Homotopy (ψX ≫ eX) (eC ≫ E.map ΦX)) ∧
            Nonempty (Homotopy (ψY ≫ eY) (eC ≫ E.map ΦY)) := by
  classical
  obtain ⟨dC, hdC, P₀, hP₀lo, hP₀hi, freeP₀, eC₀, qeC₀, ueC₀⟩ :=
    exists_retained_universal_free_comparison C 0 b flatC perfectC p
  obtain ⟨dX, hdX, PX₀, hPX₀lo, hPX₀hi, freePX₀, eX₀, qeX₀, ueX₀⟩ :=
    exists_retained_universal_free_comparison DX 0 b flatX perfectX p
  obtain ⟨dY, hdY, PY₀, hPY₀lo, hPY₀hi, freePY₀, eY₀, qeY₀, ueY₀⟩ :=
    exists_retained_universal_free_comparison DY 0 b flatY perfectY p
  let d := dC * dX * dY
  have hd : d ∉ p := ‹p.IsPrime›.mul_notMem (‹p.IsPrime›.mul_notMem hdC hdX) hdY
  let S := Localization.Away d
  let α : A →+* S := algebraMap A S
  have hunit : IsUnit (α d) := IsLocalization.Away.algebraMap_isUnit d
  change IsUnit (α (dC * dX * dY)) at hunit
  rw [map_mul, map_mul] at hunit
  have hCX : IsUnit (α dC * α dX) := (IsUnit.mul_iff.mp hunit).1
  have hC : IsUnit (α dC) := (IsUnit.mul_iff.mp hCX).1
  have hX : IsUnit (α dX) := (IsUnit.mul_iff.mp hCX).2
  have hY : IsUnit (α dY) := (IsUnit.mul_iff.mp hunit).2
  let RC := Localization.Away dC
  let RX := Localization.Away dX
  let RY := Localization.Away dY
  let βC : RC →+* S := Localization.awayLift α dC hC
  let βX : RX →+* S := Localization.awayLift α dX hX
  let βY : RY →+* S := Localization.awayLift α dY hY
  have hβC : βC.comp (algebraMap A RC) = α := IsLocalization.Away.lift_comp _ _
  have hβX : βX.comp (algebraMap A RX) = α := IsLocalization.Away.lift_comp _ _
  have hβY : βY.comp (algebraMap A RY) = α := IsLocalization.Away.lift_comp _ _
  haveI : P₀.IsStrictlyGE 0 := hP₀lo
  haveI : P₀.IsStrictlyLE b := hP₀hi
  haveI : PX₀.IsStrictlyGE 0 := hPX₀lo
  haveI : PX₀.IsStrictlyLE b := hPX₀hi
  haveI : PY₀.IsStrictlyGE 0 := hPY₀lo
  haveI : PY₀.IsStrictlyLE b := hPY₀hi
  let E := (ModuleCat.extendScalars α).mapHomologicalComplex (.up ℤ)
  let P : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars βC).mapHomologicalComplex (.up ℤ)).obj P₀
  let PX : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars βX).mapHomologicalComplex (.up ℤ)).obj PX₀
  let PY : CochainComplex (ModuleCat.{u} S) ℤ :=
    ((ModuleCat.extendScalars βY).mapHomologicalComplex (.up ℤ)).obj PY₀
  have boundsP := scalarExtendedComplex_strictBounds βC P₀ 0 b
  have boundsPX := scalarExtendedComplex_strictBounds βX PX₀ 0 b
  have boundsPY := scalarExtendedComplex_strictBounds βY PY₀ 0 b
  have freeP (n : ℤ) : Module.Free S (P.X n) ∧ Module.Finite S (P.X n) := by
    letI : Algebra RC S := βC.toAlgebra
    haveI : Module.Free RC (P₀.X n) := (freeP₀ n).1
    haveI : Module.Finite RC (P₀.X n) := (freeP₀ n).2
    exact scalarExtension_free_finite RC S (P₀.X n)
  have freePX (n : ℤ) : Module.Free S (PX.X n) ∧ Module.Finite S (PX.X n) := by
    letI : Algebra RX S := βX.toAlgebra
    haveI : Module.Free RX (PX₀.X n) := (freePX₀ n).1
    haveI : Module.Finite RX (PX₀.X n) := (freePX₀ n).2
    exact scalarExtension_free_finite RX S (PX₀.X n)
  have freePY (n : ℤ) : Module.Free S (PY.X n) ∧ Module.Finite S (PY.X n) := by
    letI : Algebra RY S := βY.toAlgebra
    haveI : Module.Free RY (PY₀.X n) := (freePY₀ n).1
    haveI : Module.Finite RY (PY₀.X n) := (freePY₀ n).2
    exact scalarExtension_free_finite RY S (PY₀.X n)
  let eC : P ⟶ E.obj C := retainedMapAfterScalarExtension (algebraMap A RC) βC α hβC eC₀
  let eX : PX ⟶ E.obj DX := retainedMapAfterScalarExtension (algebraMap A RX) βX α hβX eX₀
  let eY : PY ⟶ E.obj DY := retainedMapAfterScalarExtension (algebraMap A RY) βY α hβY eY₀
  have qeC : QuasiIso eC := quasiIso_retainedMapAfterScalarExtension (algebraMap A RC) βC α hβC eC₀ ueC₀
  have qeX : QuasiIso eX := quasiIso_retainedMapAfterScalarExtension (algebraMap A RX) βX α hβX eX₀ ueX₀
  have qeY : QuasiIso eY := quasiIso_retainedMapAfterScalarExtension (algebraMap A RY) βY α hβY eY₀ ueY₀
  have universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      let F := (ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex (.up ℤ)
      QuasiIso (F.map eC) ∧ QuasiIso (F.map eX) ∧ QuasiIso (F.map eY) := by
    intro B _ _
    exact ⟨universal_quasiIso_retainedMapAfterScalarExtension (algebraMap A RC) βC α hβC eC₀ ueC₀ B,
      universal_quasiIso_retainedMapAfterScalarExtension (algebraMap A RX) βX α hβX eX₀ ueX₀ B,
      universal_quasiIso_retainedMapAfterScalarExtension (algebraMap A RY) βY α hβY eY₀ ueY₀ B⟩
  haveI : P.IsStrictlyLE b := boundsP.2
  letI (n : ℤ) : Projective (P.X n) := by
    haveI : Module.Free S (P.X n) := (freeP n).1
    infer_instance
  letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} S) := HasDerivedCategory.standard _
  haveI : QuasiIso eX := qeX
  haveI : QuasiIso eY := qeY
  obtain ⟨ψX, hψX⟩ := exists_homotopyLift_of_bounded_projective b eX (eC ≫ E.map ΦX)
  obtain ⟨ψY, hψY⟩ := exists_homotopyLift_of_bounded_projective b eY (eC ≫ E.map ΦY)
  exact ⟨d, hd, P, PX, PY, boundsP.1, boundsP.2, boundsPX.1, boundsPX.2, boundsPY.1, boundsPY.2,
    freeP, freePX, freePY, eC, eX, eY, qeC, qeX, qeY, universal, ψX, ψY, hψX, hψY⟩

end ZInQ.Contrib.CloudR2Poincare.L1
