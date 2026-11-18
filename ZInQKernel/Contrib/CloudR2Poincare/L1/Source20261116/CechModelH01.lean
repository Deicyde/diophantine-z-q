import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.GeometricFieldCech

/-!
# Original-field H0/H1 comparisons of the produced Čech model arrows

These are witness-transport definitions. Their input e/universal/h is the
ACTUAL output of `exists_retained_nativeCechFace_models`; the closed geometry
constructor in ConsumerStatements supplies it. Neither e nor the geometric
Čech map is selected from ranks. The target map is the existing native H
pullback, and the same scalar ψ is retained in its commuting equation.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2Poincare.L1.RetainedFaceFibreConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L1

local instance instIsQuasicoherentOfIsInvertible_cechModel {X : Scheme.{u}}
    (M : X.Modules) [M.IsInvertible] : M.IsQuasicoherent :=
  SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} ‹M.IsInvertible›

/-- Degree0/1 equivalence of the already fixed ACTUAL face comparison. -/
def nativeCechFaceHFieldLinearEquiv_low
    {κ : Type u} [Field κ] {X Y : Scheme.{u}}
    [X.Over (Spec (.of κ))] [Y.Over (Spec (.of κ))]
    [IsSeparated (X ↘ Spec (.of κ))] [IsProper (Y ↘ Spec (.of κ))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of κ))] [IsAffineHom j]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (n : ℕ) (hn : n ≤ 1) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom).obj
        ((Scheme.Modules.cechModuleComplex (j ≫ (X ↘ Spec (.of κ)))
          ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)).homology n) ≃ₗ[κ]
      ((Scheme.Modules.pullback j).obj M).H n :=
  LinearEquiv.ofBijective (nativeCechFaceHFieldLinearMap (k := κ) j M U affineU coverU n) (by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst n
      exact bijective_nativeCechFaceHFieldLinearMap_zero j M U affineU coverU
    · have he : n = 1 := by omega
      subst n
      exact bijective_nativeCechFaceHFieldLinearMap_one j M U affineU coverU)

/-- Low-degree packaging keeps the same stored forward map; it does not
replace θ by an equally ranked isomorphism. -/
theorem nativeCechFaceHFieldLinearEquiv_low_apply
    {κ : Type u} [Field κ] {X Y : Scheme.{u}}
    [X.Over (Spec (.of κ))] [Y.Over (Spec (.of κ))]
    [IsSeparated (X ↘ Spec (.of κ))] [IsProper (Y ↘ Spec (.of κ))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of κ))] [IsAffineHom j]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (n : ℕ) (hn : n ≤ 1)
    (z : (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom).obj
      ((Scheme.Modules.cechModuleComplex (j ≫ (X ↘ Spec (.of κ)))
        ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)).homology n)) :
    nativeCechFaceHFieldLinearEquiv_low (κ := κ) j M U affineU coverU n hn z =
      nativeCechFaceHFieldLinearMap (k := κ) j M U affineU coverU n z := rfl

/-- Canonical model-to-native-H comparison on the ACTUAL field fibre. Raw
extension occurs before homology. The original κ action is never reconstructed. -/
def retainedCechModelHFieldLinearEquiv
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X XB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (P : CochainComplex (ModuleCat.{u} S) ℤ)
    (eC : P ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) S)).obj
      (Scheme.Modules.cechModuleComplex q M U))
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eC))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β)) (n : ℕ) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    ((scalarComplexFunctor β).obj P).homology n ≃ₗ[κ] ((Scheme.Modules.pullback a).obj M).H n := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  haveI : IsProper qB := MorphismProperty.of_isPullback (P := @IsProper) HC inferInstance
  haveI : IsSeparated (XB ↘ Spec (.of κ)) := inferInstanceAs (IsSeparated qB)
  haveI : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) HC.flip inferInstance
  let MB := (Scheme.Modules.pullback a).obj M
  let UB := fun i ↦ a ⁻¹ᵁ U i
  have affineB : ∀ i, IsAffineOpen (UB i) := fun i ↦ (affineU i).preimage a
  have coverB : ⨆ i, UB i = ⊤ := by
    rw [← a.preimage_iSup, coverU, a.preimage_top]
  let CB := Scheme.Modules.cechModuleComplex qB MB UB
  let EC := retainedGeometricCechIso R S q M U affineU κ β qB a HC
  exact (retainedFieldHomologyIso (algebraMap Γ(Spec (.of R), ⊤) S) (.of κ) β
      (Scheme.Modules.cechModuleComplex q M U) P eC CB EC universal (n : ℤ)).toLinearEquiv.trans
    (nativeCechHFieldLinearEquiv (k := κ) MB UB affineB coverB n)

/-- The ACTUAL target field equivalence attached to eX, with the inverse
scalar face coefficient/cover comparison and native low-degree H map. -/
def retainedCechModelFaceHFieldLinearEquiv
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X Y XB YB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : Y ⟶ X) [IsAffineHom j] [IsProper (j ≫ q)]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (PX : CochainComplex (ModuleCat.{u} S) ℤ)
    (eX : PX ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) S)).obj
      (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i)))
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eX))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β))
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) (retainedFieldBasePoint R S κ β))
    (square : jB ≫ a = b ≫ j) (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jB ≫ qB⟩
    ((scalarComplexFunctor β).obj PX).homology n ≃ₗ[κ]
      ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M)).H n := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jB ≫ qB⟩
  obtain ⟨properB, properD, affineJ⟩ := retainedFieldFace_geometry R S q j κ β qB a b jB HC HD square
  haveI : IsProper qB := properB
  haveI : IsSeparated (XB ↘ Spec (.of κ)) := inferInstanceAs (IsSeparated qB)
  haveI : IsProper (jB ≫ qB) := properD
  haveI : IsProper (YB ↘ Spec (.of κ)) := inferInstanceAs (IsProper (jB ≫ qB))
  haveI : IsAffineHom jB := affineJ
  haveI : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) HC.flip inferInstance
  haveI : jB.IsOver (Spec (.of κ)) := ⟨rfl⟩
  let MB := (Scheme.Modules.pullback a).obj M
  let UB := fun i ↦ a ⁻¹ᵁ U i
  have affineB : ∀ i, IsAffineOpen (UB i) := fun i ↦ (affineU i).preimage a
  have coverB : ⨆ i, UB i = ⊤ := by rw [← a.preimage_iSup, coverU, a.preimage_top]
  let DB := Scheme.Modules.cechModuleComplex (jB ≫ qB) ((Scheme.Modules.pullback jB).obj MB)
    (fun i ↦ jB ⁻¹ᵁ UB i)
  let ED := retainedGeometricFaceCechIso R S q j M U affineU κ β qB a b jB HD square
  exact (retainedFieldHomologyIso (algebraMap Γ(Spec (.of R), ⊤) S) (.of κ) β
      (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i)) PX eX DB ED universal (n : ℤ)).toLinearEquiv.trans
    (nativeCechFaceHFieldLinearEquiv_low (κ := κ) jB MB UB affineB coverB n hn)

/-- The SAME scalar ψ now commutes with the EXISTING native field-face
H.pullback. Every ring map β is allowed; residues are not assumed flat. -/
theorem retainedCechModelFaceHFieldLinearEquiv_square
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X Y XB YB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : Y ⟶ X) [IsAffineHom j] [IsProper (j ≫ q)]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (P PX : CochainComplex (ModuleCat.{u} S) ℤ) (ψ : P ⟶ PX)
    (eC : P ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) S)).obj
      (Scheme.Modules.cechModuleComplex q M U))
    (eX : PX ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) S)).obj
      (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i)))
    (h : Homotopy (ψ ≫ eX) (eC ≫ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) S)).map
      (cechModuleFaceMap q j M U)))
    (uC : ∀ (B : Type u) [CommRing B] [Algebra S B], QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eC))
    (uX : ∀ (B : Type u) [CommRing B] [Algebra S B], QuasiIso ((scalarComplexFunctor (algebraMap S B)).map eX))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β))
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) (retainedFieldBasePoint R S κ β))
    (square : jB ≫ a = b ≫ j) (n : ℕ) (hn : n ≤ 1)
    (z : ((scalarComplexFunctor β).obj P).homology n) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jB ≫ qB⟩
    retainedCechModelFaceHFieldLinearEquiv R S q j M U affineU coverU PX eX uX
        κ β qB a b jB HC HD square n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) (n : ℤ) z) =
      Scheme.Modules.H.pullback jB ((Scheme.Modules.pullback a).obj M) n
        (retainedCechModelHFieldLinearEquiv R S q M U affineU coverU P eC uC κ β qB a HC n z) := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jB ≫ qB⟩
  obtain ⟨properB, properD, affineJ⟩ := retainedFieldFace_geometry R S q j κ β qB a b jB HC HD square
  haveI : IsProper qB := properB
  haveI : IsSeparated (XB ↘ Spec (.of κ)) := inferInstanceAs (IsSeparated qB)
  haveI : IsProper (jB ≫ qB) := properD
  haveI : IsProper (YB ↘ Spec (.of κ)) := inferInstanceAs (IsProper (jB ≫ qB))
  haveI : IsAffineHom jB := affineJ
  haveI : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) HC.flip inferInstance
  haveI : jB.IsOver (Spec (.of κ)) := ⟨rfl⟩
  let α := algebraMap Γ(Spec (.of R), ⊤) S
  let C := Scheme.Modules.cechModuleComplex q M U
  let D := Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
    (fun i ↦ j ⁻¹ᵁ U i)
  let MB := (Scheme.Modules.pullback a).obj M
  let UB := fun i ↦ a ⁻¹ᵁ U i
  let CB := Scheme.Modules.cechModuleComplex qB MB UB
  let DB := Scheme.Modules.cechModuleComplex (jB ≫ qB) ((Scheme.Modules.pullback jB).obj MB)
    (fun i ↦ jB ⁻¹ᵁ UB i)
  let EC := retainedGeometricCechIso R S q M U affineU κ β qB a HC
  let ED := retainedGeometricFaceCechIso R S q j M U affineU κ β qB a b jB HD square
  let ΦB := cechModuleFaceMap qB jB MB UB
  let eHC := retainedFieldHomologyIso α (.of κ) β C P eC CB EC uC (n : ℤ)
  let eHX := retainedFieldHomologyIso α (.of κ) β D PX eX DB ED uX (n : ℤ)
  have hCat : HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) (n : ℤ) ≫ eHX.hom =
      eHC.hom ≫ (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of κ)).inv.hom).map
        (HomologicalComplex.homologyMap ΦB (n : ℤ)) :=
    retainedFieldHomologyIso_face_square α (.of κ) β (cechModuleFaceMap q j M U) ψ eC eX h
      uC uX ΦB EC ED (retainedGeometricCechIso_face_square R S q j M U affineU κ β qB a b jB HC HD square) (n : ℤ)
  have hElem : eHX.hom
      (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) (n : ℤ) z) =
      HomologicalComplex.homologyMap ΦB (n : ℤ) (eHC.hom z) :=
    ConcreteCategory.congr_hom hCat z
  have affineB : ∀ i, IsAffineOpen (UB i) := fun i ↦ (affineU i).preimage a
  have coverB : ⨆ i, UB i = ⊤ := by rw [← a.preimage_iSup, coverU, a.preimage_top]
  change nativeCechFaceHFieldLinearMap (k := κ) jB MB UB affineB coverB n
      (eHX.hom (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψ) (n : ℤ) z)) =
    Scheme.Modules.H.pullback jB MB n
      (nativeCechHFieldLinearEquiv (k := κ) MB UB affineB coverB n (eHC.hom z))
  exact (congrArg (nativeCechFaceHFieldLinearMap (k := κ) jB MB UB affineB coverB n) hElem).trans
    (nativeCechFaceHFieldLinearMap_square jB MB UB affineB coverB n (eHC.hom z))

end ZInQ.Contrib.CloudR2Poincare.L1
