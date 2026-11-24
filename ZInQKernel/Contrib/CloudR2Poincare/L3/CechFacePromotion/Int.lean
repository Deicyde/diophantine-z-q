import ZInQKernel.Contrib.CloudR2Poincare.L3.CechFacePromotion.Nat
import ZInQKernel.Contrib.CloudR2Poincare.L3.CechFacePromotion.Extension

/-!
# E2 original-integer extension using fixed arrow equations

The skipped consumer contained the same whole-target definition simplification
and simpa-of-instance-heavy equality that failed in Nat. This edition projects
one coefficient/cover/BC arrow at a time and composes native extendMap equations.
All existing headers and the actual target isomorphism data are unchanged.
The import lines remain available for the parent's source-staging rewrite.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Only the hom projection of the original integer coefficient iso. -/
theorem integerCoefficientIso_hom_extend
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (e : M ≅ N)
    {ι : Type u} (U : ι → X.Opens) :
    (L1.cechModuleCoefficientIso q e U).hom =
      HomologicalComplex.extendMap (L1.cechModuleCoefficientIsoNat q e U).hom
        ComplexShape.embeddingUpNat := rfl

/-- Only the hom projection of the original integer equality-of-cover iso. -/
theorem integerCoverIso_hom_extend
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u}
    {U V : ι → X.Opens} (h : U = V) :
    (L1.cechModuleCoverEqIso q M h).hom =
      HomologicalComplex.extendMap (L1.cechModuleCoverEqIsoNat q M h).hom
        ComplexShape.embeddingUpNat := rfl

/-- The Nat target is projected as an arrow equation, not unfolded by simp in
an integer-complex proof motive. -/
theorem natTarget_hom_for_integer_extension
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom =
      (L1.cechModuleCoefficientIsoNat (jB ≫ qB)
        (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i)).hom ≫
      (L1.cechModuleCoverEqIsoNat (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (L1.nativeFaceBaseChange_cover_eq j a b jB square U)).hom :=
  Iso.trans_hom _ _

/-- The scalar BC hom on the original integer complex is its fixed native
mapExtendIso hom followed by the extended Nat BC hom. -/
theorem nativeIntegerBC_hom_extend
    {X XB S T : Scheme.{u}} {q : X ⟶ S} {qB : XB ⟶ T} {g : T ⟶ S} {a : XB ⟶ X}
    (HC : IsPullback a qB q g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l))) :
    (Scheme.Modules.cechModuleComplexBaseChangeIso HC M hg U affineC).hom =
      ((Scheme.Modules.cechModuleComplexNat q M U).mapExtendIso ComplexShape.embeddingUpNat
        (ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤)))).hom ≫
        HomologicalComplex.extendMap
          (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom
          ComplexShape.embeddingUpNat :=
  Iso.trans_hom _ _

/-- The integer face is exactly the extension of the specified Nat face. -/
theorem integerFaceMap_eq_extend
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    L1.cechModuleFaceMap q j M U =
      HomologicalComplex.extendMap (L1.cechModuleFaceMapNat q j M U) ComplexShape.embeddingUpNat := rfl

/-- The coefficient/cover target iso on the original integer complex, obtained
by extending precisely L1's canonical Nat target iso. -/
def nativeFaceBaseChangeCechTargetIso
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplex (jB ≫ qB)
        ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) ≅
      Scheme.Modules.cechModuleComplex (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (fun i ↦ b ⁻¹ᵁ j ⁻¹ᵁ U i) :=
  L1.cechModuleCoefficientIso (jB ≫ qB)
    (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
    (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) ≪≫
    L1.cechModuleCoverEqIso (jB ≫ qB)
      ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
      (L1.nativeFaceBaseChange_cover_eq j a b jB square U)

/-- Its actual hom map is the coefficient iso followed by equal-cover transport,
using the original integer versions, not just an unrelated extension iso. -/
theorem nativeFaceBaseChangeCechTargetIso_hom
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (nativeFaceBaseChangeCechTargetIso qB j a b jB square M U).hom =
      (L1.cechModuleCoefficientIso (jB ≫ qB)
        (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i)).hom ≫
      (L1.cechModuleCoverEqIso (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (L1.nativeFaceBaseChange_cover_eq j a b jB square U)).hom :=
  Iso.trans_hom _ _

/-- The original integer coefficient/cover map is exactly the extension of the
specified Nat target map; use named mapIso/extendMap composition equations. -/
theorem nativeFaceBaseChangeCechTargetIso_hom_extend
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (nativeFaceBaseChangeCechTargetIso qB j a b jB square M U).hom =
      HomologicalComplex.extendMap
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom
        ComplexShape.embeddingUpNat := by
  let eC := L1.cechModuleCoefficientIsoNat (jB ≫ qB)
    (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
    (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i)
  let eU := L1.cechModuleCoverEqIsoNat (jB ≫ qB)
    ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
    (L1.nativeFaceBaseChange_cover_eq j a b jB square U)
  calc
    _ = (L1.cechModuleCoefficientIso (jB ≫ qB)
          (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
          (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i)).hom ≫
        (L1.cechModuleCoverEqIso (jB ≫ qB)
          ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U)).hom :=
      nativeFaceBaseChangeCechTargetIso_hom qB j a b jB square M U
    _ = HomologicalComplex.extendMap eC.hom ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap eU.hom ComplexShape.embeddingUpNat := by
      rw [integerCoefficientIso_hom_extend, integerCoverIso_hom_extend]
    _ = HomologicalComplex.extendMap (eC.hom ≫ eU.hom) ComplexShape.embeddingUpNat :=
      (HomologicalComplex.extendMap_comp eC.hom eU.hom ComplexShape.embeddingUpNat).symm
    _ = HomologicalComplex.extendMap
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom
        ComplexShape.embeddingUpNat :=
      congrArg (fun phi => HomologicalComplex.extendMap phi ComplexShape.embeddingUpNat)
        (natTarget_hom_for_integer_extension qB j a b jB square M U).symm

/-- The same genuine all-scalar face/base-change square on the ORIGINAL ℤ-indexed
native Čech complex. There is no scalar-flatness or Nat-square hypothesis. -/
theorem cechModuleFaceMap_baseChange_square
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (HD : IsPullback b (jB ≫ qB) (j ≫ q) g)
    (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (affineD : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, j ⁻¹ᵁ U (t l))) :
    (Scheme.Modules.cechModuleComplexBaseChangeIso HC M hg U affineC).hom ≫
        L1.cechModuleFaceMap qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i) ≫
        (nativeFaceBaseChangeCechTargetIso qB j a b jB square M U).hom =
      (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex
          (.up ℤ)).map (L1.cechModuleFaceMap q j M U)) ≫
        (Scheme.Modules.cechModuleComplexBaseChangeIso HD
          ((Scheme.Modules.pullback j).obj M) hg (fun i ↦ j ⁻¹ᵁ U i) affineD).hom := by
  let C := Scheme.Modules.cechModuleComplexNat q M U
  let D := Scheme.Modules.cechModuleComplexNat (j ≫ q) ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)
  let E := ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))
  let EC := Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC
  let ED := Scheme.Modules.cechModuleComplexNatBaseChangeIso HD ((Scheme.Modules.pullback j).obj M) hg
    (fun i ↦ j ⁻¹ᵁ U i) affineD
  let face := L1.cechModuleFaceMapNat q j M U
  let faceB := L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i)
  let target := L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U
  have extendedSquare := extend_proved_Nat_square face (faceB ≫ target.hom) EC ED
    (cechModuleFaceMapNat_baseChange_square q qB g j a b jB HC HD square M hg U affineC affineD)
  calc
    _ = (C.mapExtendIso ComplexShape.embeddingUpNat E).hom ≫
        HomologicalComplex.extendMap EC.hom ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap faceB ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap target.hom ComplexShape.embeddingUpNat := by
      rw [nativeIntegerBC_hom_extend, integerFaceMap_eq_extend,
        nativeFaceBaseChangeCechTargetIso_hom_extend, Category.assoc]
    _ = (C.mapExtendIso ComplexShape.embeddingUpNat E).hom ≫
        HomologicalComplex.extendMap EC.hom ComplexShape.embeddingUpNat ≫
        HomologicalComplex.extendMap (faceB ≫ target.hom) ComplexShape.embeddingUpNat :=
      congrArg (fun phi => (C.mapExtendIso ComplexShape.embeddingUpNat E).hom ≫
        HomologicalComplex.extendMap EC.hom ComplexShape.embeddingUpNat ≫ phi)
        (HomologicalComplex.extendMap_comp faceB target.hom ComplexShape.embeddingUpNat).symm
    _ = (E.mapHomologicalComplex (.up ℤ)).map
          (HomologicalComplex.extendMap face ComplexShape.embeddingUpNat) ≫
        (D.mapExtendIso ComplexShape.embeddingUpNat E).hom ≫
        HomologicalComplex.extendMap ED.hom ComplexShape.embeddingUpNat := extendedSquare
    _ = _ := by
      rw [nativeIntegerBC_hom_extend, integerFaceMap_eq_extend]

end ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion
