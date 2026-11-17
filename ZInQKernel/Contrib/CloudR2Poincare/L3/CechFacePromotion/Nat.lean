import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFaceBaseChangeChains

/-!
# E4: concrete-joint bisection of the face/target and left-unit calculations

E3's passing declarations and every existing statement header are preserved.
The remaining concrete face/target instantiation is split into separately named
composition, target evaluation and face evaluation equations. The dependent
left-unit calculation is likewise split into BC composition, face evaluation
and section transport. Each joint states the next exact concrete term. A named
literal equality exposes the target construction without changing its data.
No numeric option, new public premise, rank/model fact or oracle is added.
This is source-only; the parent owns the native probe and acceptance.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Composition evaluated with abstract complexes and modules. No concrete
Čech complex or coefficient structure is unfolded in this proof. -/
theorem chain_comp_component_apply {R : Type u} [CommRing R]
    {C D E : CochainComplex (ModuleCat.{u} R) ℕ}
    (phi : C ⟶ D) (psi : D ⟶ E) (n : ℕ) (x : C.X n) :
    (phi ≫ psi).f n x = psi.f n (phi.f n x) := by
  rw [HomologicalComplex.comp_f, ModuleCat.comp_apply]

/-- Unit-tensor extensionality at the SAME scalar-extension module object.
The native equality of the two tensor presentations is transported explicitly. -/
theorem scalarModule_hom_ext_unit {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] {C : ModuleCat.{u} R} {D : ModuleCat.{u} B}
    (phi psi : (ModuleCat.extendScalars (algebraMap R B)).obj C ⟶ D)
    (h : ∀ c : C,
      phi (ModuleCat.tensorEquivExtendScalars R B C ((1 : B) ⊗ₜ c)) =
        psi (ModuleCat.tensorEquivExtendScalars R B C ((1 : B) ⊗ₜ c))) : phi = psi := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro c
  have et := ModuleCat.tensorEquivExtendScalars_tmul R B C (1 : B) c
  exact (congrArg (fun x : (ModuleCat.extendScalars (algebraMap R B)).obj C => phi x) et).symm.trans
    ((h c).trans
      (congrArg (fun x : (ModuleCat.extendScalars (algebraMap R B)).obj C => psi x) et))

/-- The abstract complex version of the preceding same-object extensionality. -/
theorem scalarComplex_hom_ext_unit {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] {C : CochainComplex (ModuleCat.{u} R) ℕ}
    {D : CochainComplex (ModuleCat.{u} B) ℕ}
    (phi psi : ((ModuleCat.extendScalars (algebraMap R B)).mapHomologicalComplex (.up ℕ)).obj C ⟶ D)
    (h : ∀ n (c : C.X n),
      phi.f n (ModuleCat.tensorEquivExtendScalars R B (C.X n) ((1 : B) ⊗ₜ c)) =
        psi.f n (ModuleCat.tensorEquivExtendScalars R B (C.X n) ((1 : B) ⊗ₜ c))) : phi = psi := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact scalarModule_hom_ext_unit (phi.f n) (psi.f n) (h n)

/-- Project the actual coefficient chain map in one degree and tuple, using the
already-proved coefficient cochain formula. -/
theorem cechCoefficientMapNat_component_apply
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    (L1.cechModuleCoefficientMapNat q φ U).f n c t = φ.app (⨅ l, U (t l)) (c t) := by
  exact L1.cechCoefficientCochainLinearMap_apply q φ U n c t

/-- Only the hom component of the actual coefficient iso is projected. -/
theorem cechCoefficientIsoNat_component_apply
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (e : M ≅ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    (L1.cechModuleCoefficientIsoNat q e U).hom.f n c t = e.hom.app (⨅ l, U (t l)) (c t) :=
  cechCoefficientMapNat_component_apply q e.hom U n c t

/-- One component of the actual face map is its existing normalized section
pullback, without unfolding any other field of the complex. -/
theorem cechFaceMapNat_component_apply
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    (L1.cechModuleFaceMapNat q j M U).f n c t =
      L1.faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (L1.face_preimage_iInf j (fun l ↦ U (t l)))
        (Scheme.Modules.pullbackSection j (c t)) :=
  L1.cechFaceCochainLinearMap_apply q j M U n c t

/-- Native scalar extension on a unit pure tensor uses the same original face
component. This uses the existing tensor naturality and its pure-tensor law. -/
theorem extendScalars_face_component_unit_tensor
    {X Y S T : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) :
    (ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).map
      ((L1.cechModuleFaceMapNat q j M U).f n)
      (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) =
    ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
      ((Scheme.Modules.cechModuleComplexNat (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i)).X n)
      ((1 : Γ(T, ⊤)) ⊗ₜ ((L1.cechModuleFaceMapNat q j M U).f n c)) := by
  rw [ModuleCat.tensorEquivExtendScalars_naturality, LinearMap.baseChange_tmul]

/-- A coefficient/cover target evaluated with ALL coefficients, covers,
isomorphisms and equality proofs as variables. The explicit target-hom equation
is only an isomorphism projection; concrete targets instantiate it below. -/
theorem coefficientCover_targetIsoNat_component
    {Z S : Scheme.{u}} (q : Z ⟶ S) {N N' : Z.Modules} (e : N ≅ N')
    {ι : Type u} (V W : ι → Z.Opens) (h : V = W)
    (target : Scheme.Modules.cechModuleComplexNat q N V ≅
      Scheme.Modules.cechModuleComplexNat q N' W)
    (hTarget : target.hom = (L1.cechModuleCoefficientIsoNat q e V).hom ≫
      (L1.cechModuleCoverEqIsoNat q N' h).hom)
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q N V).X n)
    (t : Fin (n + 1) → ι) :
    target.hom.f n c t =
      L1.faceOpenEqLinearEquiv q N'
        (congrArg (fun U : ι → Z.Opens ↦ ⨅ l, U (t l)) h)
        (e.hom.app (⨅ l, V (t l)) (c t)) := by
  have homEquation := congrArg (fun phi => phi.f n c t) hTarget
  have compEquation := congrArg (fun d => d t)
    (chain_comp_component_apply (L1.cechModuleCoefficientIsoNat q e V).hom
      (L1.cechModuleCoverEqIsoNat q N' h).hom n c)
  have coverEquation := L1.cechModuleCoverEqIsoNat_hom_f_apply q N' h n
    ((L1.cechModuleCoefficientIsoNat q e V).hom.f n c) t
  have coefficientEquation := cechCoefficientIsoNat_component_apply q e V n c t
  exact homEquation.trans (compEquation.trans (coverEquation.trans
    (congrArg (L1.faceOpenEqLinearEquiv q N'
      (congrArg (fun U : ι → Z.Opens ↦ ⨅ l, U (t l)) h)) coefficientEquation)))

/-- The abstract coefficient/cover construction itself satisfies the preceding
formula; this instance still keeps e, V, W and h as arbitrary variables. -/
theorem coefficientCoverIsoNat_component
    {Z S : Scheme.{u}} (q : Z ⟶ S) {N N' : Z.Modules} (e : N ≅ N')
    {ι : Type u} (V W : ι → Z.Opens) (h : V = W)
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q N V).X n)
    (t : Fin (n + 1) → ι) :
    ((L1.cechModuleCoefficientIsoNat q e V) ≪≫
      (L1.cechModuleCoverEqIsoNat q N' h)).hom.f n c t =
      L1.faceOpenEqLinearEquiv q N'
        (congrArg (fun U : ι → Z.Opens ↦ ⨅ l, U (t l)) h)
        (e.hom.app (⨅ l, V (t l)) (c t)) :=
  coefficientCover_targetIsoNat_component q e V W h
    ((L1.cechModuleCoefficientIsoNat q e V) ≪≫ (L1.cechModuleCoverEqIsoNat q N' h))
    (Iso.trans_hom _ _) n c t

/-- The face step followed by an arbitrary coefficient/cover target. Every
coefficient, cover, target iso and target-hom equation remains a variable until
the actual face square is instantiated. -/
theorem face_coefficientCover_targetIsoNat_component
    {Z Y S : Scheme.{u}} (q : Z ⟶ S) (j : Y ⟶ Z) (N : Z.Modules)
    {N' : Y.Modules} (e : (Scheme.Modules.pullback j).obj N ≅ N')
    {ι : Type u} (V : ι → Z.Opens) (W : ι → Y.Opens)
    (h : (fun i ↦ j ⁻¹ᵁ V i) = W)
    (target : Scheme.Modules.cechModuleComplexNat (j ≫ q)
      ((Scheme.Modules.pullback j).obj N) (fun i ↦ j ⁻¹ᵁ V i) ≅
      Scheme.Modules.cechModuleComplexNat (j ≫ q) N' W)
    (hTarget : target.hom =
      (L1.cechModuleCoefficientIsoNat (j ≫ q) e (fun i ↦ j ⁻¹ᵁ V i)).hom ≫
        (L1.cechModuleCoverEqIsoNat (j ≫ q) N' h).hom)
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q N V).X n)
    (t : Fin (n + 1) → ι) :
    (L1.cechModuleFaceMapNat q j N V ≫ target.hom).f n c t =
      L1.faceOpenEqLinearEquiv (j ≫ q) N'
        (congrArg (fun U : ι → Y.Opens ↦ ⨅ l, U (t l)) h)
        (e.hom.app (⨅ l, j ⁻¹ᵁ V (t l))
          (L1.faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj N)
            (L1.face_preimage_iInf j (fun l ↦ V (t l)))
            (Scheme.Modules.pullbackSection j (c t)))) := by
  have compEquation := congrArg (fun d => d t)
    (chain_comp_component_apply (L1.cechModuleFaceMapNat q j N V) target.hom n c)
  have targetEquation := coefficientCover_targetIsoNat_component (j ≫ q) e
    (fun i ↦ j ⁻¹ᵁ V i) W h target hTarget n
    ((L1.cechModuleFaceMapNat q j N V).f n c) t
  have faceEquation := cechFaceMapNat_component_apply q j N V n c t
  exact compEquation.trans (targetEquation.trans
    (congrArg
      (fun s : Scheme.Modules.sectionsModule (j ≫ q)
        ((Scheme.Modules.pullback j).obj N) (⨅ l, j ⁻¹ᵁ V (t l)) =>
        L1.faceOpenEqLinearEquiv (j ≫ q) N'
          (congrArg (fun U : ι → Y.Opens ↦ ⨅ l, U (t l)) h)
          (e.hom.app (⨅ l, j ⁻¹ᵁ V (t l)) s)) faceEquation))

/-- Abstract precomposition of a known component formula. The BC arrow, face
arrow, target arrow, complexes, projections and section functions are VARIABLES.
The two input equations are discharged by actual native evaluations at each
geometric instantiation; no square hypothesis enters a public geometric theorem. -/
theorem chain_left_component_of_projection
    {R : Type u} [CommRing R]
    {C D E F : CochainComplex (ModuleCat.{u} R) ℕ}
    (bc : C ⟶ D) (face : D ⟶ E) (target : E ⟶ F)
    (n : ℕ) (x : C.X n) {A B : Type u}
    (project : D.X n → A) (evaluate : F.X n → B) (result : A → B)
    (hFace : ∀ y : D.X n, evaluate ((face ≫ target).f n y) = result (project y))
    (s : A) (hBC : project (bc.f n x) = s) :
    evaluate ((bc ≫ face ≫ target).f n x) = result s := by
  have compEquation := chain_comp_component_apply bc (face ≫ target) n x
  exact (congrArg evaluate compEquation).trans
    ((hFace (bc.f n x)).trans (congrArg result hBC))

/-- The actual target hom is projected at the arrow level. This is only the
native Iso.trans_hom equation, not simplification of the target definition. -/
theorem nativeFaceBaseChangeCechTargetIsoNat_hom
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

/-- The target coefficient/cover map evaluated in one component. Every stage
is composed as an equality in a fixed section/cochain type, without Eq.mpr
casts induced by unfolding the entire target and complex definitions. -/
theorem nativeFaceBaseChangeCechTargetIsoNat_hom_f_apply
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat (jB ≫ qB)
      ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
      (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i)).X n) (t : Fin (n + 1) → ι) :
    (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom.f n c t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l)) (c t)) := by
  exact coefficientCover_targetIsoNat_component (jB ≫ qB)
    (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
    (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) (fun i ↦ b ⁻¹ᵁ j ⁻¹ᵁ U i)
    (L1.nativeFaceBaseChange_cover_eq j a b jB square U)
    (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U)
    (nativeFaceBaseChangeCechTargetIsoNat_hom qB j a b jB square M U) n c t

/-- Literal equality of the specified target data with its coefficient/cover
construction. This is an explicit named unfolding boundary, not a budget change. -/
theorem nativeFaceBaseChangeCechTargetIsoNat_eq
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U =
      L1.cechModuleCoefficientIsoNat (jB ≫ qB)
        (L1.nativeFaceBaseChangeCoefficientIso j a b jB square M)
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) ≪≫
      L1.cechModuleCoverEqIsoNat (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (L1.nativeFaceBaseChange_cover_eq j a b jB square U) := rfl

/-- Bisection A: only the concrete face/target composition joint. The result is
written exactly as the input to the next concrete target-evaluation step. -/
theorem baseChangedFace_comp_component
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat qB ((Scheme.Modules.pullback a).obj M)
      (fun i ↦ a ⁻¹ᵁ U i)).X n) (t : Fin (n + 1) → ι) :
    ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
        (fun i ↦ a ⁻¹ᵁ U i) ≫
      (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n c) t =
      (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom.f n
        ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i)).f n c) t := by
  exact congrArg (fun d => d t)
    (chain_comp_component_apply
      (L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
        (fun i ↦ a ⁻¹ᵁ U i))
      (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom n c)

/-- Bisection B: the E3 kernel-passing target evaluator instantiated only at the
actual face component value. Its result retains that exact value syntactically. -/
theorem baseChangedFace_target_component
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat qB ((Scheme.Modules.pullback a).obj M)
      (fun i ↦ a ⁻¹ᵁ U i)).X n) (t : Fin (n + 1) → ι) :
    (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom.f n
        ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i)).f n c) t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
            (fun i ↦ a ⁻¹ᵁ U i)).f n c t)) := by
  exact nativeFaceBaseChangeCechTargetIsoNat_hom_f_apply qB j a b jB square M U n
    ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
      (fun i ↦ a ⁻¹ᵁ U i)).f n c) t

/-- Bisection C: only the concrete face-component/pullback joint, before its
value is supplied to the coefficient and cover maps. -/
theorem baseChangedFace_pullback_component
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat qB ((Scheme.Modules.pullback a).obj M)
      (fun i ↦ a ⁻¹ᵁ U i)).X n) (t : Fin (n + 1) → ι) :
    (L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
        (fun i ↦ a ⁻¹ᵁ U i)).f n c t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
        (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
        (Scheme.Modules.pullbackSection jB (c t)) := by
  exact cechFaceMapNat_component_apply qB jB ((Scheme.Modules.pullback a).obj M)
    (fun i ↦ a ⁻¹ᵁ U i) n c t

/-- The chain-map component is the actual face pullback followed by only the
canonical coefficient and cover transports. -/
theorem baseChangedFace_targetIso_f_apply
    {X Y XB YB T : Scheme.{u}} (qB : XB ⟶ T)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (square : jB ≫ a = b ≫ j) (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat qB ((Scheme.Modules.pullback a).obj M)
      (fun i ↦ a ⁻¹ᵁ U i)).X n) (t : Fin (n + 1) → ι) :
    ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
        (fun i ↦ a ⁻¹ᵁ U i) ≫
      (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n c) t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB (c t)))) := by
  have hComp := baseChangedFace_comp_component qB j a b jB square M U n c t
  have hTarget := baseChangedFace_target_component qB j a b jB square M U n c t
  have hFace := baseChangedFace_pullback_component qB j a b jB square M U n c t
  exact hComp.trans (hTarget.trans
    (congrArg
      (fun s : Scheme.Modules.sectionsModule (jB ≫ qB)
        ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
        (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l)) =>
        L1.faceOpenEqLinearEquiv (jB ≫ qB)
          ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
          (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
            (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
          ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
            (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l)) s)) hFace))

/-- Native BC on one unit tensor, with scalar action eliminated in its fixed
sectionsModule type rather than by simplification of a whole chain equality. -/
theorem nativeBC_unit_tensor_section
    {X XB S T : Scheme.{u}} {q : X ⟶ S} {qB : XB ⟶ T} {g : T ⟶ S} {a : XB ⟶ X}
    (HC : IsPullback a qB q g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t =
      L1.faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M)
        (L1.face_preimage_iInf a (fun l ↦ U (t l)))
        (Scheme.Modules.pullbackSection a (c t)) := by
  have hBC := L1.nativeCechBaseChangeIsoNat_hom_f_tensor_apply HC M hg U affineC n (1 : Γ(T, ⊤)) c t
  have hOne : (1 : Γ(T, ⊤)) •
      (show Scheme.Modules.sectionsModule qB ((Scheme.Modules.pullback a).obj M)
        (a ⁻¹ᵁ (⨅ l, U (t l))) from Scheme.Modules.pullbackSection a (c t)) =
      (show Scheme.Modules.sectionsModule qB ((Scheme.Modules.pullback a).obj M)
        (a ⁻¹ᵁ (⨅ l, U (t l))) from Scheme.Modules.pullbackSection a (c t)) := one_smul _ _
  exact hBC.trans (congrArg
    (L1.faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M)
      (L1.face_preimage_iInf a (fun l ↦ U (t l)))) hOne)

/-- MapHomologicalComplex is projected once, before applying the native
scalar-extension tensor law. The domain is exactly the scalar-extension object. -/
theorem mappedFace_unit_tensor_component
    {X Y S T : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) :
    (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex (.up ℕ)).map
        (L1.cechModuleFaceMapNat q j M U)).f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) =
      ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((Scheme.Modules.cechModuleComplexNat (j ≫ q) ((Scheme.Modules.pullback j).obj M)
          (fun i ↦ j ⁻¹ᵁ U i)).X n)
        ((1 : Γ(T, ⊤)) ⊗ₜ ((L1.cechModuleFaceMapNat q j M U).f n c)) := by
  rw [Functor.mapHomologicalComplex_map_f]
  exact extendScalars_face_component_unit_tensor (T := T) q j M U n c

/-- Left bisection A: only the actual BC/face/target chain-composition joint.
The result is exactly the argument of the following face-evaluation lemma. -/
theorem cechFace_left_unit_comp
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom ≫
        L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t =
      ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n
        ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
          (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
            ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)))) t := by
  exact congrArg (fun d => d t)
    (chain_comp_component_apply
      (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom
      (L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
        (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom)
      n (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)))

/-- Left bisection B: only the actual face/target component formula at the BC
component value. No BC section reduction is performed in this joint. -/
theorem cechFace_left_unit_face
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    ((L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n
        ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
          (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
            ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)))) t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB
              ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
                (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
                  ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t)))) := by
  exact baseChangedFace_targetIso_f_apply qB j a b jB square M U n
    ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
      (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c))) t

/-- Left bisection C: only the BC section equation inside the fixed section
pullback/coefficient/cover function. No complex-composition joint is present. -/
theorem cechFace_left_unit_section
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB
              ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom.f n
                (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
                  ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t)))) =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB
              (L1.faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M)
                (L1.face_preimage_iInf a (fun l ↦ U (t l)))
                (Scheme.Modules.pullbackSection a (c t)))))) := by
  exact congrArg
    (fun s : Scheme.Modules.sectionsModule qB ((Scheme.Modules.pullback a).obj M)
      (⨅ l, a ⁻¹ᵁ U (t l)) =>
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l))
          (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB s))))
    (nativeBC_unit_tensor_section HC M hg U affineC n c t)

/-- The left composite on a unit tensor, reduced only by the named component
formula and native BC section equation. -/
theorem cechFace_baseChange_left_unit
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom ≫
        L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l)) (L1.nativeFaceBaseChange_cover_eq j a b jB square U))
        ((L1.nativeFaceBaseChangeCoefficientIso j a b jB square M).hom.app
          (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l))
          (L1.faceOpenEqLinearEquiv (jB ≫ qB)
            ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
            (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
            (Scheme.Modules.pullbackSection jB
              (L1.faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M)
                (L1.face_preimage_iInf a (fun l ↦ U (t l))) (Scheme.Modules.pullbackSection a (c t)))))) := by
  have hComp := cechFace_left_unit_comp q qB g j a b jB HC square M hg U affineC n c t
  have hFace := cechFace_left_unit_face q qB g j a b jB HC square M hg U affineC n c t
  have hSection := cechFace_left_unit_section q qB g j a b jB HC square M hg U affineC n c t
  exact hComp.trans (hFace.trans hSection)

/-- The right composite on the SAME unit tensor and scalar-extension object. -/
theorem cechFace_baseChange_right_unit
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineD : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, j ⁻¹ᵁ U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    ((((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex (.up ℕ)).map
        (L1.cechModuleFaceMapNat q j M U)) ≫
        (Scheme.Modules.cechModuleComplexNatBaseChangeIso HD ((Scheme.Modules.pullback j).obj M) hg
          (fun i ↦ j ⁻¹ᵁ U i) affineD).hom).f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t =
      L1.faceOpenEqLinearEquiv (jB ≫ qB)
        ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
        (L1.face_preimage_iInf b (fun l ↦ j ⁻¹ᵁ U (t l)))
        (Scheme.Modules.pullbackSection b
          (L1.faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M)
            (L1.face_preimage_iInf j (fun l ↦ U (t l))) (Scheme.Modules.pullbackSection j (c t)))) := by
  let face := L1.cechModuleFaceMapNat q j M U
  let mappedFace := ((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex (.up ℕ)).map face
  let BC := Scheme.Modules.cechModuleComplexNatBaseChangeIso HD ((Scheme.Modules.pullback j).obj M) hg
    (fun i ↦ j ⁻¹ᵁ U i) affineD
  let x := ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
    ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)
  have hComp := congrArg (fun d => d t) (chain_comp_component_apply mappedFace BC.hom n x)
  have hMap := mappedFace_unit_tensor_component (T := T) q j M U n c
  have hBC := nativeBC_unit_tensor_section HD ((Scheme.Modules.pullback j).obj M) hg
    (fun i ↦ j ⁻¹ᵁ U i) affineD n (face.f n c) t
  have hFace := cechFaceMapNat_component_apply q j M U n c t
  exact hComp.trans ((congrArg (fun y => BC.hom.f n y t) hMap).trans
    (hBC.trans (congrArg
      (fun s : Scheme.Modules.sectionsModule (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (⨅ l, j ⁻¹ᵁ U (t l)) =>
        L1.faceOpenEqLinearEquiv (jB ≫ qB)
          ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback j).obj M))
          (L1.face_preimage_iInf b (fun l ↦ j ⁻¹ᵁ U (t l))) (Scheme.Modules.pullbackSection b s)) hFace)))

/-- The geometric equality is now only the three named, syntactically fixed
section equations. No composite unfolding or instance-changing simplification. -/
theorem cechFace_baseChange_unit_tensor_square
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (HD : IsPullback b (jB ≫ qB) (j ≫ q) g)
    (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (affineD : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, j ⁻¹ᵁ U (t l)))
    (n : ℕ) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    ((Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom ≫
        L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom).f n
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t =
      ((((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex (.up ℕ)).map
          (L1.cechModuleFaceMapNat q j M U)) ≫
          (Scheme.Modules.cechModuleComplexNatBaseChangeIso HD ((Scheme.Modules.pullback j).obj M) hg
            (fun i ↦ j ⁻¹ᵁ U i) affineD).hom).f n
          (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
            ((Scheme.Modules.cechModuleComplexNat q M U).X n) ((1 : Γ(T, ⊤)) ⊗ₜ c)) t := by
  have hLeft := cechFace_baseChange_left_unit q qB g j a b jB HC square M hg U affineC n c t
  have hRight := cechFace_baseChange_right_unit q qB g j a b jB HD M hg U affineD n c t
  have hSection := L1.nativeFaceBaseChange_normalized_sections_square q qB j a b jB square M
    (⨅ l, U (t l)) (⨅ l, a ⁻¹ᵁ U (t l)) (⨅ l, j ⁻¹ᵁ U (t l))
    (⨅ l, jB ⁻¹ᵁ a ⁻¹ᵁ U (t l)) (⨅ l, b ⁻¹ᵁ j ⁻¹ᵁ U (t l))
    (L1.face_preimage_iInf a (fun l ↦ U (t l)))
    (L1.face_preimage_iInf j (fun l ↦ U (t l)))
    (L1.face_preimage_iInf jB (fun l ↦ a ⁻¹ᵁ U (t l)))
    (L1.face_preimage_iInf b (fun l ↦ j ⁻¹ᵁ U (t l)))
    (congrArg (fun V : ι → YB.Opens ↦ ⨅ l, V (t l)) (L1.nativeFaceBaseChange_cover_eq j a b jB square U)) (c t)
  exact hLeft.trans (hSection.trans hRight.symm)

/-- The actual geometric all-scalar Čech base-change square as an equality of
Nat chain maps. Both genuine finite-intersection affine hypotheses are kept;
there is deliberately no flatness assumption on g or its scalar algebra. -/
theorem cechModuleFaceMapNat_baseChange_square
    {X Y XB YB S T : Scheme.{u}} (q : X ⟶ S) (qB : XB ⟶ T) (g : T ⟶ S)
    (j : Y ⟶ X) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q g) (HD : IsPullback b (jB ≫ qB) (j ≫ q) g)
    (square : jB ≫ a = b ≫ j) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineC : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (affineD : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, j ⁻¹ᵁ U (t l))) :
    (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineC).hom ≫
        L1.cechModuleFaceMapNat qB jB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i) ≫
        (L1.nativeFaceBaseChangeCechTargetIsoNat qB j a b jB square M U).hom =
      (((ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))).mapHomologicalComplex
          (.up ℕ)).map (L1.cechModuleFaceMapNat q j M U)) ≫
        (Scheme.Modules.cechModuleComplexNatBaseChangeIso HD
          ((Scheme.Modules.pullback j).obj M) hg (fun i ↦ j ⁻¹ᵁ U i) affineD).hom := by
  exact scalarComplex_hom_ext_unit _ _
    (fun n c => funext (fun t =>
      cechFace_baseChange_unit_tensor_square q qB g j a b jB HC HD square M hg U affineC affineD n c t))

end ZInQ.Contrib.CloudR2Poincare.L3.CechFacePromotion
