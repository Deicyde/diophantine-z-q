import ZInQKernel.Contrib.CloudR2Poincare.L1.BasedScalarRank
import ZInQKernel.Contrib.CloudR2Poincare.L1.ScalarCechZeroRank
import ZInQKernel.Contrib.CloudR2Poincare.L1.NonnegativeKernelComparison

/-!
# Canonical scalar zero kernels of the retained Čech model

The actual model map is quasi-isomorphic before and after every scalar
extension. The ACTUAL Čech field-fibre zero kernel has dimension one. Thus
rank-nullity supplies constant rank for the model matrix over the reduced
coefficient ring, and the genuine scalar constant-rank theorem applies.
No sheaf/ring kernel comparison is equated by fiat.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The field-valued point of an affine scheme corresponding to a map from its global functions. -/
def fieldPointFromGlobalSections {Y : Scheme.{u}} [IsAffine Y]
    (K : Type u) [Field K] (ψ : Γ(Y, ⊤) →+* K) : Spec (.of K) ⟶ Y :=
  Spec.map (CommRingCat.ofHom ψ) ≫ Y.isoSpec.inv

/-- Its ACTUAL global-functions map is the given field embedding with the canonical ΓSpec inverse. -/
theorem fieldPointFromGlobalSections_appTop {Y : Scheme.{u}} [IsAffine Y]
    (K : Type u) [Field K] (ψ : Γ(Y, ⊤) →+* K) :
    (fieldPointFromGlobalSections K ψ).appTop.hom = (Scheme.ΓSpecIso (.of K)).inv.hom.comp ψ := by
  have h0 : Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = 𝟙 _ := by
    rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop, Scheme.toSpecΓ_isoSpec_inv]
    rfl
  have h1 : (Spec.map (CommRingCat.ofHom ψ)).appTop =
      (Scheme.ΓSpecIso Γ(Y, ⊤)).hom ≫ CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (.of K)).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (Y.isoSpec.inv.appTop ≫ (Spec.map (CommRingCat.ofHom ψ)).appTop).hom = _
  rw [h1, ← Category.assoc, ← Category.assoc, h0, Category.id_comp]
  rfl

/-- Scalar kernels of the ACTUAL retained map have rank one on all field tests;
this is dimension information derived through the ACTUAL universal map. -/
theorem retainedModel_kernel_field_dimension_one
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (S : Type u) [CommRing S] [Algebra Γ(Y, ⊤) S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) [P.IsStrictlyGE 0]
    (φ : P ⟶ ((ModuleCat.extendScalars (algebraMap Γ(Y, ⊤) S)).mapHomologicalComplex _).obj
      (Scheme.Modules.cechModuleComplex f M U))
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso (((ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex _).map φ))
    (K : Type u) [Field K] (ψ : S →+* K) :
    let ν : S →+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.comp ψ
    Module.finrank Γ(Spec (.of K), ⊤)
      (kernel ((ModuleCat.extendScalars ν).map (P.d 0 1)) : ModuleCat.{u} Γ(Spec (.of K), ⊤)) = 1 := by
  let A := Γ(Y, ⊤)
  let B := Γ(Spec (.of K), ⊤)
  let α : A →+* S := algebraMap A S
  let ν : S →+* B := (Scheme.ΓSpecIso (.of K)).inv.hom.comp ψ
  letI : Algebra S B := ν.toAlgebra
  let β : A →+* B := ν.comp α
  letI : Algebra A B := β.toAlgebra
  let E := ModuleCat.extendScalars α
  let F := ModuleCat.extendScalars ν
  let H := ModuleCat.extendScalars β
  let C := Scheme.Modules.cechModuleComplex f M U
  haveI : QuasiIso ((F.mapHomologicalComplex _).map φ) := universal B
  have negP : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X (-1)) :=
    F.map_isZero (P.isZero_of_isStrictlyGE 0 (-1) (by omega))
  have negC : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((E.mapHomologicalComplex _).obj C)).X (-1)) :=
    F.map_isZero (E.map_isZero (C.isZero_of_isStrictlyGE 0 (-1) (by omega)))
  let φ' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ
  haveI := isIso_kernelMap_zeroInt_of_quasiIso φ' negP negC
  let kφ := asIso (kernel.map
    (((F.mapHomologicalComplex _).obj P).d 0 1)
    (((F.mapHomologicalComplex _).obj ((E.mapHomologicalComplex _).obj C)).d 0 1)
    (φ'.f 0) (φ'.f 1) (φ'.comm 0 1).symm)
  let assoc := ModuleCat.extendScalarsComp α ν
  let kα := kernel.mapIso ((E ⋙ F).map (C.d 0 1)) (H.map (C.d 0 1))
    (assoc.app (C.X 0)).symm (assoc.app (C.X 1)).symm (assoc.inv.naturality (C.d 0 1))
  let g := fieldPointFromGlobalSections K (ψ.comp α)
  have hg : algebraMap A B = g.appTop.hom := by
    exact (fieldPointFromGlobalSections_appTop K (ψ.comp α)).symm
  have hc := finrank_scalarCech_zeroKernel_field_eq_one f M hM U hcover hU K g hg
  exact (kφ ≪≫ kα).toLinearEquiv.finrank_eq.trans hc

/-- The P-side canonical scalar zero-kernel comparison is an ACTUAL isomorphism,
from the actual retained Čech map and the proved reduced-ring constant-rank theorem. -/
theorem isIso_retainedModel_scalarKernelComparison
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (S : Type u) [CommRing S] [_root_.IsReduced S] [Algebra Γ(Y, ⊤) S]
    (P : CochainComplex (ModuleCat.{u} S) ℤ) [P.IsStrictlyGE 0]
    {m n : Type u} [Fintype m] [Fintype n]
    (b0 : Module.Basis n S (P.X 0)) (b1 : Module.Basis m S (P.X 1))
    (φ : P ⟶ ((ModuleCat.extendScalars (algebraMap Γ(Y, ⊤) S)).mapHomologicalComplex _).obj
      (Scheme.Modules.cechModuleComplex f M U))
    (universal : ∀ (B : Type u) [CommRing B] [Algebra S B],
      QuasiIso (((ModuleCat.extendScalars (algebraMap S B)).mapHomologicalComplex _).map φ))
    (K : Type u) [Field K] (ψ : S →+* K) :
    IsIso (kernelComparison (P.d 0 1) (ModuleCat.extendScalars ψ)) := by
  classical
  let A := LinearMap.toMatrix b0 b1 (P.d 0 1).hom
  have hr : ∀ (B : Type u) [Field B] (β : S →+* B), (A.map β).rank = Fintype.card n - 1 := by
    intro B _ β
    let T := Γ(Spec (.of B), ⊤)
    letI : Field T := (Scheme.isField_Γ_Spec (Field.toIsField B)).toField
    let ν : S →+* T := (Scheme.ΓSpecIso (.of B)).inv.hom.comp β
    letI : Algebra S T := ν.toAlgebra
    have hd := retainedModel_kernel_field_dimension_one f M hM U hcover hU S P φ universal B β
    have hn := scalar_matrix_rank_add_kernel_finrank S T b0 b1 (P.d 0 1)
    change (A.map ν).rank + Module.finrank T
      (kernel ((ModuleCat.extendScalars ν).map (P.d 0 1)) : ModuleCat.{u} T) = Fintype.card n at hn
    change Module.finrank T
      (kernel ((ModuleCat.extendScalars ν).map (P.d 0 1)) : ModuleCat.{u} T) = 1 at hd
    rw [hd] at hn
    have hrmap := rank_map_field_embedding (A.map β) (Scheme.ΓSpecIso (.of B)).inv.hom
    have heq : (A.map β).map (Scheme.ΓSpecIso (.of B)).inv.hom = A.map ν := by ext i j; rfl
    rw [heq] at hrmap
    change (A.map ν).rank + 1 = Fintype.card n at hn
    omega
  let F := ModuleCat.extendScalars ψ
  let a : ModuleCat.of S (n → S) ⟶ ModuleCat.of S (m → S) := ModuleCat.ofHom A.mulVecLin
  let e0 := b0.equivFun.toModuleIso
  let e1 := b1.equivFun.toModuleIso
  have h : P.d 0 1 ≫ e1.hom = e0.hom ≫ a := based_morphism_matrix_square b0 b1 (P.d 0 1)
  have hc : a ≫ e1.inv = e0.inv ≫ P.d 0 1 := by
    apply (cancel_mono e1.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  exact isIso_kernelComparison_of_universal_model_map F a (P.d 0 1) e0.inv e1.inv hc
    (by infer_instance) (by infer_instance)
    (isIso_matrix_kernelComparison_of_constant_fieldRank S A (Fintype.card n - 1) hr K ψ)

end ZInQ.Contrib.CloudR2Poincare.L1
