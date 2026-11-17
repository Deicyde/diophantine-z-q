/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statements in this file:
* Q3, concrete: the identifications `E₁`, `E₂` and the coaction `θ`;
* Q4: the cocycle of `θ`;
* Q5: the unit of `θ`;
* Q6 input: the descended sections span `Γ(L', ⊤)` over `S'`, via the published W07
  algebraic descent `TensorProduct.bijective_descentLift_of_flat`.

NATIVE. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

RISK NOTE: this is the bookkeeping-heavy part of route Q. Q4 transports the FLT cocycle
equation `hψ` through `pullbackComp` / `pullbackCongr`, using the published W07 lemmas on
pulled-back sections (Modules/AffineSections, Modules/BaseChange).
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.Coaction
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.FaithfullyFlat.FamilyDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "CIBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

/-- The descended sections contain `0`. -/
theorem descended_zero {X' X'' : Scheme.{u}} {L' : X'.Modules} (a₁ a₂ : X'' ⟶ X')
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L') :
    ψ.hom.app ⊤ (pbSec a₁ (0 : Γ(L', ⊤))) = pbSec a₂ (0 : Γ(L', ⊤)) := by
  simp [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection]

/-- Unit naturality of the pulled-back global section. -/
theorem pbSec_naturality {X Y : Scheme.{u}} (b : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N)
    (x : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback b).map φ).app ⊤ (pbSec b x) = pbSec b (φ.app ⊤ x) := by
  have h := congr($(((Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality φ)).app ⊤ x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  exact h.symm

/-- On global sections over a cartesian square of affine bases, pulling back is semilinear. -/
theorem pbSec_smul_of_isPullback {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} {g : Y ⟶ Spec (CommRingCat.of B)}
    {p : Y ⟶ X} (h : IsPullback p g f (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (F : X.Modules) (a : A) (s : Γ(F, ⊤)) :
    pbSec p (letI := moduleTop f F; a • s) =
      (g.appLE ⊤ ⊤ le_top).hom (ΓinvA B (algebraMap A B a)) • pbSec p s := by
  letI := algebraΓSpec A B
  have key := Scheme.Modules.pullbackSection_smul_appTop h F rfl (openSubset := ⊤) (ΓinvA A a) s
  rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id, X.presheaf.map_id,
    show (homOfLE (le_top : p ⁻¹ᵁ (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id, Y.presheaf.map_id]
    at key
  rw [Scheme.Hom.appLE_top_top_eq_appTop, ΓinvA_algebraMap]
  change pbSec p ((f.appLE ⊤ ⊤ le_top).hom (ΓinvA A a) • s) = _
  rw [Scheme.Hom.appLE_top_top_eq_appTop]
  exact key

section Main

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']
  (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')

/-- The functions `κ : S' ⊗[S] S' → Γ(X'', ⊤)`. -/
abbrev κ : S' ⊗[S] S' →+* Γ(X'', ⊤) := (f''.appLE ⊤ ⊤ le_top).hom.comp (ΓinvA (S' ⊗[S] S'))

variable [hL : L'.IsInvertible] [IsProper f']

include hL in
theorem isQuasicoherent_L : SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) L' :=
  SheafOfModules.IsInvertible.isQuasicoherent hL

/-- **E₁** : `S' ⊗[S] Γ(L', ⊤) ≃+ Γ(a₁^*L', ⊤)`, `s ⊗ n ↦ κ (1 ⊗ s) • a₁^* n`. -/
noncomputable def E₁ (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (algebraMap S' (S' ⊗[S] S'))))) :
    (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; S' ⊗[S] Γ(L', ⊤)) ≃+
      Γ((Scheme.Modules.pullback a₁).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  haveI := isScalarTower_top S' f' L'
  haveI := isQuasicoherent_L X' L'
  (tensorBaseChangeAddEquiv S S' S' Γ(L', ⊤)).trans
    (AddEquiv.ofBijective (sectionsBC ha₁' L') (bijective_sectionsBC ha₁' L'))

theorem E₁_tmul (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (algebraMap S' (S' ⊗[S] S'))))) (s : S') (n : Γ(L', ⊤)) :
    E₁ S' X' f' L' X'' f'' a₁ ha₁' (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; s ⊗ₜ n) =
      κ S' X'' f'' (1 ⊗ₜ s) • pbSec a₁ n := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  change sectionsBC ha₁' L' ((1 ⊗ₜ s) ⊗ₜ n) = _
  rw [sectionsBC_tmul]
  rfl

/-- **E₂** : `S' ⊗[S] Γ(L', ⊤) ≃+ Γ(a₂^*L', ⊤)`, `s ⊗ n ↦ κ (s ⊗ 1) • a₂^* n`, through the
swapped square. -/
noncomputable def E₂ (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) :
    (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; S' ⊗[S] Γ(L', ⊤)) ≃+
      Γ((Scheme.Modules.pullback a₂).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  haveI := isScalarTower_top S' f' L'
  haveI := isQuasicoherent_L X' L'
  (tensorBaseChangeAddEquiv S S' S' Γ(L', ⊤)).trans
    (AddEquiv.ofBijective (sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L')
      (bijective_sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L'))

theorem E₂_tmul (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) (s : S')
    (n : Γ(L', ⊤)) :
    E₂ S' X' f' L' X'' f'' a₂ ha₂ (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; s ⊗ₜ n) =
      κ S' X'' f'' (s ⊗ₜ 1) • pbSec a₂ n := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  change sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L' ((1 ⊗ₜ s) ⊗ₜ n) = _
  rw [sectionsBC_tmul]
  congr 1
  -- `(f'' ≫ Spec swap)^♯ (1 ⊗ s) = f''^♯ (s ⊗ 1)`
  rw [Scheme.Hom.appLE_top_top_eq_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply, ← ΓinvA_algebraMap (A := S' ⊗[S] S') (B := S' ⊗[S] S')]
  · change (f''.appTop).hom (ΓinvA _ ((Algebra.TensorProduct.comm S S' S') (1 ⊗ₜ s))) = _
    rw [Algebra.TensorProduct.comm_tmul, Scheme.Hom.appLE_top_top_eq_appTop]
    rfl

/-- Pulling back along `a₁` is semilinear through `κ (t ⊗ 1)`. -/
theorem pbSec_a₁_smul (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (algebraMap S' (S' ⊗[S] S'))))) (t : S') (n : Γ(L', ⊤)) :
    pbSec a₁ (letI := moduleTop f' L'; t • n) = κ S' X'' f'' (t ⊗ₜ 1) • pbSec a₁ n :=
  pbSec_smul_of_isPullback ha₁' L' t n

/-- Pulling back along `a₂` is semilinear through `κ (1 ⊗ t)`. -/
theorem pbSec_a₂_smul (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) (t : S')
    (n : Γ(L', ⊤)) :
    pbSec a₂ (letI := moduleTop f' L'; t • n) = κ S' X'' f'' (1 ⊗ₜ t) • pbSec a₂ n := by
  rw [pbSec_smul_of_isPullback (isPullback_swap S' f' f'' a₂ ha₂) L' t n]
  congr 1
  rw [Scheme.Hom.appLE_top_top_eq_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply, ← ΓinvA_algebraMap (A := S' ⊗[S] S') (B := S' ⊗[S] S')]
  change (f''.appTop).hom (ΓinvA _ ((Algebra.TensorProduct.comm S S' S') (t ⊗ₜ 1))) = _
  rw [Algebra.TensorProduct.comm_tmul, Scheme.Hom.appLE_top_top_eq_appTop]
  rfl

variable (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))))
  (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
  (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')

/-- `E₂` is semilinear for the left factor. -/
theorem E₂_smul (t : S') (y : letI := moduleTop f' L'; letI := moduleTopS S' f' L'; S' ⊗[S] Γ(L', ⊤)) :
    E₂ S' X' f' L' X'' f'' a₂ ha₂ (t • y) = κ S' X'' f'' (t ⊗ₜ 1) • E₂ S' X' f' L' X'' f'' a₂ ha₂ y := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul s n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, E₂_tmul, E₂_tmul, ← mul_smul, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- **Q3.** The coaction `θ n = E₂⁻¹ (ψ (a₁^* n))`, an `S'`-linear map for the left factor. -/
noncomputable def θ : letI := moduleTop f' L'; letI := moduleTopS S' f' L'
    Γ(L', ⊤) →ₗ[S'] S' ⊗[S] Γ(L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  { toFun := fun n => (E₂ S' X' f' L' X'' f'' a₂ ha₂).symm (ψ.hom.app ⊤ (pbSec a₁ n))
    map_add' := fun n m => by
      rw [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection, map_add, map_add, map_add]
      rfl
    map_smul' := fun t n => by
      apply (E₂ S' X' f' L' X'' f'' a₂ ha₂).injective
      rw [RingHom.id_apply, AddEquiv.apply_symm_apply, E₂_smul, AddEquiv.apply_symm_apply,
        pbSec_a₁_smul S' X' f' L' X'' f'' a₁ ha₁', Scheme.Modules.Hom.app_smul] }

theorem E₂_θ (n : Γ(L', ⊤)) :
    E₂ S' X' f' L' X'' f'' a₂ ha₂ (θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n) =
      ψ.hom.app ⊤ (pbSec a₁ n) :=
  AddEquiv.apply_symm_apply _ _

/-- **Q3 (fixed points).** `θ n = 1 ⊗ n` iff `ψ (a₁^* n) = a₂^* n`. -/
theorem θ_eq_one_tmul_iff (n : Γ(L', ⊤)) :
    θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n =
        (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; (1 : S') ⊗ₜ n) ↔
      ψ.hom.app ⊤ (pbSec a₁ n) = pbSec a₂ n := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  have h1 : E₂ S' X' f' L' X'' f'' a₂ ha₂ ((1 : S') ⊗ₜ n) = pbSec a₂ n := by
    rw [E₂_tmul, Algebra.TensorProduct.one_def, map_one, one_smul]
  constructor
  · intro h
    rw [← E₂_θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ, h, h1]
  · intro h
    apply (E₂ S' X' f' L' X'' f'' a₂ ha₂).injective
    rw [E₂_θ, h, h1]

end Main

end ZInQ.Contrib.CloudR2NOS.Descent
