/-
Copyright (c) 2026 H5/NOS Round-2 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Adapted from CloudR2NOS/Descent/{Cocycle,Span,Descend}.lean at e2d523d39.
The global-section comparisons use flat base change on quasi-compact,
quasi-separated schemes for quasi-coherent modules.
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.Descend

/-!
# Faithfully flat descent of global sections

On the affine double and triple overlaps, the module cocycle induces
the usual module descent datum on global sections. Faithfully flat
descent then expresses every global section as a linear combination
of compatible sections.
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open ZInQ.Contrib.CloudR2NOS.Descent
  (moduleTop moduleTopS isScalarTower_top tensorBaseChangeAddEquiv sectionsBC
    bijective_sectionsBC sectionsBC_tmul κ κ₃ ΓinvA isPullback_swap swapΓ
    pbSec_smul_of_isPullback pbSec_smul_κ pbSec_naturality cyc₃ cyc₃_algebraMap
    cyc₃_tmul chainR chainL trans₂ trans₂_smul trans₂_pbSec inv_app_trans₂ inv_inv_trans₂
    app_smul_top appTop_κ)

namespace NeronDVR.SectionDescent

local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

section DoubleOverlap

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']
  (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')

variable [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) L']
  [QuasiCompact f'] [QuasiSeparated f']

/-- **E₁** : `S' ⊗[S] Γ(L', ⊤) ≃+ Γ(a₁^*L', ⊤)`, `s ⊗ n ↦ κ (1 ⊗ s) • a₁^* n`. -/
noncomputable def E₁ (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (algebraMap S' (S' ⊗[S] S'))))) :
    (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; S' ⊗[S] Γ(L', ⊤)) ≃+
      Γ((Scheme.Modules.pullback a₁).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  (tensorBaseChangeAddEquiv S S' S' Γ(L', ⊤)).trans
    (AddEquiv.ofBijective (sectionsBC ha₁' L') (bijective_sectionsBC ha₁' L'))

theorem E₁_tmul (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (algebraMap S' (S' ⊗[S] S'))))) (s : S') (n : Γ(L', ⊤)) :
    E₁ S' X' f' L' X'' f'' a₁ ha₁' (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; s ⊗ₜ n) =
      κ S' X'' f'' (1 ⊗ₜ s) • pbSec a₁ n := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  change sectionsBC ha₁' L' ((1 ⊗ₜ s) ⊗ₜ n) = _
  rw [sectionsBC_tmul]
  rfl

/-- **E₂** : `S' ⊗[S] Γ(L', ⊤) ≃+ Γ(a₂^*L', ⊤)`, `s ⊗ n ↦ κ (s ⊗ 1) • a₂^* n`, through the
swapped square. -/
noncomputable def E₂ (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) :
    (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; S' ⊗[S] Γ(L', ⊤)) ≃+
      Γ((Scheme.Modules.pullback a₂).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  (tensorBaseChangeAddEquiv S S' S' Γ(L', ⊤)).trans
    (AddEquiv.ofBijective (sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L')
      (bijective_sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L'))

theorem E₂_tmul (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))) (s : S')
    (n : Γ(L', ⊤)) :
    E₂ S' X' f' L' X'' f'' a₂ ha₂ (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; s ⊗ₜ n) =
      κ S' X'' f'' (s ⊗ₜ 1) • pbSec a₂ n := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  change sectionsBC (isPullback_swap S' f' f'' a₂ ha₂) L' ((1 ⊗ₜ s) ⊗ₜ n) = _
  rw [sectionsBC_tmul]
  congr 1
  -- `(f'' ≫ Spec swap)^♯ (1 ⊗ s) = f''^♯ (s ⊗ 1)`
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  have hnat : ∀ y : S' ⊗[S] S', (Spec.map (CommRingCat.ofHom (swapΓ (S := S) S'))).appTop.hom (ΓinvA _ y) =
      ΓinvA _ ((swapΓ (S := S) S') y) := fun y => by
    first
    | exact (congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (swapΓ (S := S) S')))).symm
    | exact congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (swapΓ (S := S) S')))
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat]
  · change (f''.appTop).hom (ΓinvA _ ((Algebra.TensorProduct.comm S S' S') (1 ⊗ₜ s))) = _
    rw [Algebra.TensorProduct.comm_tmul]
    show (f''.appTop).hom (ΓinvA _ (s ⊗ₜ[S] 1)) = (f''.appLE ⊤ ⊤ le_top).hom (ΓinvA _ (s ⊗ₜ[S] 1))
    erw [Scheme.Hom.appLE_top_top_eq_appTop]
    all_goals rfl

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
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  have hnat : ∀ y : S' ⊗[S] S', (Spec.map (CommRingCat.ofHom (swapΓ (S := S) S'))).appTop.hom (ΓinvA _ y) =
      ΓinvA _ ((swapΓ (S := S) S') y) := fun y => by
    first
    | exact (congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (swapΓ (S := S) S')))).symm
    | exact congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (swapΓ (S := S) S')))
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat]
  change (f''.appTop).hom (ΓinvA _ ((Algebra.TensorProduct.comm S S' S') (t ⊗ₜ 1))) = _
  rw [Algebra.TensorProduct.comm_tmul]
  show (f''.appTop).hom (ΓinvA _ (1 ⊗ₜ[S] t)) = (f''.appLE ⊤ ⊤ le_top).hom (ΓinvA _ (1 ⊗ₜ[S] t))
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  all_goals rfl

variable (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))))
  (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
  (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')

/-- `E₂` is semilinear for the left factor. -/
theorem E₂_smul (t : S') (y : letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; S' ⊗[S] Γ(L', ⊤)) :
    E₂ S' X' f' L' X'' f'' a₂ ha₂ (t • y) = κ S' X'' f'' (t ⊗ₜ 1) • E₂ S' X' f' L' X'' f'' a₂ ha₂ y := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | tmul s n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, E₂_tmul, E₂_tmul, ← mul_smul, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- **Q3.** The coaction `θ n = E₂⁻¹ (ψ (a₁^* n))`, an `S'`-linear map for the left factor. -/
noncomputable def θ : letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'
    Γ(L', ⊤) →ₗ[S'] S' ⊗[S] Γ(L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  { toFun := fun n => (E₂ S' X' f' L' X'' f'' a₂ ha₂).symm (ψ.hom.app ⊤ (pbSec a₁ n))
    map_add' := fun n m => by
      have h1 : pbSec a₁ (n + m) = pbSec a₁ n + pbSec a₁ m := map_add _ _ _
      have h2 : ψ.hom.app ⊤ (pbSec a₁ n + pbSec a₁ m) =
          ψ.hom.app ⊤ (pbSec a₁ n) + ψ.hom.app ⊤ (pbSec a₁ m) := map_add _ _ _
      show (E₂ S' X' f' L' X'' f'' a₂ ha₂).symm (ψ.hom.app ⊤ (pbSec a₁ (n + m))) = _
      rw [h1, h2, map_add]
      all_goals rfl
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
        (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; (1 : S') ⊗ₜ n) ↔
      ψ.hom.app ⊤ (pbSec a₁ n) = pbSec a₂ n := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  have h1 : E₂ S' X' f' L' X'' f'' a₂ ha₂ ((1 : S') ⊗ₜ n) = pbSec a₂ n := by
    rw [E₂_tmul, ← Algebra.TensorProduct.one_def, map_one, one_smul]
  constructor
  · intro h
    rw [← E₂_θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ, h, h1]
  · intro h
    apply (E₂ S' X' f' L' X'' f'' a₂ ha₂).injective
    rw [E₂_θ, h, h1]

end DoubleOverlap

section TripleOverlap

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']

variable (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
  (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
  (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
  [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) L']
  [QuasiCompact f'] [QuasiSeparated f']

/-- The triple-overlap square over the third factor, in `algebraMap` form via `cyc₃`. -/
theorem isPullback_third
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom))) :
    IsPullback (b₁₃ ≫ a₂) (f''' ≫ Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom)) f'
      (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] (S' ⊗[S] S'))))) := by
  have h₀ := (hb₁₃.flip.paste_vert ha₂.flip).flip
  have hsw : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) =
      Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] (S' ⊗[S] S')))) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      cyc₃_algebraMap]
  haveI : IsIso (Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom)) := by
    have : IsIso (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom) :=
      ⟨⟨CommRingCat.ofHom (cyc₃ (S := S) S').symm.toAlgHom.toRingHom,
        congrArg CommRingCat.ofHom (RingHom.ext fun x => (cyc₃ (S := S) S').symm_apply_apply x),
        congrArg CommRingCat.ofHom (RingHom.ext fun x => (cyc₃ (S := S) S').apply_symm_apply x)⟩⟩
    infer_instance
  rw [hsw] at h₀
  exact IsPullback.of_iso h₀ (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

variable
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))

include ha₂ hb₁₃ in
/-- **G** : `S' ⊗[S] (S' ⊗[S] Γ(L', ⊤)) ≃+ Γ((b₁₃ ≫ a₂)^*L', ⊤)`,
`s ⊗ (t ⊗ n) ↦ κ₃ (s ⊗ (t ⊗ 1)) • (b₁₃ ≫ a₂)^* n`. -/
noncomputable def G₃ :
    (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L';
      S' ⊗[S] (S' ⊗[S] Γ(L', ⊤))) ≃+ Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  (TensorProduct.assoc S S' S' Γ(L', ⊤)).symm.toAddEquiv.trans
    ((tensorBaseChangeAddEquiv S S' (S' ⊗[S] S') Γ(L', ⊤)).trans
      (AddEquiv.ofBijective (sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L')
        (bijective_sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L')))

theorem G₃_tmul (s t : S') (n : Γ(L', ⊤)) :
    G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; s ⊗ₜ[S] (t ⊗ₜ[S] n)) =
      κ₃ S' f''' (s ⊗ₜ[S] (t ⊗ₜ[S] 1)) • pbSec (b₁₃ ≫ a₂) n := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  change sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L'
      (((1 : S') ⊗ₜ[S] (s ⊗ₜ[S] t)) ⊗ₜ[S'] n) = _
  rw [sectionsBC_tmul]
  congr 1
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  have hnat : ∀ y : S' ⊗[S] (S' ⊗[S] S'), (Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom)).appTop.hom (ΓinvA _ y) =
      ΓinvA _ ((cyc₃ (S := S) S').toAlgHom.toRingHom y) := fun y => by
    first
    | exact (congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom))).symm
    | exact congrArg (fun φ => φ.hom y) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom))
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hnat]
  change (f'''.appTop).hom (ΓinvA _ ((cyc₃ (S := S) S') (1 ⊗ₜ (s ⊗ₜ t)))) = _
  rw [cyc₃_tmul]
  show (f'''.appTop).hom (ΓinvA _ (s ⊗ₜ[S] (t ⊗ₜ[S] 1))) =
    (f'''.appLE ⊤ ⊤ le_top).hom (ΓinvA _ (s ⊗ₜ[S] (t ⊗ₜ[S] 1)))
  erw [Scheme.Hom.appLE_top_top_eq_appTop]
  all_goals rfl

end TripleOverlap

section Cocycle

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']
  (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
  (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
  (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')

variable [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) L']
  [QuasiCompact f'] [QuasiSeparated f']
  (ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))))
  (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
  (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
  (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
  (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
  (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
  (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')

include hb₁₃ in
/-- **(R2)** The right transport of `E₂ y` is `G₃` of `(1 ⊗ ·)`-padding of `y`. -/
theorem chainR_E₂ (y : letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; S' ⊗[S] Γ(L', ⊤)) :
    chainR X' L' X'' a₂ X''' b₁₃ (E₂ S' X' f' L' X'' f'' a₂ ha₂ y) =
      G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L';
          (TensorProduct.mk S S' Γ(L', ⊤) 1).lTensor S' y) := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s n =>
    rw [E₂_tmul, LinearMap.lTensor_tmul, TensorProduct.mk_apply, G₃_tmul]
    change trans₂ X' L' X'' b₁₃ a₂ (b₁₃ ≫ a₂) rfl (pbSec b₁₃ (κ S' X'' f'' (s ⊗ₜ 1) • pbSec a₂ n)) = _
    rw [pbSec_smul_κ S' X'' f'' X''' f''' b₁₃ _ hb₁₃.w, trans₂_smul, trans₂_pbSec]
    congr 2
    all_goals simp

include hb₁₂ hb₂₃ ha₁' in
/-- **(R3)** The left transport of `E₂ y` is `G₃` of `(θ ⊗ ·)` applied to `y`. -/
theorem chainL_E₂ (y : letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'; S' ⊗[S] Γ(L', ⊤)) :
    chainL X' L' X'' a₁ a₂ X''' b₁₂ b₁₃ b₂₃ h₂ h₃ ψ (E₂ S' X' f' L' X'' f'' a₂ ha₂ y) =
      G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L';
          haveI := isScalarTower_top (S := S) S' f' L';
          ((θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ).restrictScalars S).lTensor S' y) := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s n =>
    rw [E₂_tmul, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply]
    -- the `b₁₂` step
    change trans₂ X' L' X'' b₂₃ a₂ (b₁₃ ≫ a₂) h₃.symm
        (((Scheme.Modules.pullback b₂₃).map ψ.hom).app ⊤
          ((((Scheme.Modules.pullbackComp b₂₃ a₁).app L' ≪≫
              (Scheme.Modules.pullbackCongr h₂.symm).app L').inv.app ⊤)
            (trans₂ X' L' X'' b₁₂ a₂ (b₁₂ ≫ a₂) rfl
              (pbSec b₁₂ (κ S' X'' f'' (s ⊗ₜ 1) • pbSec a₂ n))))) = _
    rw [pbSec_smul_κ S' X'' f'' X''' f''' b₁₂ _ hb₁₂.w, trans₂_smul, trans₂_pbSec,
      app_smul_top, app_smul_top, trans₂_smul]
    -- `(b₁₂ ≫ a₂)^* n ↦ b₂₃^* a₁^* n`, then `ψ`, then `E₂ (θ n)`
    have hinv : (((Scheme.Modules.pullbackComp b₂₃ a₁).app L' ≪≫
        (Scheme.Modules.pullbackCongr h₂.symm).app L').inv.app ⊤) (pbSec (b₁₂ ≫ a₂) n) =
        pbSec b₂₃ (pbSec a₁ n) := by
      have := trans₂_pbSec X' L' X'' b₂₃ a₁ (b₁₂ ≫ a₂) h₂.symm n
      rw [← this]
      exact inv_app_trans₂ X' L' X'' b₂₃ a₁ (b₁₂ ≫ a₂) h₂.symm _
    rw [hinv, pbSec_naturality, ← E₂_θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n]
    -- expand `θ n` and use `(R1)` termwise
    generalize θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n = w
    induction w using TensorProduct.induction_on with
    | zero =>
      have h0 : pbSec b₂₃ (0 : Γ((Scheme.Modules.pullback a₂).obj L', ⊤)) = 0 := map_zero _
      simp [h0]
    | add x y hx hy =>
      have hpb : pbSec b₂₃ ((E₂ S' X' f' L' X'' f'' a₂ ha₂) x + (E₂ S' X' f' L' X'' f'' a₂ ha₂) y) =
          pbSec b₂₃ ((E₂ S' X' f' L' X'' f'' a₂ ha₂) x) + pbSec b₂₃ ((E₂ S' X' f' L' X'' f'' a₂ ha₂) y) :=
        map_add _ _ _
      rw [map_add, hpb, map_add, smul_add, hx, hy, tmul_add, map_add]
    | tmul t m =>
      rw [E₂_tmul, pbSec_smul_κ S' X'' f'' X''' f''' b₂₃ _ hb₂₃.w, trans₂_smul, trans₂_pbSec,
        G₃_tmul, smul_smul, ← map_mul]
      congr 2
      all_goals simp [Algebra.TensorProduct.tmul_mul_tmul]

include hb₁₂ hb₁₃ hb₂₃ in
/-- **Q4.** The cocycle condition, in the form of W07 `TensorProduct.bijective_descentLift_of_flat`
for `J = Unit`. -/
theorem θ_cocycle
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫
          ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫
          ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (x : Γ(L', ⊤)) :
    letI := moduleTop f' L'; letI := moduleTopS (S := S) S' f' L'
    haveI := isScalarTower_top (S := S) S' f' L'
    ((θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ).restrictScalars S).lTensor S'
        (θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ x) =
      (TensorProduct.mk S S' Γ(L', ⊤) 1).lTensor S' (θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ x) := by
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  apply (G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃).injective
  rw [← chainL_E₂ S' X' f' L' X'' f'' a₁ a₂ X''' f''' b₁₂ b₁₃ b₂₃ ha₁' ha₂ hb₁₂ hb₁₃ hb₂₃ h₂ h₃ ψ,
    ← chainR_E₂ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃, E₂_θ]
  -- evaluate `hψ` on `(b₁₃ ≫ a₁)^* x`
  have e := congr($(congrArg Iso.hom hψ).app ⊤ (pbSec (b₁₃ ≫ a₁) x))
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at e
  -- the initial transports `(b₁₃ ≫ a₁)^* x ↦ b₁₂^* a₁^* x` and `↦ b₁₃^* a₁^* x`
  have i₁ : ((Scheme.Modules.pullbackComp b₁₂ a₁).inv.app L').app ⊤
      (((Scheme.Modules.pullbackCongr h₁).inv.app L').app ⊤ (pbSec (b₁₃ ≫ a₁) x)) =
      pbSec b₁₂ (pbSec a₁ x) := by
    have := trans₂_pbSec X' L' X'' b₁₂ a₁ (b₁₃ ≫ a₁) h₁ x
    rw [← this]
    exact inv_inv_trans₂ X' L' X'' b₁₂ a₁ (b₁₃ ≫ a₁) h₁ _
  have i₂ : ((Scheme.Modules.pullbackComp b₁₃ a₁).inv.app L').app ⊤ (pbSec (b₁₃ ≫ a₁) x) =
      pbSec b₁₃ (pbSec a₁ x) :=
    Scheme.Modules.pullbackComp_inv_app_pullbackSection b₁₃ a₁ (openSubset := ⊤) x
  rw [i₁, i₂, pbSec_naturality, pbSec_naturality] at e
  exact e

end Cocycle

section Span

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']

/-- Sections invariant under faithfully flat descent span all global sections of a
quasicoherent module on a quasi-compact, quasi-separated scheme over the covering
affine base. The tensor comparison identifies them with the descent submodule. -/
theorem span_descended_of_isQuasicoherent (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
    [SheafOfModules.IsQuasicoherent (R := X'.ringCatSheaf) L']
    [QuasiCompact f'] [QuasiSeparated f']
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫
          ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫
          ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    letI := moduleTop f' L'
    ∀ n : Γ(L', ⊤), n ∈ Submodule.span S'
      {d | ψ.hom.app ⊤ (pbSec a₁ d) = pbSec a₂ d} := by
  classical
  letI := moduleTop f' L'
  letI := moduleTopS (S := S) S' f' L'
  haveI := isScalarTower_top (S := S) S' f' L'
  have hL : (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom =
      algebraMap S' (S' ⊗[S] S') := RingHom.ext fun _ => rfl
  have ha₁' : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (algebraMap S' (S' ⊗[S] S')))) := by
    rw [← hL]; exact ha₁
  let Θ := θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ
  let θU : Unit → Unit → (Γ(L', ⊤) →ₗ[S'] S' ⊗[S] Γ(L', ⊤)) := fun _ _ => Θ
  -- Q4
  have hcoc : ∀ (j k l : Unit) (x : Γ(L', ⊤)),
      ((θU k l).restrictScalars S).lTensor S' (θU j k x) =
        (TensorProduct.mk S S' Γ(L', ⊤) 1).lTensor S' (θU j l x) := fun _ _ _ x =>
    θ_cocycle S' X' f' L' X'' f'' a₁ a₂ X''' f''' b₁₂ b₁₃ b₂₃ ha₁' ha₂ hb₁₂ hb₁₃ hb₂₃ h₁ h₂ h₃ ψ hψ x
  -- Q5: the unit, via `ϕ = E₂⁻¹ ∘ ψ ∘ E₁`
  have hunit : ∀ (j : Unit) (x : Γ(L', ⊤)),
      (LinearMap.id : Γ(L', ⊤) →ₗ[S] Γ(L', ⊤)).liftBaseChange S' (θU j j x) = x := by
    intro _ x
    let μ : S' ⊗[S] Γ(L', ⊤) →ₗ[S'] Γ(L', ⊤) := (LinearMap.id : Γ(L', ⊤) →ₗ[S] Γ(L', ⊤)).liftBaseChange S'
    let uS : Γ(L', ⊤) →ₗ[S'] Γ(L', ⊤) := μ ∘ₗ Θ
    -- (a) `(id ⊗ u) ∘ θ = θ`
    have ha : ∀ y : Γ(L', ⊤), (uS.restrictScalars S).lTensor S' (Θ y) = Θ y := fun y => by
      have hμ1 : (μ.restrictScalars S) ∘ₗ (TensorProduct.mk S S' Γ(L', ⊤) 1) = LinearMap.id := by
        ext m; simp [μ]
      have h := congrArg ((μ.restrictScalars S).lTensor S') (hcoc () () () y)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← LinearMap.lTensor_comp, hμ1, LinearMap.lTensor_id, LinearMap.id_apply] at h
      exact h
    -- `ϕ (s ⊗ n) = (id ⊗ s•) (θ n)`, with `ϕ` bijective
    let e₁ := E₁ S' X' f' L' X'' f'' a₁ ha₁'
    let e₂ := E₂ S' X' f' L' X'' f'' a₂ ha₂
    let ψT : Γ((Scheme.Modules.pullback a₁).obj L', ⊤) ≃+ Γ((Scheme.Modules.pullback a₂).obj L', ⊤) :=
      { toFun := ψ.hom.app ⊤
        invFun := ψ.inv.app ⊤
        left_inv := fun z => Scheme.Modules.iso_hom_app_inv_app ψ.symm ⊤ z
        right_inv := fun z => Scheme.Modules.iso_hom_app_inv_app ψ ⊤ z
        map_add' := map_add _ }
    let ϕ := (e₁.trans ψT).trans e₂.symm
    have hϕ : ∀ (s : S') (n : Γ(L', ⊤)),
        ϕ (s ⊗ₜ n) = ((LinearMap.lsmul S' Γ(L', ⊤) s).restrictScalars S).lTensor S' (Θ n) := by
      intro s n
      apply e₂.injective
      change e₂ (e₂.symm (ψ.hom.app ⊤ (e₁ (s ⊗ₜ n)))) = _
      rw [AddEquiv.apply_symm_apply, E₁_tmul, app_smul_top, ← E₂_θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n]
      generalize Θ n = w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [map_add, map_add, smul_add, hy, hz, map_add]
      | tmul t m =>
        rw [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply,
          E₂_tmul, E₂_tmul, pbSec_a₂_smul S' X' f' L' X'' f'' a₂ ha₂, smul_smul, smul_smul, mul_comm]
    -- (b) `(id ⊗ u) ∘ ϕ = ϕ`, hence `id ⊗ u = id`
    have hb : ∀ z : S' ⊗[S] Γ(L', ⊤), (uS.restrictScalars S).lTensor S' (ϕ z) = ϕ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [map_add, map_add, hy, hz]
      | tmul s n =>
        rw [hϕ, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
        have hcomm : (uS.restrictScalars S) ∘ₗ ((LinearMap.lsmul S' Γ(L', ⊤) s).restrictScalars S) =
            ((LinearMap.lsmul S' Γ(L', ⊤) s).restrictScalars S) ∘ₗ (uS.restrictScalars S) := by
          ext m; simp [map_smul]
        rw [hcomm, LinearMap.lTensor_comp, LinearMap.comp_apply, ha]
    have hid : (uS.restrictScalars S).lTensor S' ((1 : S') ⊗ₜ x) = (1 : S') ⊗ₜ x := by
      obtain ⟨z, hz⟩ := ϕ.surjective ((1 : S') ⊗ₜ x)
      rw [← hz, hb]
    simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply] at hid
    have h0 : (1 : S') ⊗ₜ[S] (uS x - x) = 0 := by rw [tmul_sub, hid, sub_self]
    have := sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := S) (A := S')
      (M := Γ(L', ⊤)) _).mp h0)
    exact this
  -- W07 algebraic descent
  have hbij := TensorProduct.bijective_descentLift_of_flat θU hunit hcoc ()
  show ∀ n : Γ(L', ⊤), _
  intro n
  obtain ⟨z, rfl⟩ := hbij.2 n
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | tmul s w =>
    rw [TensorProduct.descentLift_tmul]
    refine Submodule.smul_mem _ s (Submodule.subset_span ?_)
    have hw := (TensorProduct.mem_descentSubmodule θU (w : Unit → Γ(L', ⊤))).mp w.2 () ()
    exact (θ_eq_one_tmul_iff S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ _).mp hw

end Span

end NeronDVR.SectionDescent
