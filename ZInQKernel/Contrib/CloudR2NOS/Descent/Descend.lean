/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statements in this file:
* Q4: the cocycle of `θ`;
* Q5: its unit;
* `span_descended`: the descended sections span `Γ(L', ⊤)` over `S'`.

NATIVE. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

Route of Q4:
* `hψ` is evaluated on the pulled-back section `(b₁₃ ≫ a₁)^* n`.
* The W07 section lemmas `pullbackComp_inv_app_pullbackSection` and
  `pullbackCongr_hom_app_pullbackSection` (Modules/AffineSections) move it through the
  `pullbackComp`/`pullbackCongr` isomorphisms.
* The two sides are compared after the injective base change `G₃` of `Γ(L', ⊤)` along the
  third factor.

Route of Q5: the cocycle gives `(id ⊗ u) ∘ θ = θ` for `u = μ ∘ θ`. Then
`(id ⊗ u) ∘ ϕ = ϕ` for the bijection `ϕ = E₂⁻¹ ∘ ψ ∘ E₁`, and faithful flatness gives `u = id`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.Span

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "CIBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

section Descend

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']
  (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
  (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
  (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')

/-- Pulling back along any `b : X''' ⟶ X''` over a ring map `m` is semilinear on the functions
`κ`. This is the generic form of `pbSec_smul_of_isPullback`: the unit of the
pullback–pushforward adjunction is `𝒪`-linear. -/
theorem pbSec_smul_κ (b : X''' ⟶ X'') (m : S' ⊗[S] S' →+* S' ⊗[S] (S' ⊗[S] S'))
    (hw : b ≫ f'' = f''' ≫ Spec.map (CommRingCat.ofHom m)) (F : X''.Modules) (x : S' ⊗[S] S')
    (y : Γ(F, ⊤)) :
    pbSec b (κ S' X'' f'' x • y) = κ₃ S' f''' (m x) • pbSec b y := by
  rw [← appTop_κ S' b m hw x]
  exact Scheme.Modules.pullbackSection_smul b (κ S' X'' f'' x) y

/-- `𝒪`-linearity of a morphism of modules on global sections. -/
theorem app_smul_top {Z : Scheme.{u}} {M N : Z.Modules} (φ : M ⟶ N) (g : Γ(Z, ⊤)) (x : Γ(M, ⊤)) :
    φ.app ⊤ (g • x) = g • φ.app ⊤ x :=
  Scheme.Modules.Hom.app_smul φ ⊤ g x

/-- The transport `b^* a^* L' → (b ≫ a)^* L'`, then along `h : b ≫ a = c`. -/
noncomputable def trans₂ {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X')
    (h : b ≫ a = c) :
    Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤) →+
      Γ((Scheme.Modules.pullback c).obj L', ⊤) :=
  (((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').hom.app ⊤).hom.toAddMonoidHom

theorem trans₂_pbSec {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (n : Γ(L', ⊤)) :
    trans₂ X' L' X'' b a c h (pbSec b (pbSec a n)) = pbSec c n := by
  subst h
  change ((Scheme.Modules.pullbackCongr rfl).hom.app L').app ⊤
      (((Scheme.Modules.pullbackComp b a).hom.app L').app ⊤ (pbSec b (pbSec a n))) = _
  have e : ((Scheme.Modules.pullbackComp b a).hom.app L').app ⊤ (pbSec b (pbSec a n)) =
      pbSec (b ≫ a) n := by
    rw [← Scheme.Modules.pullbackComp_inv_app_pullbackSection b a (openSubset := ⊤) n]
    exact Scheme.Modules.natIso_hom_app_inv_app (Scheme.Modules.pullbackComp b a) L' _ _
  rw [e, Scheme.Modules.pullbackCongr_hom_app_pullbackSection]
  exact congr($(CategoryTheory.Functor.map_id _ _) _)

theorem trans₂_smul {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (g : Γ(Y, ⊤)) (z : Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤)) :
    trans₂ X' L' X'' b a c h (g • z) = g • trans₂ X' L' X'' b a c h z :=
  app_smul_top _ g z

variable [hL : L'.IsInvertible] [IsProper f']
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

local notation "Nt" => (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; S' ⊗[S] Γ(L', ⊤))

/-- The right-hand transport `y ↦ (b₁₃ ≫ a₂)`-section of `b₁₃^* y`. -/
noncomputable def chainR : Γ((Scheme.Modules.pullback a₂).obj L', ⊤) →+
    Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  (trans₂ X' L' X'' b₁₃ a₂ (b₁₃ ≫ a₂) rfl).comp
    { toFun := pbSec b₁₃
      map_zero' := by simp [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection]
      map_add' := fun x y => by
        simp [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection] }

/-- The left-hand transport through `b₁₂`, `ψ` on the `b₂₃` overlap, and `h₂`, `h₃`. -/
noncomputable def chainL : Γ((Scheme.Modules.pullback a₂).obj L', ⊤) →+
    Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  (trans₂ X' L' X'' b₂₃ a₂ (b₁₃ ≫ a₂) h₃.symm).comp
    ((((Scheme.Modules.pullback b₂₃).map ψ.hom).app ⊤).hom.toAddMonoidHom.comp
      ((((Scheme.Modules.pullbackComp b₂₃ a₁).app L' ≪≫
          (Scheme.Modules.pullbackCongr h₂.symm).app L').inv.app ⊤).hom.toAddMonoidHom.comp
        ((trans₂ X' L' X'' b₁₂ a₂ (b₁₂ ≫ a₂) rfl).comp
          { toFun := pbSec b₁₂
            map_zero' := by simp [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection]
            map_add' := fun x y => by
              simp [ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection] })))

include hb₁₃ in
/-- **(R2)** The right transport of `E₂ y` is `G₃` of `(1 ⊗ ·)`-padding of `y`. -/
theorem chainR_E₂ (y : Nt) :
    chainR X' L' X'' a₂ b₁₃ (E₂ S' X' f' L' X'' f'' a₂ ha₂ y) =
      G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS S' f' L';
          (TensorProduct.mk S S' Γ(L', ⊤) 1).lTensor S' y) := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s n =>
    rw [E₂_tmul, LinearMap.lTensor_tmul, TensorProduct.mk_apply, G₃_tmul]
    change trans₂ X' L' X'' b₁₃ a₂ (b₁₃ ≫ a₂) rfl (pbSec b₁₃ (κ S' X'' f'' (s ⊗ₜ 1) • pbSec a₂ n)) = _
    rw [pbSec_smul_κ S' X'' f'' X''' f''' b₁₃ _ hb₁₃.w, trans₂_smul, trans₂_pbSec]
    congr 2
    simp

include hb₁₂ hb₂₃ ha₁' in
/-- **(R3)** The left transport of `E₂ y` is `G₃` of `(θ ⊗ ·)` applied to `y`. -/
theorem chainL_E₂ (y : Nt) :
    chainL X' L' X'' a₁ a₂ b₁₂ b₁₃ b₂₃ h₂ h₃ ψ (E₂ S' X' f' L' X'' f'' a₂ ha₂ y) =
      G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS S' f' L';
          ((θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ).restrictScalars S).lTensor S' y) := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
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
      exact Scheme.Modules.iso_hom_app_inv_app _ ⊤ _
    rw [hinv, pbSec_naturality, ← E₂_θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n]
    -- expand `θ n` and use `(R1)` termwise
    generalize θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ n = w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add, map_add, map_add, smul_add, hx, hy, tmul_add, map_add]
    | tmul t m =>
      rw [E₂_tmul, pbSec_smul_κ S' X'' f'' X''' f''' b₂₃ _ hb₂₃.w, trans₂_smul, trans₂_pbSec,
        G₃_tmul, smul_smul, ← map_mul]
      congr 2
      simp [Algebra.TensorProduct.tmul_mul_tmul]

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
    letI := moduleTop f' L'; letI := moduleTopS S' f' L'
    ((θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ).restrictScalars S).lTensor S'
        (θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ x) =
      (TensorProduct.mk S S' Γ(L', ⊤) 1).lTensor S' (θ S' X' f' L' X'' f'' a₁ a₂ ha₁' ha₂ ψ x) := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
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
    exact Scheme.Modules.iso_hom_app_inv_app
      ((Scheme.Modules.pullbackComp b₁₂ a₁).app L' ≪≫ (Scheme.Modules.pullbackCongr h₁).app L') ⊤ _
  have i₂ : ((Scheme.Modules.pullbackComp b₁₃ a₁).inv.app L').app ⊤ (pbSec (b₁₃ ≫ a₁) x) =
      pbSec b₁₃ (pbSec a₁ x) :=
    Scheme.Modules.pullbackComp_inv_app_pullbackSection b₁₃ a₁ (openSubset := ⊤) x
  rw [i₁, i₂, pbSec_naturality, pbSec_naturality] at e
  exact e

end Descend

section Final

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']

/-- **Q5 + Q6 input.** Under the full FLT hypotheses minus `hL'`, the descended sections span
`Γ(L', ⊤)` over `S'` (for the action through `f'`).

Truth check: by W07 `bijective_descentLift_of_flat` (`J = Unit`), `S' ⊗[S] D ≃ Γ(L', ⊤)` for
the descent submodule `D` of `θ`. Its elements are exactly the descended sections
(`θ_eq_one_tmul_iff`). Unit and cocycle are Q5 and Q4. -/
theorem span_descended (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
    (hva : CIBS L' f')
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
  obtain ⟨hprop, hinv⟩ := isProper_and_isInvertible_of_closedImmersionBySections f' L' hva
  haveI := hprop
  haveI := hinv
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  haveI := isScalarTower_top S' f' L'
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
      have h := congrArg ((μ.restrictScalars S).lTensor S') (hcoc () () () y)
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        ← LinearMap.lTensor_comp] at h
      convert h using 2
      · rfl
      · ext m; simp [μ]
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
    rw [LinearMap.lTensor_tmul] at hid
    have h0 : (1 : S') ⊗ₜ[S] (uS x - x) = 0 := by rw [tmul_sub, hid, sub_self]
    have := sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := S) (A := S')
      (M := Γ(L', ⊤)) _).mp h0)
    exact this
  -- W07 algebraic descent
  have hbij := TensorProduct.bijective_descentLift_of_flat θU hunit hcoc ()
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

end Final

end ZInQ.Contrib.CloudR2NOS.Descent
