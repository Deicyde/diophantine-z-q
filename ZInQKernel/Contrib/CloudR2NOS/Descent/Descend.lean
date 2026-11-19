/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
for scheme-only native descent.

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
EDITION 2 (2026-11-17, pre-emptive, before its first compile): the conclusion of `span_descended` is a `letI … ;`
expression, so its goal is a `let`, and a bare `intro n` would introduce the let-bound instance instead of the element;
`show ∀ n : Γ(L', ⊤), _` (zeta by defeq) now precedes `intro n`. Statements unchanged.
EDITION (2026-11-17, pre-emptive, from the Coaction first probe): `moduleTopS` and `isScalarTower_top` take the base
ring `S` IMPLICITLY and it is not determined by `S' f' L'` (stuck `Algebra ?m S'`); every use now passes `(S := S)`.
Statements otherwise unchanged.
EDITION 4 (2026-11-17, pre-emptive, from the Cocycle probe): the additive structure of the pulled-back sections is
`map_zero`/`map_add` of the bundled unit map (the `simp` did not see through the section synonym in Cocycle).
Statements unchanged.
EDITION 5 (2026-11-17, first Parent compile probe of this file). Statements unchanged except as disclosed:
* `app_smul_top`: the pinned `Scheme.Modules.Hom.app_smul` takes the scalar right after the morphism (open implicit);
* `trans₂`, `chainL`: an `AddCommGrpCat` morphism's `.hom` is already an `AddMonoidHom` (no `.toAddMonoidHom`); the
  85/97 errors were cascades of the then-ill-formed `trans₂`; `trans₂_smul` names its morphism;
* the `Nt` notation is removed (a `letI` cannot occur in a notation body); the two binders spell the type out;
* `chainL_E₂`, `θ_cocycle`: their statements restrict `θ` to `S`, which needs the scalar tower on `Γ(L', ⊤)`
  (`LinearMap.CompatibleSMul`); `haveI := isScalarTower_top (S := S) S' f' L'` is added to the statements' instance
  prefix (DISCLOSED: route-Q-internal statements that did not elaborate before; no new premise) and to the proofs;
* `θ_cocycle`: `include hb₁₂ hb₁₃ hb₂₃` (its proof uses them); its explicit argument order is then exactly the one
  `span_descended` uses;
* `span_descended`: the unit step proves `μ ∘ (1 ⊗ ·) = id` and rewrites with it (the second `convert` goal was an element
  equation); `hid` is normalised with `restrictScalars_apply`.
EDITION 6 (2026-11-17, second Parent compile probe, read from the exact goals in the log). Statements unchanged:
* `trans₂_pbSec`: the W07 rewrite lemmas are stated with `Scheme.Modules.pullbackSection`, the goal with the (definitionally
  equal) lane alias `pbSec`, so `rw` finds no key; `e` is now the W07 lemma composed through `congrArg … |>.trans`, which
  unifies up to unfolding (as `pbSec_smul_κ` does with `exact`), and the final `pullbackCongr rfl` step is closed by
  `rfl` (fallbacks: the W07 lemma by `exact`/`erw`) (104/106);
* the two transport maps take the triple-overlap scheme `X'''` as an explicit section variable before `b₁₂ b₁₃ b₂₃`
  (their types mention it), so the statements of `chainR_E₂`/`chainL_E₂` now pass it (152/171); 236 and 231 were cascades.
EDITION 7 (2026-11-17, third Parent compile probe: 179, 212/215, 261, read from the log). No existing statement changed;
two NEW helper lemmas:
* `inv_app_trans₂` / `inv_inv_trans₂`: the inverse transport undoes `trans₂`, stated GENERICALLY with explicit types and
  proved once (`Scheme.Modules.iso_hom_app_inv_app e.symm`; ed6 and earlier applied `iso_hom_app_inv_app` in the wrong
  direction, without `.symm`, and at 212 with the iso left to unification at the concrete overlap — the whnf heartbeat;
  the 215 timeout was the same declaration's exhausted per-declaration budget); `hinv` (chainL_E₂) and `i₁` (θ_cocycle)
  now only instantiate them;
* 179: `congr 2` already closes the goal; the trailing `simp` is `all_goals simp` (and likewise pre-emptively in the
  chainL_E₂ inner case, unchecked so far because of the exhausted budget).
EDITION 8 (2026-11-17, fourth Parent compile probe: 247/249, from the exact goals). The lane alias `pbSec` is a definition,
not a bundled-map coercion, so neither `simp`'s `map_zero` nor `rw [map_add]` (pattern `⇑?f (?x + ?y)`) sees through it;
in `chainL_E₂`'s inner induction the zero and additivity steps for `pbSec b₂₃` are now named facts proved by
`map_zero _` / `map_add _ _ _` (the form compiled in Cocycle's `descended_zero`). Proof-only; no statement changed.
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
    φ.app ⊤ (g • x) = g • φ.app ⊤ x := by
  first
  | exact Scheme.Modules.Hom.app_smul φ g x
  | exact Scheme.Modules.Hom.app_smul φ ⊤ g x
  | rw [Scheme.Modules.Hom.app_smul]

/-- The transport `b^* a^* L' → (b ≫ a)^* L'`, then along `h : b ≫ a = c`. -/
noncomputable def trans₂ {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X')
    (h : b ≫ a = c) :
    Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤) →+
      Γ((Scheme.Modules.pullback c).obj L', ⊤) :=
  (((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').hom.app ⊤).hom

theorem trans₂_pbSec {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (n : Γ(L', ⊤)) :
    trans₂ X' L' X'' b a c h (pbSec b (pbSec a n)) = pbSec c n := by
  subst h
  change ((Scheme.Modules.pullbackCongr rfl).hom.app L').app ⊤
      (((Scheme.Modules.pullbackComp b a).hom.app L').app ⊤ (pbSec b (pbSec a n))) = _
  have e : ((Scheme.Modules.pullbackComp b a).hom.app L').app ⊤ (pbSec b (pbSec a n)) =
      pbSec (b ≫ a) n := by
    have h0 := Scheme.Modules.pullbackComp_inv_app_pullbackSection b a (openSubset := ⊤) n
    exact (congrArg (fun z => ((Scheme.Modules.pullbackComp b a).hom.app L').app ⊤ z) h0.symm).trans
      (Scheme.Modules.natIso_hom_app_inv_app (Scheme.Modules.pullbackComp b a) L' _ _)
  rw [e]
  first
  | rfl
  | exact (Scheme.Modules.pullbackCongr_hom_app_pullbackSection (compatibility := rfl) (openSubset := ⊤)
      (sectionValue := n)).trans (congr($(CategoryTheory.Functor.map_id _ _) _))
  | (erw [Scheme.Modules.pullbackCongr_hom_app_pullbackSection]
     exact congr($(CategoryTheory.Functor.map_id _ _) _))

theorem trans₂_smul {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (g : Γ(Y, ⊤)) (z : Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤)) :
    trans₂ X' L' X'' b a c h (g • z) = g • trans₂ X' L' X'' b a c h z :=
  app_smul_top ((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').hom g z

/-- The inverse transport undoes `trans₂` (stated generically with its explicit type, so that concrete overlaps only
instantiate it and never unify a composite isomorphism). -/
theorem inv_app_trans₂ {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (z : Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤)) :
    (((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').inv.app ⊤) (trans₂ X' L' X'' b a c h z) = z := by
  first
  | exact Scheme.Modules.iso_hom_app_inv_app ((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').symm ⊤ z
  | (simp only [trans₂]; exact Scheme.Modules.iso_hom_app_inv_app ((Scheme.Modules.pullbackComp b a).app L' ≪≫ (Scheme.Modules.pullbackCongr h).app L').symm ⊤ z)

/-- `inv_app_trans₂` with the composite inverse split into its two factors (the form produced by `simp only
[Iso.trans_inv, Iso.app_inv, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]`). -/
theorem inv_inv_trans₂ {Y : Scheme.{u}} (b : Y ⟶ X'') (a : X'' ⟶ X') (c : Y ⟶ X') (h : b ≫ a = c)
    (z : Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback a).obj L'), ⊤)) :
    ((Scheme.Modules.pullbackComp b a).inv.app L').app ⊤
      (((Scheme.Modules.pullbackCongr h).inv.app L').app ⊤ (trans₂ X' L' X'' b a c h z)) = z := by
  have h0 := inv_app_trans₂ X' L' X'' b a c h z
  first
  | exact h0
  | (simp only [Iso.trans_inv, Iso.app_inv, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h0
     exact h0)

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

/-- The right-hand transport `y ↦ (b₁₃ ≫ a₂)`-section of `b₁₃^* y`. -/
noncomputable def chainR : Γ((Scheme.Modules.pullback a₂).obj L', ⊤) →+
    Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  (trans₂ X' L' X'' b₁₃ a₂ (b₁₃ ≫ a₂) rfl).comp
    { toFun := pbSec b₁₃
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y }

/-- The left-hand transport through `b₁₂`, `ψ` on the `b₂₃` overlap, and `h₂`, `h₃`. -/
noncomputable def chainL : Γ((Scheme.Modules.pullback a₂).obj L', ⊤) →+
    Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  (trans₂ X' L' X'' b₂₃ a₂ (b₁₃ ≫ a₂) h₃.symm).comp
    ((((Scheme.Modules.pullback b₂₃).map ψ.hom).app ⊤).hom.comp
      ((((Scheme.Modules.pullbackComp b₂₃ a₁).app L' ≪≫
          (Scheme.Modules.pullbackCongr h₂.symm).app L').inv.app ⊤).hom.comp
        ((trans₂ X' L' X'' b₁₂ a₂ (b₁₂ ≫ a₂) rfl).comp
          { toFun := pbSec b₁₂
            map_zero' := map_zero _
            map_add' := fun x y => map_add _ x y })))

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

end Final

end ZInQ.Contrib.CloudR2NOS.Descent
