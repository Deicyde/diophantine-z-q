/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
for scheme-only native descent.

Sub-statements in this file:
* Q4: the cocycle of `θ`;
* Q5: the unit of `θ`;
* the Q6 input `span_descended`: the descended sections span `Γ(L', ⊤)` over `S'`, by the
  published W07 `TensorProduct.bijective_descentLift_of_flat` (FamilyDescent, `J = Unit`; no
  numeric options).

NATIVE. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

RISK NOTE (C6): Q4 is the bookkeeping-heavy step. It moves the FLT cocycle equation `hψ` to
global sections on the triple overlap and compares through the injective base-change map `G`
for `X''' → X'` (third factor).
EDITION (2026-11-17, pre-emptive, from the Coaction first probe): `moduleTopS` and `isScalarTower_top` take the base
ring `S` IMPLICITLY and it is not determined by `S' f' L'` (stuck `Algebra ?m S'`); every use now passes `(S := S)`.
Statements otherwise unchanged.
EDITION 3 (2026-11-17, pre-emptive, from the Coaction/Cocycle probes): the W07 `appLE_top_top_eq_appTop` rewrites are
`erw`; the `ΓSpecIso` naturality square is applied pointwise (the old `simpa` reduced it to `True` in Coaction).
Statements unchanged.
EDITION 4 (2026-11-17, pre-emptive, from the Cocycle second probe): in `G₃_tmul` the composite's ring map is `cyc₃`, not an
`algebraMap`, so the pointwise `ΓSpecIso` naturality square for it (`hnat`) replaces `ΓinvA_algebraMap`. Statements
unchanged.
EDITION 5 (2026-11-17, pre-emptive, same class as Cocycle's third probe): in `G₃_tmul` the right-hand `appLE` is hidden
inside the abbreviation `κ₃`; a `show` exposes it before `erw [appLE_top_top_eq_appTop]`. Statements unchanged.
EDITION 6 (2026-11-17, first Parent compile probe of this file). Statements unchanged in meaning:
* `cyc₃_tmul`: the base ring is pinned (`(S := S)`, `⊗ₜ[S]`); the stuck instance at 56 left the lemma undeclared, hence
  the unknown name at 64;
* `isPullback_third`: the cyclic map is an isomorphism by its explicit inverse `cyc₃.symm` (no
  `CommRingCat.isIso_iff_bijective` at the pin), as in Coaction;
* `G₃_tmul` (145): its own copy of the `hb₁₃` binder was MIS-PARENTHESISED (`.toRingHom` applied to `includeRight`
  inside `Algebra.TensorProduct.map` instead of to the map), so `G₃ … hb₁₃` had to unify two different square types
  (the `whnf` timeout at `hb₁₃`). The two square hypotheses are now ONE shared section `variable` pair, i.e. exactly
  `G₃`'s binder terms in the same positions; the tensor argument names its ring; the opening step unfolds `G₃` by its
  equations (old `change` as fallback).
EDITION 7 (2026-11-17, second Parent compile probe: one error, 165). The `simp only` opening unfolded `G₃` but left the
coerced `TensorProduct.assoc … .symm` and `tensorBaseChangeAddEquiv` applications un-rewritten (the coercion form did not
match `LinearEquiv.coe_toAddEquiv`), and since it did not fail the `change` fallback never ran; the opening is now the
definitional `change` to `sectionsBC … ((1 ⊗ₜ (s ⊗ₜ t)) ⊗ₜ n)` (both maps reduce on pure tensors), as in Cocycle's
compiled `E₂_tmul`. Statements unchanged.
EDITION 8 (2026-11-17, third Parent compile probe: 166, read from the exact expected type in the log). The base change is
OVER `S'`: `sectionsBC` takes `(S' ⊗[S] (S' ⊗[S] S')) ⊗[S'] Γ(L', ⊤)`, so the outer tensor is `⊗ₜ[S']` and the unit is
`(1 : S')` (ed7 wrote `⊗ₜ[S]`, and the bare `1` defaulted to `ℕ`, hence the `Module S ℕ` failure). Statements unchanged.
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.Cocycle

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "CIBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

section Span

variable {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
  [Module.FaithfullyFlat S S']

/-- The cyclic automorphism `a ⊗ (b ⊗ c) ↦ b ⊗ (c ⊗ a)` of `S' ⊗[S] (S' ⊗[S] S')`. -/
noncomputable def cyc₃ : S' ⊗[S] (S' ⊗[S] S') ≃ₐ[S] S' ⊗[S] (S' ⊗[S] S') :=
  (Algebra.TensorProduct.comm S S' (S' ⊗[S] S')).trans (Algebra.TensorProduct.assoc S S S S' S' S')

theorem cyc₃_tmul (a b c : S') :
    cyc₃ (S := S) S' (a ⊗ₜ[S] (b ⊗ₜ[S] c)) = b ⊗ₜ[S] (c ⊗ₜ[S] a) := rfl

/-- The third-factor inclusion `t ↦ 1 ⊗ (1 ⊗ t)` is `cyc₃ ∘ algebraMap`. -/
theorem cyc₃_algebraMap :
    (cyc₃ (S := S) S').toAlgHom.toRingHom.comp (algebraMap S' (S' ⊗[S] (S' ⊗[S] S'))) =
      ((Algebra.TensorProduct.map (AlgHom.id S S')
          (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom).comp
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom :=
  RingHom.ext fun t => by simp [cyc₃_tmul, Algebra.TensorProduct.one_def]

/-- The global functions on `X'''` coming from `S' ⊗ (S' ⊗ S')`. -/
abbrev κ₃ {X''' : Scheme.{u}} (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S')))) :
    S' ⊗[S] (S' ⊗[S] S') →+* Γ(X''', ⊤) :=
  (f'''.appLE ⊤ ⊤ le_top).hom.comp (ΓinvA (S' ⊗[S] (S' ⊗[S] S')))

/-- Functions pulled back along a map over a ring map. -/
theorem appTop_κ {X'' X''' : Scheme.{u}} {f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))}
    {f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S')))} (b : X''' ⟶ X'')
    (m : S' ⊗[S] S' →+* S' ⊗[S] (S' ⊗[S] S'))
    (hw : b ≫ f'' = f''' ≫ Spec.map (CommRingCat.ofHom m)) (x : S' ⊗[S] S') :
    b.appTop (κ S' X'' f'' x) = κ₃ S' f''' (m x) := by
  simp only [κ, κ₃, RingHom.comp_apply]
  repeat erw [Scheme.Hom.appLE_top_top_eq_appTop]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  first
  | exact congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))
  | exact (congrArg (fun φ => φ.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m))).symm
  | (have := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m)) x); simpa using this.symm)

variable (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
  (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
  (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
  (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
  [hL : L'.IsInvertible] [IsProper f']

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
  haveI := isQuasicoherent_L X' L'
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

end Span

end ZInQ.Contrib.CloudR2NOS.Descent
