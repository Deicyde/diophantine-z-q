/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

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

theorem cyc₃_tmul (a b c : S') : cyc₃ S' (a ⊗ₜ (b ⊗ₜ c)) = b ⊗ₜ (c ⊗ₜ a) := rfl

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
  simp only [κ, κ₃, RingHom.comp_apply, Scheme.Hom.appLE_top_top_eq_appTop]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom m)) x)
  simpa using this.symm

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
      (CommRingCat.isIso_iff_bijective _).mpr (cyc₃ (S := S) S').bijective
    infer_instance
  rw [hsw] at h₀
  exact IsPullback.of_iso h₀ (Iso.refl _) (Iso.refl _)
    (asIso (Spec.map (CommRingCat.ofHom (cyc₃ (S := S) S').toAlgHom.toRingHom))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- **G** : `S' ⊗[S] (S' ⊗[S] Γ(L', ⊤)) ≃+ Γ((b₁₃ ≫ a₂)^*L', ⊤)`,
`s ⊗ (t ⊗ n) ↦ κ₃ (s ⊗ (t ⊗ 1)) • (b₁₃ ≫ a₂)^* n`. -/
noncomputable def G₃
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom))) :
    (letI := moduleTop f' L'; letI := moduleTopS S' f' L';
      S' ⊗[S] (S' ⊗[S] Γ(L', ⊤))) ≃+ Γ((Scheme.Modules.pullback (b₁₃ ≫ a₂)).obj L', ⊤) :=
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  haveI := isScalarTower_top S' f' L'
  haveI := isQuasicoherent_L X' L'
  (TensorProduct.assoc S S' S' Γ(L', ⊤)).symm.toAddEquiv.trans
    ((tensorBaseChangeAddEquiv S S' (S' ⊗[S] S') Γ(L', ⊤)).trans
      (AddEquiv.ofBijective (sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L')
        (bijective_sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L')))

theorem G₃_tmul
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))))
    (s t : S') (n : Γ(L', ⊤)) :
    G₃ S' X' f' L' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃
        (letI := moduleTop f' L'; letI := moduleTopS S' f' L'; s ⊗ₜ (t ⊗ₜ n)) =
      κ₃ S' f''' (s ⊗ₜ (t ⊗ₜ 1)) • pbSec (b₁₃ ≫ a₂) n := by
  letI := moduleTop f' L'
  letI := moduleTopS S' f' L'
  change sectionsBC (isPullback_third S' X' f' X'' f'' a₂ X''' f''' b₁₃ ha₂ hb₁₃) L'
      ((1 ⊗ₜ (s ⊗ₜ t)) ⊗ₜ n) = _
  rw [sectionsBC_tmul]
  congr 1
  rw [Scheme.Hom.appLE_top_top_eq_appTop, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply, ← ΓinvA_algebraMap (A := S' ⊗[S] (S' ⊗[S] S')) (B := S' ⊗[S] (S' ⊗[S] S'))]
  change (f'''.appTop).hom (ΓinvA _ ((cyc₃ (S := S) S') (1 ⊗ₜ (s ⊗ₜ t)))) = _
  rw [cyc₃_tmul, Scheme.Hom.appLE_top_top_eq_appTop]
  rfl

end Span

end ZInQ.Contrib.CloudR2NOS.Descent
