/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.lean
  Source sha256  : a4c6aa3040e1baa2711d768197a89ff2c14866f6343d9a82f9bf25ca5a84cde8
  Retrieved      : byte-for-byte at the source revision above
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_forall_exists_quotient_restrict
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

universe u

namespace Q1SCH
r2nos_namespace_dual

theorem exists_invariant_affine_cover
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ W : X → X.Opens, (∀ x, IsAffineOpen (W x)) ∧ (∀ x, x ∈ W x) ∧ (∀ x, s ⁻¹ᵁ W x = t ⁻¹ᵁ W x) := by
  choose U hU hxU using haff
  choose W hW hxW _ hinv using fun x =>
    AlgebraicGeometry.Scheme.exists_invariant_isAffineOpen_of_finiteLocallyFree_equivalenceRelation s t hequiv (hU x) (hxU x)
  exact ⟨W, hW, hxW, hinv⟩

section restrict

variable {X R : Scheme.{u}} (s t : R ⟶ X) (W : X.Opens) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W)

noncomputable def sW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme := s ∣_ W

noncomputable def tW : (s ⁻¹ᵁ W).toScheme ⟶ W.toScheme := (R.isoOfEq hinv).hom ≫ (t ∣_ W)

theorem sW_ι : sW s W ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ s := by simp [sW]

theorem tW_ι : tW s t W hinv ≫ W.ι = (s ⁻¹ᵁ W).ι ≫ t := by simp [tW]

theorem isPullback_sW : IsPullback (s ⁻¹ᵁ W).ι (sW s W) s W.ι :=
  (isPullback_morphismRestrict s W).flip

theorem isPullback_tW : IsPullback (s ⁻¹ᵁ W).ι (tW s t W hinv) t W.ι := by
  refine (isPullback_morphismRestrict t W).flip.of_iso (R.isoOfEq hinv).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · simp [tW]

scoped instance [IsFinite s] : IsFinite (sW s W) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_sW s W) inferInstance
scoped instance [Flat s] : Flat (sW s W) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_sW s W) inferInstance
scoped instance [LocallyOfFinitePresentation s] : LocallyOfFinitePresentation (sW s W) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_sW s W)
    inferInstance
theorem tW_finite [IsFinite t] : IsFinite (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_tW s t W hinv) inferInstance
theorem tW_flat [Flat t] : Flat (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback_tW s t W hinv) inferInstance
theorem tW_lfp [LocallyOfFinitePresentation t] : LocallyOfFinitePresentation (tW s t W hinv) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_tW s t W hinv)
    inferInstance

theorem mono_restrict
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    {T : Scheme.{u}} (a b : T ⟶ (s ⁻¹ᵁ W).toScheme) (h₁ : a ≫ sW s W = b ≫ sW s W)
    (h₂ : a ≫ tW s t W hinv = b ≫ tW s t W hinv) : a = b := by
  rw [← cancel_mono (s ⁻¹ᵁ W).ι]
  apply hmono
  · rw [Category.assoc, Category.assoc, ← sW_ι, reassoc_of% h₁]
  · rw [Category.assoc, Category.assoc, ← tW_ι s t W hinv, reassoc_of% h₂]

theorem rel_restrict_iff {T : Scheme.{u}} (x y : T ⟶ W.toScheme) :
    (∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ sW s W = x ∧ φ ≫ tW s t W hinv = y) ↔
      ∃ ψ : T ⟶ R, ψ ≫ s = x ≫ W.ι ∧ ψ ≫ t = y ≫ W.ι := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨φ ≫ (s ⁻¹ᵁ W).ι, by rw [Category.assoc, Category.assoc, sW_ι],
      by rw [Category.assoc, Category.assoc, tW_ι]⟩
  · rintro ⟨ψ, h₁, h₂⟩
    have hrange : Set.range ψ.base ⊆ Set.range (s ⁻¹ᵁ W).ι.base := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      change s (ψ p) ∈ W
      rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
      exact (x p).2
    refine ⟨IsOpenImmersion.lift (s ⁻¹ᵁ W).ι ψ hrange, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, sW_ι, ← Category.assoc, IsOpenImmersion.lift_fac, h₁]
    · rw [← cancel_mono W.ι, Category.assoc, tW_ι, ← Category.assoc, IsOpenImmersion.lift_fac, h₂]

theorem equivalence_restrict
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (T : Scheme.{u}) :
    _root_.Equivalence fun x y : T ⟶ W.toScheme =>
      ∃ φ : T ⟶ (s ⁻¹ᵁ W).toScheme, φ ≫ sW s W = x ∧ φ ≫ tW s t W hinv = y := by
  have E := hequiv T
  exact
    { refl := fun x => (rel_restrict_iff s t W hinv x x).2 (E.refl _)
      symm := fun h => (rel_restrict_iff s t W hinv _ _).2 (E.symm ((rel_restrict_iff s t W hinv _ _).1 h))
      trans := fun h h' => (rel_restrict_iff s t W hinv _ _).2
        (E.trans ((rel_restrict_iff s t W hinv _ _).1 h) ((rel_restrict_iff s t W hinv _ _).1 h')) }

end restrict

theorem main {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) := by
  obtain ⟨W, hW, hxW, hinv⟩ := exists_invariant_affine_cover s t hequiv haff

  have loc : ∀ x : X, ∃ (Y : Scheme.{u}) (_ : IsAffine Y) (p : (W x).toScheme ⟶ Y)
      (w : sW s (W x) ≫ p = tW s t (W x) (hinv x) ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback (sW s (W x)) (tW s t (W x) (hinv x)) p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
    fun x => by
      haveI : IsAffine (W x).toScheme := hW x
      haveI := tW_finite s t (W x) (hinv x)
      haveI := tW_flat s t (W x) (hinv x)
      haveI := tW_lfp s t (W x) (hinv x)
      exact AlgebraicGeometry.Scheme.exists_affine_quotient_of_finiteLocallyFree_equivalenceRelation (sW s (W x)) (tW s t (W x) (hinv x))
        (fun a b h₁ h₂ => mono_restrict s t (W x) (hinv x) hmono a b h₁ h₂)
        (equivalence_restrict s t (W x) (hinv x) hequiv)

  refine AlgebraicGeometry.Scheme.exists_quotient_of_forall_exists_quotient_restrict s t W hxW hinv fun x => ?_
  obtain ⟨Y, _, p, w, h₁, h₂, h₃, h₄, h₅, -⟩ := loc x
  exact ⟨Y, p, w, h₁, h₂, h₃, h₄, h₅⟩

end Q1SCH
w03_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation.Q1SCH"

theorem solution
    {X R : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (haff : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ r : R, s r = x → t r ∈ U) :
    ∃ (Y : Scheme.{u}) (p : X ⟶ Y) (w : s ≫ p = t ≫ p),
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      IsPullback s t p p ∧ Nonempty (IsColimit (Cofork.ofπ p w)) :=
  Q1SCH.main s t hmono hequiv haff
end S_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
