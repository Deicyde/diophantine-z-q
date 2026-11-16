/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean
  Retrieved      : 2026-11-14 (raw.githubusercontent.com, byte-for-byte)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original.
The changes are mechanical, except that two self-test sections were deleted (noted below).
No statement, hypothesis, definition or proof term that the port depends on was altered,
weakened or omitted:
  * 74 line(s) of `#print axioms` / `#guard_msgs` audit removed (diagnostics only; no proof term).
  * 1 scope(s) the source leaves open at EOF closed explicitly (end) so the port namespace can be closed; Lean closes these implicitly at EOF in the original, so this is a no-op.
  * one `w03_open "AlgebraicGeometry"` inserted after the port namespace: this file `open`s `AlgebraicGeometry`, which the port also declares as nested namespace(s), so a
    plain `open` would resolve to the nested one and hide Mathlib's. The dual root+prefix
    shim keeps the Mathlib root namespace(s) visible, exactly as in the original.
  * `import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil` added (the original imported only
    Mathlib; the port needs it for the `w03_open` shim below).
  * the self-test sections `section SatGates` and `section TeethGate` (6 `gate_*`/`isEmpty_*`
    sanity theorems on ℤ_[p], including the generic-fibre-only counterexample) DELETED. They are
    diagnostics, not part of the mathematics: nothing in the 81-file closure, in Basic.lean or in
    Main references any of their names (verified by search before removal). Everything in
    `NeronModelInfra` that the closure uses — the interface (`specGenericFibreInclusion`,
    `SchemeHomOver`, `genericFibreRestrict`, `NeronUniqueExtension`, `NeronModelPropertyBundle`),
    `ComparisonHooks`, `RestrictHooks` and `IsoEngines` — is retained unchanged.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra

variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]

def specGenericFibreInclusion : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

@[simp]
theorem specGenericFibreInclusion_eq :
    specGenericFibreInclusion R K = Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  rfl

abbrev SchemeHomOver {B Y X : Scheme.{u}} (g : Y ⟶ B) (f : X ⟶ B) :=
  {φ : Y ⟶ X // φ ≫ f = g}

variable {X Y : Scheme.{u}}

def genericFibreRestrict (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver g f) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)) :=
  ⟨pullback.lift (pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1)
      (pullback.snd g (specGenericFibreInclusion R K))
      (by rw [Category.assoc, φ.2, pullback.condition]),
    pullback.lift_snd _ _ _⟩

def NeronUniqueExtension (f : X ⟶ Spec (CommRingCat.of R)) : Prop :=
  ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
    Function.Bijective (genericFibreRestrict R K f t)

theorem neronUniqueExtension_iff_bijective (f : X ⟶ Spec (CommRingCat.of R)) :
    NeronUniqueExtension R K f ↔
      ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t →
        Function.Bijective (genericFibreRestrict R K f t) :=
  Iff.rfl

structure NeronModelPropertyBundle [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
    (f : X ⟶ Spec (CommRingCat.of R)) : Prop where

  smooth : Smooth f

  separated : IsSeparated f

  locallyOfFiniteType : LocallyOfFiniteType f

  quasiCompact : QuasiCompact f

  neronMapping : NeronUniqueExtension R K f

section ComparisonHooks

variable {R K}
variable [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K]
variable {f : X ⟶ Spec (CommRingCat.of R)}

theorem NeronModelPropertyBundle.smooth_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.Smooth f :=
  h.smooth

theorem NeronModelPropertyBundle.isSeparated_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.IsSeparated f :=
  h.separated

theorem NeronModelPropertyBundle.locallyOfFiniteType_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.LocallyOfFiniteType f :=
  h.locallyOfFiniteType

theorem NeronModelPropertyBundle.quasiCompact_mathlibSpelling
    (h : NeronModelPropertyBundle R K f) : AlgebraicGeometry.QuasiCompact f :=
  h.quasiCompact

theorem NeronModelPropertyBundle.neronMapping_bijective
    (h : NeronModelPropertyBundle R K f) (T : Scheme.{u})
    (t : T ⟶ Spec (CommRingCat.of R)) (ht : Smooth t) :
    Function.Bijective (genericFibreRestrict R K f t) :=
  h.neronMapping T t ht

theorem neronModelPropertyBundle_iff_propertyList (f : X ⟶ Spec (CommRingCat.of R)) :
    NeronModelPropertyBundle R K f ↔
      (Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
        NeronUniqueExtension R K f) :=
  ⟨fun h => ⟨h.smooth, h.separated, h.locallyOfFiniteType, h.quasiCompact, h.neronMapping⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

theorem NeronModelPropertyBundle.existsUnique_extension
    (h : NeronModelPropertyBundle R K f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (ht : Smooth t)
    (v : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃! φ : SchemeHomOver t f, genericFibreRestrict R K f t φ = v :=
  (h.neronMapping T t ht).existsUnique v

end ComparisonHooks

section RestrictHooks

variable {R K}
variable (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))

@[simp]
theorem genericFibreRestrict_coe_comp_snd (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd g (specGenericFibreInclusion R K) :=
  (genericFibreRestrict R K f g φ).2

@[simp]
theorem genericFibreRestrict_coe_comp_fst (φ : SchemeHomOver g f) :
    (genericFibreRestrict R K f g φ).1 ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst g (specGenericFibreInclusion R K) ≫ φ.1 :=
  pullback.lift_fst _ _ _

theorem genericFibreRestrict_coe_eq_pullbackMap (φ : SchemeHomOver g f)
    (eq₁ : g ≫ 𝟙 (Spec (CommRingCat.of R)) = φ.1 ≫ f)
    (eq₂ : specGenericFibreInclusion R K ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (Spec (CommRingCat.of K)) ≫ specGenericFibreInclusion R K) :
    (genericFibreRestrict R K f g φ).1 =
      pullback.map g (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K)
        φ.1 (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of R))) eq₁ eq₂ := by
  apply pullback.hom_ext
  · simp [genericFibreRestrict, pullback.map]
  · simp [genericFibreRestrict, pullback.map]

end RestrictHooks

section IsoEngines

theorem subsingleton_schemeHomOver_of_isIso {B Y' X' : Scheme.{u}} (g : Y' ⟶ B) (f : X' ⟶ B)
    [IsIso f] : Subsingleton (SchemeHomOver g f) := by
  constructor
  intro a b
  apply Subtype.ext
  have ha : a.1 = g ≫ inv f := by
    have h0 : a.1 = (a.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [a.2] at h0
    exact h0
  have hb : b.1 = g ≫ inv f := by
    have h0 : b.1 = (b.1 ≫ f) ≫ inv f := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [b.2] at h0
    exact h0
  rw [ha, hb]

theorem nonempty_schemeHomOver_of_isIso {B Y' X' : Scheme.{u}} (g : Y' ⟶ B) (f : X' ⟶ B)
    [IsIso f] : Nonempty (SchemeHomOver g f) :=
  ⟨⟨g ≫ inv f, by rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]⟩⟩

theorem genericFibreRestrict_bijective_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f]
    (g : Y ⟶ Spec (CommRingCat.of R)) :
    Function.Bijective (genericFibreRestrict R K f g) := by
  constructor
  · intro a b _
    exact (subsingleton_schemeHomOver_of_isIso g f).allEq a b
  · intro v
    obtain ⟨φ⟩ := nonempty_schemeHomOver_of_isIso g f
    exact ⟨φ, (subsingleton_schemeHomOver_of_isIso
      (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))).allEq _ v⟩

theorem neronUniqueExtension_of_isIso (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] :
    NeronUniqueExtension R K f :=
  fun _ t _ => genericFibreRestrict_bijective_of_isIso R K f t

theorem neronModelPropertyBundle_id [IsDomain R] [IsDedekindDomain R] [IsFractionRing R K] :
    NeronModelPropertyBundle R K (𝟙 (Spec (CommRingCat.of R))) :=
  { smooth := inferInstance
    separated := inferInstance
    locallyOfFiniteType := inferInstance
    quasiCompact := inferInstance
    neronMapping := neronUniqueExtension_of_isIso R K (𝟙 (Spec (CommRingCat.of R))) }

end IsoEngines

end NeronModelInfra

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
