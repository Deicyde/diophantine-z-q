/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under the Apache License, Version 2.0.

OWN pure-Mathlib global-functions backend, OUTSIDE Source. Mathematical API
provenance: Mathlib at 56a005855ea17e0b0958f73ec801ae140b0a1679,
AlgebraicGeometry/Morphisms/{Proper,Flat}.lean (Christian Merten, Andrew Yang),
AlgebraicGeometry/Scheme.lean, and CategoryTheory/Limits/Shapes/Pullback/
IsPullback/Basic.lean (Kim Morrison, Joël Riou, Calle Sönne). Their existing
source copyright/license notices remain unchanged.

SOURCE PREPARATION ONLY. No compiler selection or kernel grade is claimed.
The generic f/epsilon interface is intermediate geometry: the original-G
wrapper is separately owned by the H5 lead and derives the actual identity
section. No epsilon/hH0/unit/bundle premise is added to final NOS.

The proof constructs actual global units, an actual Gamma isomorphism with
hom=f.appTop and inv=epsilon.appTop, and actual canonical flat-base-change
Gamma pushout legs for EVERY commutative field-base algebra B. No Field,
Noetherian, nontrivial or finite condition is imposed on B. No dimension
argument, supplied hH0, SourceSectionsTwoTerm, Source law/cohomology alias,
new point, source/provider/view/root/cache/pin action or numerical option.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Lean
import Lean.Util.CollectAxioms

set_option autoImplicit false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions

/-- The existing proper/integral Gamma theorem uses the actual structure map
and existing ring operations, not a cohomology-dimension surrogate. -/
theorem globalFunctions_isField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X] :
    IsField Γ(X, ⊤) :=
  AlgebraicGeometry.isField_of_universallyClosed k f

/-- Every nonzero global function on the SAME proper integral field scheme
is a unit; no caller unit premise or rational point is needed for this fact. -/
theorem nonzero_globalFunctions_are_units {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X] :
    ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a := by
  letI : Field Γ(X, ⊤) := (globalFunctions_isField f).toField
  intro a ha
  exact isUnit_iff_ne_zero.mpr ha

/-- The actual section triangle gives the actual structure/evaluation Gamma
composition. No geometry or map-bijectivity is assumed in this identity. -/
theorem appTop_comp_evaluation {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    f.appTop ≫ ε.appTop = 𝟙 (Γ(Spec (CommRingCat.of k), ⊤)) := by
  rw [← Scheme.Hom.comp_appTop, hε, Scheme.Hom.id_appTop]

private theorem evaluation_injective {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) : Function.Injective ε.appTop := by
  letI : Field Γ(X, ⊤) := (globalFunctions_isField f).toField
  letI : Field Γ(Spec (CommRingCat.of k), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  exact ε.appTop.hom.injective

/-- Evaluation at the actual section is also a left inverse, proved by its
ring-map injectivity and the same section triangle, not by dimensions. -/
theorem evaluation_comp_appTop {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    ε.appTop ≫ f.appTop = 𝟙 (Γ(X, ⊤)) := by
  have hinj : Function.Injective ε.appTop := evaluation_injective f ε
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply hinj
  change ε.appTop (f.appTop (ε.appTop a)) = ε.appTop a
  simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
    (ConcreteCategory.congr_hom (appTop_comp_evaluation f ε hε) (ε.appTop a))

/-- The Gamma isomorphism is the literal structure map and literal original
section evaluation. It is not an arbitrary ring/vector-space isomorphism. -/
def appTopIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    Γ(Spec (CommRingCat.of k), ⊤) ≅ Γ(X, ⊤) where
  hom := f.appTop
  inv := ε.appTop
  hom_inv_id := appTop_comp_evaluation f ε hε
  inv_hom_id := evaluation_comp_appTop f ε hε

theorem appTopIso_hom {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    (appTopIso f ε hε).hom = f.appTop := rfl

theorem appTopIso_inv {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    (appTopIso f ε hε).inv = ε.appTop := rfl

theorem appTop_isIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) : IsIso f.appTop :=
  (appTopIso f ε hε).isIso_hom

theorem appTop_bijective {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    Function.Bijective f.appTop := by
  haveI : IsIso f.appTop := appTop_isIso f ε hε
  exact ConcreteCategory.bijective_of_isIso f.appTop

/-- Canonical TOP restriction agrees with the actual appTop map. This is the
existing pinned map equality, not a custom scalar action or alternate map. -/
private theorem appLE_top_eq_appTop {X S : Scheme.{u}} (f : X ⟶ S)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) :
    f.appLE ⊤ ⊤ h = f.appTop :=
  Scheme.Hom.appLE_eq_app f

/-- The actual field-base-change square is a Gamma pushout at TOP, even when
B is the zero ring or is not Noetherian/a field. Only properness is needed
for source qcqs; the section/integrality is used later on its upper leg. -/
theorem appTop_baseChange_isPushout {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (B : Type u) [CommRing B] [Algebra k B] :
    IsPushout f.appTop
      (Spec.map (CommRingCat.ofHom (algebraMap k B))).appTop
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop := by
  let σB : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k B))
  haveI : Flat σB := inferInstance
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have H : IsPullback (pullback.fst f σB) (pullback.snd f σB) f σB :=
    IsPullback.of_hasPullback f σB
  have hST : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤
      σB ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) :=
    (Scheme.Hom.preimage_top σB).ge
  have hSX : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) :=
    (Scheme.Hom.preimage_top f).ge
  have hY : (⊤ : (pullback f σB).Opens) =
      (pullback.fst f σB) ⁻¹ᵁ (⊤ : X.Opens) ⊓
        (pullback.snd f σB) ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of B)).Opens) := by
    simp
  have hQC : IsCompact ((⊤ : X.Opens) : Set X) := by
    rw [Opens.coe_top]
    exact isCompact_univ
  have hQS : IsQuasiSeparated ((⊤ : X.Opens) : Set X) := by
    simpa only [Opens.coe_top] using
      (isQuasiSeparated_univ : IsQuasiSeparated (Set.univ : Set X))
  have hSection : IsIso (pushoutSection H hST hSX hY) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hST hSX hY
      (isAffineOpen_top (Spec (CommRingCat.of k)))
      (isAffineOpen_top (Spec (CommRingCat.of B))) hQC hQS
  have hSquare := (isIso_pushoutSection_iff H hST hSX hY).mp hSection
  change IsPushout f.appTop σB.appTop
    (pullback.fst f σB).appTop (pullback.snd f σB).appTop
  simpa only [appLE_top_eq_appTop] using hSquare

/-- The LOWER Gamma pushout leg is the literal second projection. Its
isomorphism follows from the actual upper f.appTop isomorphism. -/
theorem baseChange_appTop_isIso {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)
    (B : Type u) [CommRing B] [Algebra k B] :
    IsIso (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop := by
  haveI : IsIso f.appTop := appTop_isIso f ε hε
  exact (appTop_baseChange_isPushout f B).isIso_inr_of_isIso

/-- Literal per-test-ring bijectivity, without a B-field/Noetherian/nonzero
restriction or an assumed hH0/model. -/
theorem baseChange_appTop_bijective {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)
    (B : Type u) [CommRing B] [Algebra k B] :
    Function.Bijective
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop := by
  haveI : IsIso
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop :=
    baseChange_appTop_isIso f ε hε B
  exact ConcreteCategory.bijective_of_isIso _

/-- The exact all-commutative-test-ring hH0 interface, produced from f and the
actual section triangle. Original-G production of f/ε is a separate consumer. -/
theorem all_baseChange_appTop_bijective {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
    (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _) :
    ∀ (B : Type u) [CommRing B] [Algebra k B],
      Function.Bijective
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop := by
  intro B instB instkB
  exact baseChange_appTop_bijective f ε hε B

/-! Embedded independent audit, SOURCE-prepared and unexecuted until selected.
No project/Source/W07/cohomodel or original-G wrapper import is permitted. -/
namespace Audit
open Lean Meta Elab Command

private abbrev EField : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X], IsField Γ(X, ⊤)
private abbrev EUnits : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X],
  ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a
private abbrev ERightInverse : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (ε : Spec (CommRingCat.of k) ⟶ X),
  ε ≫ f = 𝟙 _ → f.appTop ≫ ε.appTop = 𝟙 (Γ(Spec (CommRingCat.of k), ⊤))
private abbrev ELeftInverse : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X),
  ε ≫ f = 𝟙 _ → ε.appTop ≫ f.appTop = 𝟙 (Γ(X, ⊤))
private abbrev EIso := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  Γ(Spec (CommRingCat.of k), ⊤) ≅ Γ(X, ⊤)
private abbrev EHom : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  (appTopIso f ε hε).hom = f.appTop
private abbrev EInv : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  (appTopIso f ε hε).inv = ε.appTop
private abbrev EIsIso : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X), ε ≫ f = 𝟙 _ → IsIso f.appTop
private abbrev EBijective : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X), ε ≫ f = 𝟙 _ → Function.Bijective f.appTop
private abbrev ESquare : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  (B : Type u) [CommRing B] [Algebra k B],
  IsPushout f.appTop (Spec.map (CommRingCat.ofHom (algebraMap k B))).appTop
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev EBaseIso : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)
  (B : Type u) [CommRing B] [Algebra k B],
  IsIso (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev EBaseBijective : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _)
  (B : Type u) [CommRing B] [Algebra k B],
  Function.Bijective
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev EAllB : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [CommRing B] [Algebra k B],
  Function.Bijective
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop

private abbrev NUnitsNoProper : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X],
  ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a
private abbrev NUnitsNoIntegral : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f],
  ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a
private abbrev NUnitsZeroAllowed : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X],
  ∀ a : Γ(X, ⊤), IsUnit a
private abbrev NUnitsSupplied : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X],
  (∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a) → ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a
private abbrev NBijectiveNoTriangle : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X), Function.Bijective f.appTop
private abbrev NBijectiveSupplied : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  Function.Bijective f.appTop → Function.Bijective f.appTop
private abbrev NFieldTestB : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [Field B] [Algebra k B],
  Function.Bijective
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev NNoetherianTestB : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [Algebra k B],
  Function.Bijective
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev NExcludeZeroTestB : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [CommRing B] [Nontrivial B] [Algebra k B],
  Function.Bijective
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev NSuppliedH0 : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  (∀ (B : Type u) [CommRing B] [Algebra k B],
    Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop) →
  ∀ (B : Type u) [CommRing B] [Algebra k B],
    Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev NWrongProjection : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [CommRing B] [Algebra k B],
    Function.Bijective (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop
private abbrev NOnlyIdentityBase : Prop := ∀ {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  Function.Bijective (pullback.snd f (𝟙 (Spec (CommRingCat.of k)))).appTop
private abbrev NGeneralRingBase : Prop := ∀ {k : Type u} [CommRing k] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsIntegral X]
  (ε : Spec (CommRingCat.of k) ⟶ X) (hε : ε ≫ f = 𝟙 _),
  ∀ (B : Type u) [CommRing B] [Algebra k B],
  Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k B)))).appTop

private def rigid (n expected : Name) (kind : String) : MetaM Unit := do
  let ci ← getConstInfo n
  let ei ← getConstInfo expected
  let v ← match ei with | .defnInfo d => pure d.value | _ => throwError "Missing literal Gamma audit type"
  let actualKind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | _ => "other"
  unless actualKind == kind do throwError "Pure-Mathlib Gamma wrong kind {n}: {actualKind}"
  unless ci.levelParams.length == 1 && ei.levelParams.length == 1 do
    throwError "Pure-Mathlib Gamma rigid-u arity mismatch {n}"
  let rhs := v.instantiateLevelParams ei.levelParams (ci.levelParams.map Level.param)
  if ci.type.hasMVar || rhs.hasMVar || ci.type.hasLevelMVar || rhs.hasLevelMVar then
    throwError "Pure-Mathlib Gamma entire type contains metavariables"
  unless ← isDefEq ci.type rhs do throwError "Pure-Mathlib Gamma ENTIRE literal type mismatch {n}: {ci.type}"
  let axes ← collectAxioms n
  for a in axes do
    unless #[`propext, `Classical.choice, `Quot.sound].contains a do
      throwError "Pure-Mathlib Gamma forbidden transitive axiom {n}: {a}"
  logInfo m!"PURE_MATHLIB_GAMMA_WHOLE_KIND_RIGID_U_AX3_OK {n}: {axes}"
  if ← isDefEq ci.type (ci.type.instantiateLevelParams ci.levelParams [Level.zero]) then
    throwError "Pure-Mathlib Gamma silently specialized to Type0 {n}"
  logInfo m!"PURE_MATHLIB_GAMMA_TYPE0_NEGATIVE_REJECTED {n}"

private def reject (n wrong : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let wi ← getConstInfo wrong
  let w ← match wi with | .defnInfo d => pure d.value | _ => throwError "Missing explicit negative Gamma type"
  if ci.levelParams.length == wi.levelParams.length then
    if ← isDefEq ci.type (w.instantiateLevelParams wi.levelParams (ci.levelParams.map Level.param)) then
      throwError "Pure-Mathlib Gamma forbidden changed/premised signature accepted {wrong}"
  logInfo m!"PURE_MATHLIB_GAMMA_NEGATIVE_REJECTED {wrong}"

/-- Inspect only this unit's existing private/proof auxiliaries, not imported
Source/provider proofs. Map data and named existing Mathlib origins must be real. -/
private def bodyUses (n : Name) (required : Array Name) : MetaM Unit := do
  let mut pending := #[n]
  let mut seen : Array Name := #[]
  let mut all : Array Name := #[]
  while !pending.isEmpty do
    let current := pending.back!
    pending := pending.pop
    unless seen.contains current do
      seen := seen.push current
      let ci ← getConstInfo current
      let v? := match ci with | .thmInfo d => some d.value | .defnInfo d => some d.value | _ => none
      if let some v := v? then
        for d in v.getUsedConstants do
          all := all.push d
          if (d.toString.startsWith "_private.PureMathlibGlobalFunctions." ||
              (`ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions).isPrefixOf d) &&
              !seen.contains d then pending := pending.push d
  for d in required do
    unless all.contains d do throwError "Pure-Mathlib Gamma actual body/map origin missing {n}: {d}; got {all}"
    logInfo m!"PURE_MATHLIB_GAMMA_ACTUAL_BODY_MAP_ORIGIN_OK {n}: {d}"
  for d in all do
    if (`Module.finrank : Name).isPrefixOf d || (`Module.rank : Name).isPrefixOf d then
      throwError "Pure-Mathlib Gamma owned proof introduced a rank/dimension shortcut {n}: {d}"

run_cmd liftTermElabM do
  for (n,e,k) in [
      (``globalFunctions_isField, ``EField, "theorem"),
      (``nonzero_globalFunctions_are_units, ``EUnits, "theorem"),
      (``appTop_comp_evaluation, ``ERightInverse, "theorem"),
      (``evaluation_comp_appTop, ``ELeftInverse, "theorem"),
      (``appTopIso, ``EIso, "definition"),
      (``appTopIso_hom, ``EHom, "theorem"),
      (``appTopIso_inv, ``EInv, "theorem"),
      (``appTop_isIso, ``EIsIso, "theorem"),
      (``appTop_bijective, ``EBijective, "theorem"),
      (``appTop_baseChange_isPushout, ``ESquare, "theorem"),
      (``baseChange_appTop_isIso, ``EBaseIso, "theorem"),
      (``baseChange_appTop_bijective, ``EBaseBijective, "theorem"),
      (``all_baseChange_appTop_bijective, ``EAllB, "theorem")] do
    rigid n e k
  for wrong in [``NUnitsNoProper, ``NUnitsNoIntegral, ``NUnitsZeroAllowed, ``NUnitsSupplied] do
    reject ``nonzero_globalFunctions_are_units wrong
  for wrong in [``NBijectiveNoTriangle, ``NBijectiveSupplied] do
    reject ``appTop_bijective wrong
  for wrong in [``NFieldTestB, ``NNoetherianTestB, ``NExcludeZeroTestB, ``NSuppliedH0,
      ``NWrongProjection, ``NOnlyIdentityBase, ``NGeneralRingBase] do
    reject ``all_baseChange_appTop_bijective wrong
  bodyUses ``globalFunctions_isField #[``AlgebraicGeometry.isField_of_universallyClosed]
  bodyUses ``nonzero_globalFunctions_are_units #[``globalFunctions_isField, ``IsField.toField, ``isUnit_iff_ne_zero]
  bodyUses ``appTop_comp_evaluation #[``AlgebraicGeometry.Scheme.Hom.comp_appTop, ``AlgebraicGeometry.Scheme.Hom.id_appTop]
  bodyUses ``evaluation_injective #[``globalFunctions_isField, ``IsField.toField,
    ``AlgebraicGeometry.Scheme.ΓSpecIso, ``Field.toIsField, ``RingHom.injective]
  bodyUses ``evaluation_comp_appTop #[``evaluation_injective, ``appTop_comp_evaluation]
  bodyUses ``appTopIso #[``appTop_comp_evaluation, ``evaluation_comp_appTop]
  bodyUses ``appTop_isIso #[``appTopIso]
  bodyUses ``appTop_bijective #[``appTop_isIso, ``CategoryTheory.ConcreteCategory.bijective_of_isIso]
  bodyUses ``appTop_baseChange_isPushout #[
    ``AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right,
    ``AlgebraicGeometry.isIso_pushoutSection_iff, ``CategoryTheory.IsPullback.of_hasPullback,
    ``AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace,
    ``AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated, ``appLE_top_eq_appTop]
  bodyUses ``baseChange_appTop_isIso #[``appTop_isIso, ``appTop_baseChange_isPushout,
    ``CategoryTheory.IsPushout.isIso_inr_of_isIso]
  bodyUses ``baseChange_appTop_bijective #[``baseChange_appTop_isIso,
    ``CategoryTheory.ConcreteCategory.bijective_of_isIso]
  bodyUses ``all_baseChange_appTop_bijective #[``baseChange_appTop_bijective]
  let env ← getEnv
  unless env.header.mainModule == `PureMathlibGlobalFunctions do
    throwError "Pure-Mathlib Gamma unexpected private logical module"
  for mod in env.header.moduleNames do
    if (`ZInQKernel : Name).isPrefixOf mod || mod == `SourceSectionsTwoTerm ||
        mod == `NativeGeometricSourceInput || mod == `SourceSectionDualTriviality then
      throwError "Pure-Mathlib Gamma imported project/Source/cohomodel/original-G wrapper {mod}"
  logInfo "PURE_MATHLIB_GAMMA_CURRENT_OWN_MODULE_NO_PROJECT_SOURCE_NATIVE_COHOMODEL_IMPORT_OK"
  -- Rfl/data controls: the prepared isomorphism cannot be captioned as the
  -- canonical map unless both actual morphism fields agree literally.
  bodyUses ``appTopIso_hom #[``appTopIso]
  bodyUses ``appTopIso_inv #[``appTopIso]
  logInfo "PURE_MATHLIB_GAMMA_LITERAL_STRUCTURE_HOM_AND_ORIGINAL_EVALUATION_INV_CONTROLS_OK"
  for i in [:env.header.moduleNames.size] do
    let mod := env.header.moduleNames[i]!
    if mod == `Mathlib.AlgebraicGeometry.Morphisms.Proper ||
        mod == `Mathlib.AlgebraicGeometry.Morphisms.Flat ||
        mod == `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic ||
        mod == `Mathlib.AlgebraicGeometry.Scheme || mod == `Mathlib.Algebra.Field.IsField then
      let imps := env.header.moduleData[i]!.imports.map (fun x => x.module.toString)
      logInfo m!"PURE_MATHLIB_GAMMA_ACTUAL_CORE_INPUT_MODULE {mod} {String.intercalate "," imps.toList}"
  logInfo "PURE_MATHLIB_GAMMA_BACKEND_AND_EMBEDDED_AUDITS_FINISHED_COMPONENT_ONLY_NOT_ORIGINAL_G_VA_NOS"
end Audit

end ZInQ.Contrib.CloudR2NOS.FieldAmpleness.PureMathlibGlobalFunctions
