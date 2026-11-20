/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.lean
  Source sha256  : ddabc61c284058e566af05344432ce88273e5d4d8ad331e1225953095faa3730
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
r2nos_erase_attr "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology"

universe u

namespace SolCH
r2nos_namespace_dual

section Coprod

lemma coprodMap_of {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y') (ha : P a) (hb : P b) :
    P (coprod.map a b) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{u, u} X' Y') ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · show P (pullback.snd (coprod.map a b) coprod.inl)
    have hP := (isPullback_inl_inl_coprodMap a b).flip
    rw [← hP.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso _ _).mpr ha
  · show P (pullback.snd (coprod.map a b) coprod.inr)
    have hP := (isPullback_inr_inr_coprodMap a b).flip
    rw [← hP.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso _ _).mpr hb

scoped instance isOpenImmersion_coprodMap {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsOpenImmersion a] [IsOpenImmersion b] : IsOpenImmersion (coprod.map a b) :=
  coprodMap_of (P := @IsOpenImmersion) a b ‹_› ‹_›

scoped instance isProper_coprodMap {X Y X' Y' : Scheme.{u}} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsProper a] [IsProper b] : IsProper (coprod.map a b) :=
  coprodMap_of (P := @IsProper) a b ‹_› ‹_›

scoped instance isProper_coprodDesc {U V X : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X)
    [IsProper a] [IsProper b] : IsProper (coprod.desc a b) := by
  have : coprod.desc a b = coprod.map a b ≫ coprod.desc (𝟙 X) (𝟙 X) := by
    ext <;> simp
  rw [this]
  infer_instance

lemma range_coprodDesc {U V X : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ X) :
    Set.range (coprod.desc a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨(w | w), rfl⟩ := (coprodMk U V).surjective w
    · left
      refine ⟨w, ?_⟩
      rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]
    · right
      refine ⟨w, ?_⟩
      rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]
  · rintro (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact ⟨(coprod.inl : U ⟶ U ⨿ V) w, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : V ⟶ U ⨿ V) w, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

end Coprod

section Envelope

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def HasEnvelope (S : Set X) : Prop :=
  ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
    IsProper π ∧ Set.range π = S ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f

lemma HasEnvelope.empty : HasEnvelope f ∅ := by
  refine ⟨∅, ∅, Scheme.emptyTo X, 𝟙 _, Scheme.emptyTo _, ?_, ?_, inferInstance, ?_, Subsingleton.elim _ _⟩
  · haveI : IsClosedImmersion (Scheme.emptyTo X) :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Set.range_eq_empty]; exact isClosed_empty)
    infer_instance
  · exact Set.range_eq_empty _
  · haveI : IsClosedImmersion (Scheme.emptyTo (Spec (CommRingCat.of A))) :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Set.range_eq_empty]; exact isClosed_empty)
    infer_instance

variable {f}

lemma HasEnvelope.union {S T : Set X} (hS : HasEnvelope f S) (hT : HasEnvelope f T) :
    HasEnvelope f (S ∪ T) := by
  obtain ⟨X₁, P₁, π₁, j₁, q₁, hπ₁, hr₁, hj₁, hq₁, h₁⟩ := hS
  obtain ⟨X₂, P₂, π₂, j₂, q₂, hπ₂, hr₂, hj₂, hq₂, h₂⟩ := hT
  refine ⟨X₁ ⨿ X₂, P₁ ⨿ P₂, coprod.desc π₁ π₂, coprod.map j₁ j₂, coprod.desc q₁ q₂,
    inferInstance, ?_, inferInstance, inferInstance, ?_⟩
  · rw [range_coprodDesc, hr₁, hr₂]
  · ext
    · simp [h₁, h₂]
    · simp [h₁, h₂]

variable (f)

lemma HasEnvelope.of_isIntegral [IsNoetherianRing A] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] {Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i] :
    HasEnvelope f (Set.range i) := by
  obtain ⟨X', P, π', j, q, hπ', hsurj, hj, hq, hcomm⟩ :=
    AlgebraicGeometry.exists_isProper_surjective_isOpenImmersion_comp_eq_of_isIntegral (i ≫ f)
  refine ⟨X', P, π' ≫ i, j, q, inferInstance, ?_, hj, hq, by rw [hcomm, Category.assoc]⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.surj.range_eq, Set.image_univ]

end Envelope

section Reduced

variable {X : Scheme.{u}}

lemma isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  haveI : ∀ U : X.affineOpens, _root_.IsReduced ((Γ(X, (U : X.Opens)) : Type u) ⧸ I.ideal U) :=
      fun U => by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    show (I.ideal U).IsRadical
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    exact PrimeSpectrum.isRadical_vanishingIdeal _
  haveI : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := fun U => by
    show IsReduced (Spec (.of ((Γ(X, (U : X.Opens)) : Type u) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

lemma isIntegral_subscheme_vanishingIdeal (Z : Closeds X) (hZ : IsIrreducible (Z : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  haveI := isReduced_subscheme_vanishingIdeal Z
  haveI : IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    have h : IsIrreducible ((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) := by
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact Subtype.irreducibleSpace h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end Reduced

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

lemma hasEnvelope_of_mem_irreducibleComponents (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    HasEnvelope f Z := by
  let Zc : Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  haveI := isIntegral_subscheme_vanishingIdeal Zc hZ.1
  have := HasEnvelope.of_isIntegral f (Scheme.IdealSheafData.vanishingIdeal Zc).subschemeι
  rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    at this

lemma hasEnvelope_biUnion (s : Finset (Set X)) (hs : ↑s ⊆ irreducibleComponents X) :
    HasEnvelope f (⋃ Z ∈ s, Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasEnvelope.empty f
  | insert Z s hZs ih =>
    rw [Finset.set_biUnion_insert]
    rw [Finset.coe_insert] at hs
    exact (hasEnvelope_of_mem_irreducibleComponents f Z (hs (Set.mem_insert _ _))).union
      (ih ((Set.subset_insert _ _).trans hs))

theorem main :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian X := {}
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  obtain ⟨X', P, π, j, q, hπ, hr, hj, hq, hc⟩ :=
    hasEnvelope_biUnion f hfin.toFinset (by simp)
  refine ⟨X', P, π, j, q, hπ, ⟨?_⟩, hj, hq, hc⟩
  rw [← Set.range_eq_univ, hr, Set.eq_univ_iff_forall]
  intro x
  simp only [Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]
  exact ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

end Main

end SolCH
w03_reactivate "P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated.SolCH"

theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ (X' P : Scheme.{u}) (π : X' ⟶ X) (j : X' ⟶ P) (q : P ⟶ Spec (CommRingCat.of A)),
      IsProper π ∧ Surjective π ∧ IsOpenImmersion j ∧ IsProper q ∧ j ≫ q = π ≫ f :=
  SolCH.main f
end S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_comp_eq_of_isSeparated
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
