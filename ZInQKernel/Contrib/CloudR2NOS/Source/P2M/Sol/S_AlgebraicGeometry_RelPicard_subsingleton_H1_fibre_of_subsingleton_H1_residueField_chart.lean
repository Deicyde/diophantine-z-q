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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart.lean
  Source sha256  : 359df966690815a3ffd8437a7b21b1b0d80303b417c59f0a9d429a2985497021
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 13 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_subsingleton_H1_sectionsOf_of_subsingleton_H1
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    (hO : Subsingleton ((𝒱.pullback πA 𝔭.asIdeal.ResidueField).sectionsOf
            (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))
            ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A 𝔭.asIdeal.ResidueField))).obj
              ((Scheme.Modules.pullback g').obj M))).H1)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by
  classical
  set K₀ : Type u := 𝔭.asIdeal.ResidueField with hK₀
  set s₁ : Spec (CommRingCat.of K₀) ⟶ T := Scheme.TwoAffineOpenCover.specMap A K₀ ≫ j with hs₁def

  have hcart₁ : IsPullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g')
      (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀)) (pullback.snd c t) s₁ :=
    (IsPullback.of_hasPullback πA (Scheme.TwoAffineOpenCover.specMap A K₀)).paste_horiz hcart
  obtain ⟨𝒲₁, -, ⟨l₁⟩⟩ := exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M s₁
    (pullback.snd πA (Scheme.TwoAffineOpenCover.specMap A K₀))
    (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀) ≫ g') hcart₁
    ((Scheme.Modules.pullback (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀))).obj
      ((Scheme.Modules.pullback g').obj M))
    ((Scheme.Modules.pullbackComp (pullback.fst πA (Scheme.TwoAffineOpenCover.specMap A K₀)) g').app M)
    (𝒱.pullback πA K₀)
  have h₁ : Subsingleton (𝒲₁.sectionsOf (fibreAt c t s₁) (fibreModule c t s₁ M)).H1 := l₁.symm.toEquiv.subsingleton

  have hall : ∀ {k' : Type u} [Field k'] (s' : Spec (CommRingCat.of k') ⟶ T)
      (𝒲a 𝒲b : (pullback (pullback.snd c t) s').TwoAffineOpenCover),
      Subsingleton (𝒲b.sectionsOf (fibreAt c t s') (fibreModule c t s' M)).H1 →
        Subsingleton (𝒲a.sectionsOf (fibreAt c t s') (fibreModule c t s' M)).H1 := by
    intro k' _ s' 𝒲a 𝒲b h
    haveI : IsSeparated (fibreAt c t s') := by unfold fibreAt; infer_instance
    exact Scheme.TwoAffineOpenCover.subsingleton_H1_sectionsOf_of_subsingleton_H1 (fibreAt c t s')
      (fibreModule c t s' M) (hM.pullback _).exists_trivialization 𝒲a 𝒲b h

  obtain ⟨s', hs'⟩ : ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A), s' ≫ j = s := by
    refine ⟨IsOpenImmersion.lift j s ?_, IsOpenImmersion.lift_fac j s _⟩
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k), hs]
    exact ⟨𝔭, rfl⟩
  subst hs'
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of A ⟶ CommRingCat.of k, Spec.map φ = s' := ⟨Spec.preimage s', Spec.map_preimage s'⟩
  have hpt : (Spec.map φ).base (IsLocalRing.closedPoint k) = 𝔭 := by
    apply j.isOpenEmbedding.injective
    simpa using hs
  have hker : RingHom.ker φ.hom = 𝔭.asIdeal := by
    have h1 := congrArg PrimeSpectrum.asIdeal hpt
    have hmax : (IsLocalRing.closedPoint k).asIdeal = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    have h2 : ((Spec.map φ).base (IsLocalRing.closedPoint k)).asIdeal =
        Ideal.comap φ.hom (IsLocalRing.closedPoint k).asIdeal := rfl
    rw [h2, hmax] at h1
    exact h1

  have hφ𝔭 : ∀ a ∈ 𝔭.asIdeal, φ.hom a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker]; exact ha
  set φbar : A ⧸ 𝔭.asIdeal →+* k := Ideal.Quotient.lift 𝔭.asIdeal φ.hom hφ𝔭 with hφbar
  have hinj : Function.Injective φbar := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hφbar, Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker ▸ (RingHom.mem_ker.mpr ha))
  set ψ : K₀ →+* k := IsFractionRing.lift (A := A ⧸ 𝔭.asIdeal) (K := K₀) (g := φbar) hinj with hψ
  letI : Algebra K₀ k := ψ.toAlgebra
  have hφfac : φ = CommRingCat.ofHom ((algebraMap K₀ k).comp (algebraMap A K₀)) := by
    ext a
    show φ.hom a = ψ ((algebraMap A K₀) a)
    rw [hψ, IsScalarTower.algebraMap_apply A (A ⧸ 𝔭.asIdeal) K₀, IsFractionRing.lift_algebraMap,
      hφbar, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk]
  have h : Spec.map φ ≫ j = Scheme.TwoAffineOpenCover.specMap K₀ k ≫ s₁ := by
    rw [hs₁def, ← Category.assoc, hφfac, CommRingCat.ofHom_comp, Spec.map_comp]

  obtain ⟨𝒲', -, hiff⟩ := exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff c t M hM s₁ 𝒲₁ k
  have h' := hiff.mpr h₁
  clear hs hpt
  revert 𝒲
  rw [h]
  intro 𝒲
  exact hall _ 𝒲 𝒲' h'
end S_AlgebraicGeometry_RelPicard_subsingleton_H1_fibre_of_subsingleton_H1_residueField_chart
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
