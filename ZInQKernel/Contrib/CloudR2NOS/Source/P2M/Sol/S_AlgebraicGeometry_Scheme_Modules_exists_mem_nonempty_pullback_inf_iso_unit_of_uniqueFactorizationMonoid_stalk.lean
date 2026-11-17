/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk.lean
  Source sha256  : 9a275997134e9197a29904f05a753bcc100738ce9de33cf1cf266b6ed76e448f
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 4 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
r2nos_namespace_dual
r2nos_erase_attr "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra"
r2nos_erase_attr "instance" "TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
r2nos_erase_attr "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec"

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace"

noncomputable section

theorem solution
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (W : X.Opens) {𝓛 : X.Modules}
    (hW : ∀ x ∈ W, ∃ U : X.Opens, x ∈ U ∧ U ≤ W ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj 𝓛 ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf))
    (z : X) (hz : UniqueFactorizationMonoid (X.presheaf.stalk z)) :
    ∃ V : X.Opens, z ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (W ⊓ V).ι).obj 𝓛 ≅ SheafOfModules.unit (↑(W ⊓ V) : Scheme.{u}).ringCatSheaf) := by
  classical
  obtain ⟨U₀, hU₀, hz0, -⟩ := exists_isAffineOpen_mem_and_subset (x := z) (U := ⊤) (Opens.mem_top z)
  haveI : IsNoetherianRing Γ(X, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  haveI : Nonempty U₀ := ⟨⟨z, hz0⟩⟩

  let S : Type u := Γ(X, U₀)
  let 𝔭 : Ideal S := (hU₀.primeIdealOf ⟨z, hz0⟩).asIdeal
  haveI h𝔭 : 𝔭.IsPrime := (hU₀.primeIdealOf ⟨z, hz0⟩).isPrime

  let A : Scheme.{u} := (W ⊓ U₀ : X.Opens)
  let f : A ⟶ Spec (CommRingCat.of S) := X.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀) ≫ hU₀.isoSpec.hom
  haveI : IsOpenImmersion f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of S)) := inferInstance
  haveI : QuasiCompact f := inferInstance
  haveI : QuasiSeparated f := inferInstance

  let ι1 : Spec (CommRingCat.of (Localization.Away (1 : S))) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (1 : S))))
  let ι𝔭 : Spec (CommRingCat.of (Localization.AtPrime 𝔭)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))
  let ψ : Localization.Away (1 : S) →+* Localization.AtPrime 𝔭 :=
    IsLocalization.Away.lift (1 : S) (g := algebraMap S (Localization.AtPrime 𝔭)) (by simp)
  have hψ : ψ.comp (algebraMap S (Localization.Away (1 : S))) = algebraMap S (Localization.AtPrime 𝔭) :=
    IsLocalization.Away.lift_comp (1 : S) _

  let 𝓛A : A.Modules := (Scheme.Modules.pullback (W ⊓ U₀).ι).obj 𝓛
  have hAinv : Scheme.Modules.IsInvertible 𝓛A := by
    constructor
    intro y
    obtain ⟨U, hyU, hUW, ⟨eU⟩⟩ := hW y.1 y.2.1
    let V : A.Opens := (W ⊓ U₀).ι ⁻¹ᵁ U
    have hyV : y ∈ V := hyU
    refine ⟨V, hyV, ⟨?_⟩⟩
    let j : (V : Scheme.{u}) ⟶ (U : Scheme.{u}) := (W ⊓ U₀).ι.resLE U V le_rfl
    have hj : j ≫ U.ι = V.ι ≫ (W ⊓ U₀).ι := Scheme.Hom.resLE_comp_ι _ _
    exact (Scheme.Modules.pullbackComp V.ι (W ⊓ U₀).ι).app 𝓛 ≪≫ (Scheme.Modules.pullbackCongr hj.symm).app 𝓛 ≪≫
      ((Scheme.Modules.pullbackComp j U.ι).app 𝓛).symm ≪≫ (Scheme.Modules.pullback j).mapIso eU ≪≫
      Scheme.Modules.pullbackUnitIso j
  let 𝓛₁ : (pullback f ι1).Modules := (Scheme.Modules.pullback (pullback.fst f ι1)).obj 𝓛A
  have h₁ : Scheme.Modules.IsInvertible 𝓛₁ := hAinv.pullback _
  let 𝓛₂ : (pullback f ι1).Modules := SheafOfModules.unit (pullback f ι1).ringCatSheaf
  have h₂ : Scheme.Modules.IsInvertible 𝓛₂ := Scheme.Modules.isInvertible_unit _

  let φ𝔭 : pullback f ι𝔭 ⟶ pullback f ι1 :=
    pullback.lift (pullback.fst f ι𝔭) (pullback.snd f ι𝔭 ≫ Spec.map (CommRingCat.ofHom ψ))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ])

  haveI : IsDomain S := show IsDomain Γ(X, U₀) from inferInstance
  letI : Algebra S (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk (⟨z, hz0⟩ : U₀)
  let eSt : X.presheaf.stalk z ≃ₐ[S] Localization.AtPrime 𝔭 :=
    @IsLocalization.algEquiv S _ 𝔭.primeCompl (X.presheaf.stalk z) _ _ (hU₀.isLocalization_stalk ⟨z, hz0⟩)
      (Localization.AtPrime 𝔭) _ _ _
  haveI : UniqueFactorizationMonoid (Localization.AtPrime 𝔭) := MulEquiv.uniqueFactorizationMonoid eSt.toMulEquiv hz

  obtain ⟨e𝔭⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_unit_of_isOpenImmersion_of_uniqueFactorizationMonoid
    (pullback.snd f ι𝔭) (h₁.pullback φ𝔭)

  have h1𝔭 : (1 : S) ∉ 𝔭 := (Ideal.ne_top_iff_one 𝔭).mp h𝔭.ne_top
  obtain ⟨r, hr, ψr, hψr, ⟨er⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
      f 𝔭 (1 : S) h1𝔭 ψ hψ 𝓛₁ 𝓛₂ h₁ h₂ ⟨e𝔭 ≪≫ (Scheme.Modules.pullbackUnitIso φ𝔭).symm⟩

  let ιr : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))
  let φr : pullback f ιr ⟶ pullback f ι1 :=
    pullback.lift (pullback.fst f ιr) (pullback.snd f ιr ≫ Spec.map (CommRingCat.ofHom ψr))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr])
  have memD : ∀ (x : X) (hx : x ∈ U₀), hU₀.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen r ↔ x ∈ X.basicOpen r := by
    intro x hx
    have h1 : hU₀.primeIdealOf ⟨x, hx⟩ ∈ hU₀.fromSpec ⁻¹ᵁ X.basicOpen r ↔ x ∈ X.basicOpen r := by
      show hU₀.fromSpec (hU₀.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
      rw [hU₀.fromSpec_primeIdealOf]
    rw [hU₀.fromSpec_preimage_basicOpen] at h1
    exact h1
  refine ⟨X.basicOpen r, (memD z hz0).mp hr, ⟨?_⟩⟩

  let h : pullback f ιr ⟶ X := pullback.fst f ιr ≫ (W ⊓ U₀).ι
  have hfapp : ∀ a : A, f a = hU₀.primeIdealOf ⟨a.1, a.2.2⟩ := fun a => by
    have ha : (X.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀)) a = ⟨a.1, a.2.2⟩ := Subtype.ext (Scheme.homOfLE_apply _ a)
    show (X.homOfLE _ ≫ hU₀.isoSpec.hom) a = hU₀.isoSpec.hom ⟨a.1, a.2.2⟩
    rw [Scheme.Hom.comp_apply, ha]
  have hrange : Set.range (W ⊓ X.basicOpen r).ι.base = Set.range h.base := by
    rw [Scheme.Opens.range_ι]
    have hιr : Set.range ιr.base = (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum S)) := by
      change Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away r))) = _
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    ext x
    constructor
    · rintro ⟨hxW, hxr⟩
      let a : A := ⟨x, hxW, X.basicOpen_le r hxr⟩
      have hfa : f a ∈ Set.range ιr.base := by
        rw [hιr, hfapp]; exact (memD x _).mpr hxr
      obtain ⟨t, ht⟩ := hfa
      obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback a t ht.symm
      refine ⟨p, ?_⟩
      show ((W ⊓ U₀).ι) ((pullback.fst f ιr) p) = x
      rw [hp1]; rfl
    · rintro ⟨p, rfl⟩
      show ((W ⊓ U₀).ι ((pullback.fst f ιr) p)) ∈ (W ⊓ X.basicOpen r : Set X)
      refine ⟨((pullback.fst f ιr) p).2.1, ?_⟩
      have hc : f ((pullback.fst f ιr) p) = ιr ((pullback.snd f ιr) p) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      have hmemr : f ((pullback.fst f ιr) p) ∈ Set.range ιr.base := ⟨_, hc.symm⟩
      rw [hιr] at hmemr
      have : f ((pullback.fst f ιr) p) ∈ PrimeSpectrum.basicOpen r := hmemr
      rw [hfapp] at this
      exact (memD _ _).mp this
  haveI : IsOpenImmersion h := inferInstance
  let e := IsOpenImmersion.isoOfRangeEq (W ⊓ X.basicOpen r).ι h hrange
  have he : e.hom ≫ h = (W ⊓ X.basicOpen r).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hφr : φr ≫ pullback.fst f ι1 = pullback.fst f ιr := pullback.lift_fst _ _ _

  have T1 : (Scheme.Modules.pullback (pullback.fst f ιr)).obj 𝓛A ≅ SheafOfModules.unit (pullback f ιr).ringCatSheaf :=
    (Scheme.Modules.pullbackCongr hφr.symm).app 𝓛A ≪≫ ((Scheme.Modules.pullbackComp φr (pullback.fst f ι1)).app 𝓛A).symm ≪≫
      er ≪≫ Scheme.Modules.pullbackUnitIso φr
  have T2 : (Scheme.Modules.pullback h).obj 𝓛 ≅ SheafOfModules.unit (pullback f ιr).ringCatSheaf :=
    ((Scheme.Modules.pullbackComp (pullback.fst f ιr) (W ⊓ U₀).ι).app 𝓛).symm ≪≫ T1
  exact (Scheme.Modules.pullbackCongr he.symm).app 𝓛 ≪≫ ((Scheme.Modules.pullbackComp e.hom h).app 𝓛).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso T2 ≪≫ Scheme.Modules.pullbackUnitIso e.hom

end
end S_AlgebraicGeometry_Scheme_Modules_exists_mem_nonempty_pullback_inf_iso_unit_of_uniqueFactorizationMonoid_stalk
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
