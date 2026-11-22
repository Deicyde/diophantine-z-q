/-
NOS-CORE PROBE STAGING COPY (nos-core-probe-001, lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre.lean
  Source sha256  : d3e77ec2da91c271fb233a39be541984f045c32fff3a559559faf57361f536d2
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 3 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 27 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

/-
Default-limit reproof, 2026-11-17.
The coordinate of a section under a chosen module trivialization, its
injectivity, the resulting unit ratio, and transport through a module
isomorphism are proved separately. The divisor comparison applies these
lemmas to the same restricted projection and its actual trivialization.
Every existing declaration, statement, import and nonnumeric option is
retained; no coordinate, freeness, rank or equality hypothesis is added.
-/

/-
Local continuation, 2026-11-17.
Coordinate injectivity uses the universally quantified left-inverse identity
of the same trivialization, including identity evaluation, rather than an
asymmetric rewrite of a two-sided point equality. Only that helper's proof
is changed; every declaration, statement, import and option is retained.
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_eq_of_forall_comap_openCover_eq
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_snd_apply_eq_and_notMem_support
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPushforwardRestrict
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring"
r2nos_erase_attr "simp" "AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

namespace K5aUnitWs13
r2nos_namespace_dual

open Opposite TopologicalSpace
r2nos_open_dual "Opposite TopologicalSpace"

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_unit (φ : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(𝟙_ X.Modules, V)) :
    M.presheaf.map i.op (φ.app V m) = φ.app U ((𝟙_ X.Modules).presheaf.map i.op m) := by
  have h := (Scheme.Modules.Hom.mapPresheaf φ).naturality i.op
  have h2 := ConcreteCategory.congr_hom h m
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h2
  exact h2.symm

theorem map_toUnitSection_one {U V : X.Opens} (i : U ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection V 1) =
      Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem app_one_eq_map (φ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    φ.app U (Scheme.Modules.toUnitSection U 1) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [map_app_unit, map_toUnitSection_one]

noncomputable def homOfGlobal (M : X.Modules) (m : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  (SheafOfModules.unitHomEquiv M).symm
    (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m)
      (by
        intro U V f
        change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
        rw [← Functor.map_comp]
        rfl))

theorem homOfGlobal_app_top (M : X.Modules) (m : Γ(M, ⊤)) :
    (homOfGlobal M m).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = m := by
  have hS : ∀ ⦃U V : (X.Opens)ᵒᵖ⦄ (f : U ⟶ V),
      M.presheaf.map f (M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) =
        M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op m := by
    intro U V f
    change (M.presheaf.map (homOfLE _).op ≫ M.presheaf.map f) m = _
    rw [← Functor.map_comp]
    rfl
  have h := congrArg (fun s : M.val.sections => s.val (op ⊤))
    ((SheafOfModules.unitHomEquiv M).apply_symm_apply
      (PresheafOfModules.sectionsMk (fun U => M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m) hS))
  simp only [PresheafOfModules.sectionsMk_coe] at h
  have hm : M.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m := by
    rw [show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]; rfl
  rw [hm] at h
  have h2 : ∀ σ : 𝟙_ X.Modules ⟶ M,
      ((SheafOfModules.unitHomEquiv M) σ).val (op ⊤) = σ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
    intro σ
    simp only [SheafOfModules.unitHomEquiv, Equiv.trans_apply]
    erw [PresheafOfModules.unitHomEquiv_apply_coe]
    rfl
  rw [← h2]
  exact h

theorem coeff_eq_mul_coeff (s s' : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤))
    (h : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s'.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
    (U : X.Opens) (τ : M.restrict U.ι ≅ 𝟙_ ((U : Scheme.{u})).Modules) :
    Scheme.Modules.coeff s U τ.hom =
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op u * Scheme.Modules.coeff s' U τ.hom := by
  set W : X.Opens := U.ι ''ᵁ ⊤ with hW
  have hres : s.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u • s'.app W (Scheme.Modules.toUnitSection W 1) := by
    rw [app_one_eq_map s W, app_one_eq_map s' W, h, Scheme.Modules.map_smul]
  set r : Γ((U : Scheme.{u}), ⊤) := X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u with hr
  have hres' : Scheme.Modules.restrictSection s U = r • Scheme.Modules.restrictSection s' U := by
    change s.app W (Scheme.Modules.toUnitSection W 1) =
      (U.ι.appIso ⊤).inv r • s'.app W (Scheme.Modules.toUnitSection W 1)
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    exact hres
  have key : Scheme.Modules.coeff s U τ.hom = U.topIso.hom r * Scheme.Modules.coeff s' U τ.hom := by
    show U.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ (Scheme.Modules.restrictSection s U))) = _
    rw [hres', Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul, map_mul]
    rfl
  rw [key, hr, Scheme.Opens.topIso_hom]
  congr 1
  change (X.presheaf.map _ ≫ X.presheaf.map _) u = _
  rw [← Functor.map_comp]
  rfl

theorem isUnit_coord_of_forall_fibre {T : Scheme.{u}} (q : X ⟶ T) (hM : Scheme.Modules.IsInvertible M)
    (τ : (Scheme.Modules.pushforward q).obj M ≅ 𝟙_ T.Modules) (s : 𝟙_ X.Modules ⟶ M)
    (hs : ∀ x : T, ∃ y : X, q.base y = x ∧ y ∉ (Scheme.Modules.zeroSchemeIdeal s).support) :
    IsUnit (Scheme.Modules.ofUnitSection ⊤
      (τ.hom.app ⊤ (show Γ((Scheme.Modules.pushforward q).obj M, ⊤) from
        s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)))) := by
  classical
  set m : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with hm
  set a : Γ(T, ⊤) := Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ m) with ha
  set e : Γ((Scheme.Modules.pushforward q).obj M, ⊤) := τ.inv.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) with he

  have h1 : τ.hom.app ⊤ m = a • Scheme.Modules.toUnitSection ⊤ 1 := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
  have h2 : m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      Scheme.Modules.Hom.id_app]
    rfl
  have hme : m = a • e := by
    calc m = τ.inv.app ⊤ (τ.hom.app ⊤ m) := h2
      _ = τ.inv.app ⊤ (a • Scheme.Modules.toUnitSection ⊤ 1) := by rw [h1]
      _ = a • e := by rw [Scheme.Modules.Hom.app_smul]

  have hme' : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = q.appTop a • (show Γ(M, ⊤) from e) := hme

  apply RingedSpace.isUnit_of_isUnit_germ
  intro x _
  obtain ⟨y, hyx, hy⟩ := hs x
  obtain ⟨U, hyU, -, ⟨τU⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := y) trivial

  have hZU := ((Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s).2 U τU).1
  have hyb : y ∈ X.basicOpen (Scheme.Modules.coeff s U.1 τU.hom) := by
    by_contra hyb
    apply hy
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hyU, hZU, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    rw [hf]; exact hyb
  have hunit := (X.mem_basicOpen _ y hyU).mp hyb

  have hcmp := coeff_eq_mul_coeff s (homOfGlobal M (show Γ(M, ⊤) from e)) (q.appTop a)
    (by rw [homOfGlobal_app_top]; exact hme') U.1 τU
  rw [hcmp, map_mul] at hunit
  have hu1 := isUnit_of_mul_isUnit_left hunit

  rw [TopCat.Presheaf.germ_res_apply] at hu1
  have hq : X.presheaf.germ ⊤ y trivial (q.appTop a) =
      q.stalkMap y (T.presheaf.germ ⊤ (q.base y) trivial a) :=
    (Scheme.Hom.germ_stalkMap_apply q ⊤ y trivial a).symm
  rw [hq] at hu1
  rw [← hyx]
  exact (isUnit_map_iff (q.stalkMap y).hom _).mp hu1

/-- An injective linear coordinate whose two values are units makes the
second vector a unit multiple of the first, over any commutative ring. -/
theorem exists_unit_smul_of_coordinates {A P : Type u} [CommRing A]
    [AddCommGroup P] [Module A P] (f : P →ₗ[A] A)
    (hf : Function.Injective f) (x₁ x₂ : P)
    (h₁ : IsUnit (f x₁)) (h₂ : IsUnit (f x₂)) :
    ∃ a : A, IsUnit a ∧ x₂ = a • x₁ := by
  let a : A := f x₂ * ↑(h₁.unit⁻¹)
  refine ⟨a, h₂.mul (Units.isUnit _), hf ?_⟩
  rw [f.map_smul, smul_eq_mul]
  change f x₂ = (f x₂ * ↑(h₁.unit⁻¹)) * f x₁
  rw [mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- The actual coordinate of a section in a chosen trivialization of its
module sheaf. Its linear structure is proved directly from that morphism. -/
noncomputable def sectionCoordinate {T : Scheme.{u}} {P : T.Modules}
    (τ : P ≅ 𝟙_ T.Modules) (U : T.Opens) : Γ(P, U) →ₗ[Γ(T, U)] Γ(T, U) where
  toFun m := Scheme.Modules.ofUnitSection U (τ.hom.app U m)
  map_add' x y := congrArg (Scheme.Modules.ofUnitSection U)
    ((τ.hom.app U).hom.map_add' x y)
  map_smul' a x := by
    change Scheme.Modules.ofUnitSection U (τ.hom.app U (a • x)) =
      a * Scheme.Modules.ofUnitSection U (τ.hom.app U x)
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul]

/-- The coordinate is injective because the chosen trivialization has its
actual inverse, not because a coordinate-faithfulness hypothesis is supplied. -/
theorem sectionCoordinate_injective {T : Scheme.{u}} {P : T.Modules}
    (τ : P ≅ 𝟙_ T.Modules) (U : T.Opens) :
    Function.Injective (sectionCoordinate τ U) := by
  intro x y hxy
  have h : (τ.hom.app U).hom x = (τ.hom.app U).hom y :=
    Scheme.Modules.ofUnitSection_injective U hxy
  have hleft : Function.LeftInverse (τ.inv.app U).hom (τ.hom.app U).hom := fun z => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, τ.hom_inv_id,
      Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply]
  exact hleft.injective h

/-- For the original projection, two sections which each avoid their zero
scheme somewhere in every fibre are unit multiples when the actual
pushforward has a chosen rank-one trivialization. -/
theorem exists_unit_smul_of_pushforward_trivialization {T : Scheme.{u}}
    (q : X ⟶ T) (hM : Scheme.Modules.IsInvertible M)
    (τ : (Scheme.Modules.pushforward q).obj M ≅ 𝟙_ T.Modules)
    (s₁ s₂ : 𝟙_ X.Modules ⟶ M)
    (hs₁ : ∀ x : T, ∃ y : X, q.base y = x ∧
      y ∉ (Scheme.Modules.zeroSchemeIdeal s₁).support)
    (hs₂ : ∀ x : T, ∃ y : X, q.base y = x ∧
      y ∉ (Scheme.Modules.zeroSchemeIdeal s₂).support) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧
      s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
        u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
  let m₁ : Γ((Scheme.Modules.pushforward q).obj M, ⊤) :=
    s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
  let m₂ : Γ((Scheme.Modules.pushforward q).obj M, ⊤) :=
    s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)
  have h₁ : IsUnit (sectionCoordinate τ ⊤ m₁) :=
    isUnit_coord_of_forall_fibre q hM τ s₁ hs₁
  have h₂ : IsUnit (sectionCoordinate τ ⊤ m₂) :=
    isUnit_coord_of_forall_fibre q hM τ s₂ hs₂
  obtain ⟨a, ha, hm⟩ := exists_unit_smul_of_coordinates (sectionCoordinate τ ⊤)
    (sectionCoordinate_injective τ ⊤) m₁ m₂ h₁ h₂
  refine ⟨q.appTop a, ha.map q.appTop.hom, ?_⟩
  exact hm

/-- Transport the unit-multiple identity back through the same module
isomorphism, retaining the original two sections and scalar. -/
theorem unit_smul_before_iso {Y : Scheme.{u}} {P Q : Y.Modules}
    (θ : P ≅ Q) (s₁ s₂ : 𝟙_ Y.Modules ⟶ P) (u : Γ(Y, ⊤))
    (h : (s₂ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      u • (s₁ ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) := by
  have ht : ∀ s : 𝟙_ Y.Modules ⟶ P,
      s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
        θ.inv.app ⊤ ((s ≫ θ.hom).app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
    intro s
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
      Category.assoc, θ.hom_inv_id, Category.comp_id]
  rw [ht s₂, ht s₁, h, Scheme.Modules.Hom.app_smul]

end K5aUnitWs13

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {d₁ d₂ : ℕ} (D₁ : RelEffCartierDiv c d₁ t) (D₂ : RelEffCartierDiv c d₂ t)
    (N₁ N₂ : T.Modules) (hN₁ : Scheme.Modules.IsInvertible N₁) (hN₂ : Scheme.Modules.IsInvertible N₂)
    (e₁ : D₁.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₁)
    (e₂ : D₂.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N₂) :
    D₁.I = D₂.I := by
  classical
  haveI : IsSeparated c := inferInstance
  set q := pullback.snd c t with hq

  set s₁ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₁ := D₁.I.invModuleSection ≫ e₁.hom with hs₁
  set s₂ : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N₂ := D₂.I.invModuleSection ≫ e₂.hom with hs₂
  have hZ₁ : Scheme.Modules.zeroSchemeIdeal s₁ = D₁.I := by
    rw [hs₁, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (RelEffCartierDiv.isInvertible_I D₁).zeroSchemeIdeal_invModuleSection]
  have hZ₂ : Scheme.Modules.zeroSchemeIdeal s₂ = D₂.I := by
    rw [hs₂, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
      (RelEffCartierDiv.isInvertible_I D₂).zeroSchemeIdeal_invModuleSection]

  have key : ∀ z : ↥(pullback c t), ∃ V : T.Opens, q.base z ∈ V ∧
      (Scheme.Modules.zeroSchemeIdeal s₁).comap (q ⁻¹ᵁ V).ι =
        (Scheme.Modules.zeroSchemeIdeal s₂).comap (q ⁻¹ᵁ V).ι := by
    intro z
    set x : T := q.base z with hxdef

    have hP : Scheme.Modules.IsInvertible ((Scheme.Modules.pushforward q).obj M) :=
      (Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mp
        (isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t M hM 1 hfib)
    obtain ⟨U₁, hxU₁, -, ⟨τ₁⟩⟩ := hN₁.exists_restrict_iso (V := ⊤) (x := x) trivial
    obtain ⟨U₂, hxU₂, h₂₁, ⟨τ₂⟩⟩ := hN₂.exists_restrict_iso (V := U₁.1) (x := x) hxU₁
    obtain ⟨U₃, hxU₃, h₃₂, ⟨τP⟩⟩ := hP.exists_restrict_iso (V := U₂.1) (x := x) hxU₂
    set V : T.Opens := U₃.1 with hVdef

    have trivN : ∀ {N : T.Modules} {U : T.Opens} (hle : V ≤ U) (τ : N.restrict U.ι ≅ 𝟙_ ((U : Scheme.{u})).Modules),
        Nonempty ((Scheme.Modules.pullback V.ι).obj N ≅ 𝟙_ ((V : Scheme.{u})).Modules) := by
      intro N U hle τ
      refine ⟨((Scheme.Modules.pullbackCongr (T.homOfLE_ι hle).symm).app N) ≪≫
        ((Scheme.Modules.pullbackComp (T.homOfLE hle) U.ι).app N).symm ≪≫
        (Scheme.Modules.pullback (T.homOfLE hle)).mapIso
          (((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app N) ≪≫ τ) ≪≫
        (Functor.Monoidal.εIso (Scheme.Modules.pullback (T.homOfLE hle))).symm⟩
    obtain ⟨eN₁⟩ := trivN (h₃₂.trans h₂₁) τ₁
    obtain ⟨eN₂⟩ := trivN h₃₂ τ₂

    set W : (pullback c t).Opens := q ⁻¹ᵁ V with hWdef
    obtain ⟨φ₁⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M N₁ eN₁
    obtain ⟨φ₂⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M N₂ eN₂
    refine ⟨V, hxU₃, ?_⟩
    have hMN₁ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₁) := hM.tensor (hN₁.pullback q)
    have hMN₂ : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N₂) := hM.tensor (hN₂.pullback q)
    rw [hMN₁.comap_zeroSchemeIdeal W.ι s₁, hMN₂.comap_zeroSchemeIdeal W.ι s₂,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₁) φ₁.hom,
      ← Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso (Scheme.Modules.pullbackSection W.ι s₂) φ₂.hom]
    set t₁ := Scheme.Modules.pullbackSection W.ι s₁ ≫ φ₁.hom with ht₁
    set t₂ := Scheme.Modules.pullbackSection W.ι s₂ ≫ φ₂.hom with ht₂

    suffices hu : ∃ u : Γ((W : Scheme.{u}), ⊤), IsUnit u ∧
        t₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • t₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) by
      obtain ⟨u, hu, h⟩ := hu
      exact Scheme.Modules.IsInvertible.zeroSchemeIdeal_eq_of_app_eq_smul (hM.pullback W.ι) t₁ t₂ u hu h

    let τ' : (Scheme.Modules.pushforward (q ∣_ V)).obj (M.restrict W.ι) ≅ 𝟙_ ((V : Scheme.{u})).Modules :=
      ((Scheme.Modules.pushforwardRestrictIso q V).app M) ≪≫ τP
    let θ : (Scheme.Modules.pullback W.ι).obj M ≅ M.restrict W.ι :=
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm
    have hMW : Scheme.Modules.IsInvertible (M.restrict W.ι) := by
      refine ⟨fun w => ?_⟩
      obtain ⟨O, hwO, ⟨τO⟩⟩ := (hM.pullback W.ι).exists_trivialization w
      exact ⟨O, hwO, ⟨(Scheme.Modules.pullback O.ι).mapIso θ.symm ≪≫ τO⟩⟩

    have hsec : ∀ (i : Fin 2), True := fun _ => trivial
    have hs' : ∀ {L : (pullback c t).Modules} (sL : 𝟙_ _ ⟶ L) {dd : ℕ} (DD : RelEffCartierDiv c dd t)
        (hZ : Scheme.Modules.zeroSchemeIdeal sL = DD.I) (hL : Scheme.Modules.IsInvertible L)
        (φ : (Scheme.Modules.pullback W.ι).obj L ≅ (Scheme.Modules.pullback W.ι).obj M),
        ∀ v : ↥V, ∃ w : ↥W, (q ∣_ V).base w = v ∧
          w ∉ (Scheme.Modules.zeroSchemeIdeal ((Scheme.Modules.pullbackSection W.ι sL ≫ φ.hom) ≫ θ.hom)).support := by
      intro L sL dd DD hZ hL φ v
      obtain ⟨y, hy, hyD⟩ := RelEffCartierDiv.exists_snd_apply_eq_and_notMem_support c t DD (v : T)
      have hyW : y ∈ W := by
        show q.base y ∈ V
        rw [show q.base y = (v : T) from hy]; exact v.2
      refine ⟨⟨y, hyW⟩, Subtype.ext (by rw [morphismRestrict_base_coe]; exact hy), ?_⟩
      rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso,
        ← hL.comap_zeroSchemeIdeal W.ι sL, hZ]
      intro hw
      apply hyD
      have := hw
      rw [Scheme.IdealSheafData.support_comap] at this
      exact this
    have hs'₁ := hs' s₁ D₁ hZ₁ hMN₁ φ₁
    have hs'₂ := hs' s₂ D₂ hZ₂ hMN₂ φ₂

    obtain ⟨u, hu, h⟩ := K5aUnitWs13.exists_unit_smul_of_pushforward_trivialization
      (q ∣_ V) hMW τ' (t₁ ≫ θ.hom) (t₂ ≫ θ.hom) hs'₁ hs'₂
    exact ⟨u, hu, K5aUnitWs13.unit_smul_before_iso θ t₁ t₂ u h⟩
  choose V hV hloc using key
  let 𝒰 : (pullback c t).OpenCover :=
    Scheme.Cover.mkOfCovers (↥(pullback c t)) (fun z => ((q ⁻¹ᵁ V z : (pullback c t).Opens) : Scheme.{u}))
      (fun z => (q ⁻¹ᵁ V z).ι)
      (fun y => ⟨y, ⟨y, hV y⟩, rfl⟩)
      (fun z => inferInstance)
  rw [← hZ₁, ← hZ₂]
  exact Scheme.IdealSheafData.eq_of_forall_comap_openCover_eq 𝒰 fun z => hloc z
end S_AlgebraicGeometry_RelPicard_relEffCartierDiv_I_eq_of_lineBundle_iso_tensor_pullback_of_forall_fibre
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
