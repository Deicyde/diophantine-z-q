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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre.lean
  Source sha256  : 52211b2538776fd8c9913866af4d58edff2d563e289a30c4da5ca829cd18f5e4
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 18 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_finite_H0_H1_sectionsOf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre
r2nos_namespace_dual
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

namespace PFBCSketch
r2nos_namespace_dual

variable {R : Type u} [CommRing R]

theorem isPullback_baseChangeSnd {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) :
    IsPullback (baseChangeSnd c ψ) (pullback.snd c t') (pullback.snd c t) ψ.1 := by
  refine IsPullback.of_right (h₁₂ := pullback.fst c t) (v₁₃ := c) (h₂₂ := t) ?_
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) (IsPullback.of_hasPullback c t)
  rw [RelPicard.BaseChange.baseChangeSnd_fst' (cc := c) (ψ := ψ), ψ.2]
  exact IsPullback.of_hasPullback c t'

theorem fromSpec_comp_eq_specMap {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (W : T.Opens)
    (hW : IsAffineOpen W) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
    hW.fromSpec ≫ t = Scheme.TwoAffineOpenCover.specMap R Γ(T, W) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW (le_top (a := W))
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
  change _ = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top).hom)
  rw [CommRingCat.ofHom_hom]
  exact h.symm

end PFBCSketch

open PFBCSketch in
r2nos_open_dual "PFBCSketch" in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)} [LocallyOfFiniteType t]
    (ψ : SchemeHomOver t' t) (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    IsIso (Scheme.Modules.baseChangeHom
      (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := ψ)) F) := by
  have hcart := isPullback_baseChangeSnd c ψ
  refine Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback hcart F ?_
  intro y

  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show ψ.1.base y ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨W', hW', hyW', hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens
    (show y ∈ ψ.1 ⁻¹ᵁ W from hyW)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t' W'
  letI algW : Algebra Γ(T, W) Γ(T', W') := (ψ.1.appLE W W' hle).hom.toAlgebra
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  haveI : IsNoetherianRing Γ(T, W) := Algebra.FiniteType.isNoetherianRing R Γ(T, W)

  obtain ⟨u, hu, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW

  have hφ' : hW'.fromSpec ≫ ψ.1 = Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ hW.fromSpec := by
    change _ = Spec.map (CommRingCat.ofHom (ψ.1.appLE W W' hle).hom) ≫ hW.fromSpec
    rw [CommRingCat.ofHom_hom]
    exact (IsAffineOpen.SpecMap_appLE_fromSpec ψ.1 hW hW' hle).symm
  have hφ : (hW'.isoSpec.symm.hom ≫ Scheme.Opens.ι W') ≫ ψ.1 =
      Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ hW.isoSpec.symm.hom ≫ Scheme.Opens.ι W := by
    rw [Iso.symm_hom, Iso.symm_hom, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_inv_ι]
    exact hφ'
  have hφR : Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W') ≫ Scheme.TwoAffineOpenCover.specMap R Γ(T, W) =
      Scheme.TwoAffineOpenCover.specMap R Γ(T', W') := by
    rw [← fromSpec_comp_eq_specMap t W hW, ← fromSpec_comp_eq_specMap t' W' hW', ← Category.assoc, ← hφ',
      Category.assoc, ψ.2]
  let ψW : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R Γ(T', W'))
      (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) :=
    ⟨Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W'), hφR⟩
  have hv : IsPullback (baseChangeSnd c ψW) (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W')))
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)))
      (Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W')) :=
    isPullback_baseChangeSnd c ψW
  refine ⟨W, W', hyW', Spec (CommRingCat.of Γ(T, W)), Spec (CommRingCat.of Γ(T', W')),
    pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)),
    pullback c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W')), hW.isoSpec.symm, hW'.isoSpec.symm,
    Scheme.TwoAffineOpenCover.specMap Γ(T, W) Γ(T', W'), hφ,
    pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)), u, hu,
    pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W')), baseChangeSnd c ψW, hv, ?_⟩

  haveI : Smooth c := SmoothOfRelativeDimension.smooth 1 c
  haveI : Flat (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) := inferInstance
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉A, -, -, -, -⟩ := 𝔉.exists_baseChange Γ(T, W)
  have hFu : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback u).obj F) := hF.pullback u
  have hfin := 𝔉A.finite_H0_H1_sectionsOf ((Scheme.Modules.pullback u).obj F) hFu.exists_trivialization
  refine Scheme.Modules.isIso_baseChangeHom_of_twoAffineOpenCover
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) 𝔉A.twoAffineOpenCover
    ((Scheme.Modules.pullback u).obj F) hFu.exists_trivialization hfin ?_ Γ(T', W')
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T', W'))) (baseChangeSnd c ψW) hv

  intro K _ _
  obtain ⟨θ, hθ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
    (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) u hW.fromSpec hu
    (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
  obtain ⟨𝒱, -, -, -, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec))
    (fibreAt c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)) θ hθ
    (𝔉A.twoAffineOpenCover.pullback (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W))) K)
    (fibreModule c (Scheme.TwoAffineOpenCover.specMap R Γ(T, W)) (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K)
      ((Scheme.Modules.pullback u).obj F))
    (fibreModule c t (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) F) (hmod F).some
  obtain ⟨h1, -⟩ := hfib K (Scheme.TwoAffineOpenCover.specMap Γ(T, W) K ≫ hW.fromSpec) 𝒱
  exact e1.symm.toEquiv.subsingleton
end S_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
