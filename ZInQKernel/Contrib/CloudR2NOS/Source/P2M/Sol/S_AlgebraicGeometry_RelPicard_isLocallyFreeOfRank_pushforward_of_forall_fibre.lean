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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre.lean
  Source sha256  : b94dc7263288fc04471348c2866a51623116ce8e08d078dc8c2874a9062903c4
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_of_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_isPullback_snd_specMap_algebraOfHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finiteType_algebraOfHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
r2nos_namespace_dual
r2nos_erase_attr "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField"
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (F : (pullback c t).Modules) (hF : Scheme.Modules.IsInvertible F) (n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward (pullback.snd c t)).obj F) := by

  refine Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback (pullback.snd c t) F n ?_
  intro y
  obtain ⟨W, hW, hyW, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
    (show y ∈ (⊤ : T.Opens) from trivial)
  letI := Scheme.TwoAffineOpenCover.algebraOfHom t W
  haveI : Algebra.FiniteType R Γ(T, W) := Scheme.TwoAffineOpenCover.finiteType_algebraOfHom t W hW
  obtain ⟨g', hcart, -⟩ := Scheme.TwoAffineOpenCover.exists_isPullback_snd_specMap_algebraOfHom c t W hW
  refine ⟨W, hyW, Spec (CommRingCat.of Γ(T, W)),
    pullback c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), hW.isoSpec.symm,
    pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))), g', hcart, ?_⟩

  refine isLocallyFreeOfRank_pushforward_of_forall_fibre_of_finiteType R c ε h𝔉 Γ(T, W)
    ((Scheme.Modules.pullback g').obj F) (hF.pullback g') n ?_

  intro k _ s 𝒲
  obtain ⟨φ, hφ, -, hmod⟩ := Scheme.Modules.exists_iso_pullback_of_isPullback (pullback.snd c t)
    (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W))))) g' hW.fromSpec hcart s
  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ hW.fromSpec))
    (fibreAt c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s) φ hφ 𝒲
    (fibreModule c (Spec.map (CommRingCat.ofHom (algebraMap R Γ(T, W)))) s ((Scheme.Modules.pullback g').obj F))
    (fibreModule c t (s ≫ hW.fromSpec) F) (hmod F).some
  obtain ⟨h1, h0⟩ := hfib k (s ≫ hW.fromSpec) 𝒱
  exact ⟨e1.symm.toEquiv.subsingleton, e0.finrank_eq ▸ h0⟩
end S_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
