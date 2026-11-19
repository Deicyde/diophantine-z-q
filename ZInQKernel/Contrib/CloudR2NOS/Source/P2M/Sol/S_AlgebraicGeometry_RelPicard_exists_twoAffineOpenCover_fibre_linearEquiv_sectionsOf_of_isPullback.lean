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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.lean
  Source sha256  : 66d0f35540b0dac4aa017a64b4edfbb38073dcbd988046a0f8173182acd41505
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 11 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback.AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules Scheme.Modules.pullbackComp Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "fibreAt fibreModule"
namespace TransportGen
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
  (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
  {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
  {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
  (hcart : IsPullback g' y (pullback.snd c t) s)

def φ : pullback (pullback.snd c t) s ≅ Y := hcart.isoPullback.symm

theorem φ_hom_y : (φ c t s y g' hcart).hom ≫ y = fibreAt c t s := by
  rw [φ, Iso.symm_hom, IsPullback.isoPullback_inv_snd]
  rfl

def modIso : fibreModule c t s M ≅ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).obj ((Scheme.Modules.pullback g').obj M) :=
  (Scheme.Modules.pullbackCongr (hcart.isoPullback_inv_fst).symm).app M ≪≫
    (Scheme.Modules.pullbackComp (φ c t s y g' hcart).hom g').symm.app M

include hcart in
theorem main (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) := by
  obtain ⟨𝒲, -, -, ⟨eH0⟩, ⟨eH1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t s) y (φ c t s y g' hcart) (φ_hom_y c t s y g' hcart)
    𝒱 F (fibreModule c t s M)
    (modIso c t M s y g' hcart ≪≫ (Scheme.Modules.pullback (φ c t s y g' hcart).hom).mapIso e.symm)
  exact ⟨𝒲, ⟨eH0.symm⟩, ⟨eH1.symm⟩⟩

end AlgebraicGeometry.RelPicard.TransportGen

end

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k)) (g' : Y ⟶ pullback c t)
    (hcart : IsPullback g' y (pullback.snd c t) s)
    (F : Y.Modules) (e : F ≅ (Scheme.Modules.pullback g').obj M) (𝒱 : Y.TwoAffineOpenCover) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Nonempty ((𝒱.sectionsOf y F).H0 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0) ∧
      Nonempty ((𝒱.sectionsOf y F).H1 ≃ₗ[k] (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1) :=
  AlgebraicGeometry.RelPicard.TransportGen.main c t M s y g' hcart F e 𝒱
end S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
