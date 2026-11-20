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
  Source file    : Theorems/Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField.lean
  Source sha256  : 4ae9816e46d4df2dbba38573b02e434674e7e07b049e8fa3fb9d3605cc5e1bcf
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 7 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra TensorProduct"
theorem AlgebraicGeometry.RelPicard.exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {A : Type u} [CommRing A] (j : Spec (CommRingCat.of A) ⟶ T) [IsOpenImmersion j]
    {CA : Scheme.{u}} (πA : CA ⟶ Spec (CommRingCat.of A)) (g' : CA ⟶ pullback c t)
    (hcart : IsPullback g' πA (pullback.snd c t) j)
    (𝒱 : CA.TwoAffineOpenCover) (𝔭 : PrimeSpectrum A)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (hs : s.base (IsLocalRing.closedPoint k) = j.base 𝔭) :
    ∃ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      ∀ (M : (pullback c t).Modules), Scheme.Modules.IsInvertible M →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 =
          Module.finrank 𝔭.asIdeal.ResidueField
            (LinearMap.ker ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
              𝔭.asIdeal.ResidueField)) ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 =
          Module.finrank 𝔭.asIdeal.ResidueField
            ((𝔭.asIdeal.ResidueField ⊗[A] (𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).M01) ⧸
              LinearMap.range ((𝒱.sectionsOf πA ((Scheme.Modules.pullback g').obj M)).cechDiff.baseChange
                𝔭.asIdeal.ResidueField)) := by w03_exact_reverting @_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_finrank_eq_finrank_cechDiff_baseChange_residueField.solution

end ZInQ.Contrib.CloudW03NeronSurj.FLT
