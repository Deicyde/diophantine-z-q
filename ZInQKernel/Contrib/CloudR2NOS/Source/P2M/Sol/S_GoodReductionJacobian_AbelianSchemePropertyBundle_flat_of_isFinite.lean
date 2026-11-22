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
  Source file    : P2M/Sol/S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite.lean
  Source sha256  : 4f30c85c06bd4e0fd55318bb7deb93301a590e11182cc0b356997d2991c76dee
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_isFinite_endomorphism
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
r2nos_namespace_dual
r2nos_erase_attr "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace P2mIsogFlat
r2nos_namespace_dual

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2mIsogFlat.isLocallyNoetherian (hA : AbelianSchemePropertyBundle K f) : IsLocallyNoetherian A := by
  haveI : Smooth f := hA.smooth
  exact LocallyOfFiniteType.isLocallyNoetherian f

w03_export "P2mIsogFlat" "isLocallyNoetherian"

theorem flat_stalkMap (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f)
    [IsFinite β.1] (x : A) : (β.1.stalkMap x).hom.Flat := by
  haveI : Smooth f := hA.smooth
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IsLocallyNoetherian A := isLocallyNoetherian hA

  haveI hx : IsRegularLocalRing (A.presheaf.stalk x) := Smooth.isRegularLocalRing_stalk (f := f) x
  haveI hy : IsRegularLocalRing (A.presheaf.stalk (β.1.base x)) :=
    Smooth.isRegularLocalRing_stalk (f := f) (β.1.base x)

  letI alg : Algebra (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    (β.1.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (β.1.stalkMap x).hom)

  have hfib : ringKrullDim ((A.presheaf.stalk x) ⧸
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (β.1.base x))).map
        (algebraMap (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.IsFinite.ringKrullDim_stalk_quotient_eq_zero β.1 x

  have hdim : ringKrullDim (A.presheaf.stalk x) =
      ringKrullDim (A.presheaf.stalk (β.1.base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFinite_endomorphism (f := f) β.1 β.2 x

  have hflat : Module.Flat (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) :=
    Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
      (A.presheaf.stalk (β.1.base x)) (A.presheaf.stalk x) hfib hdim
  exact hflat

theorem main (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  Flat.of_stalkMap β.1 (flat_stalkMap hA β)

end P2mIsogFlat

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (hA : AbelianSchemePropertyBundle K f) (β : SchemeHomOver f f) [IsFinite β.1] :
    Flat β.1 :=
  P2mIsogFlat.main hA β

end
end S_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
