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
  Source file    : Definitions/Def_AlgebraicCurve_RiemannRochRows.lean
  Source sha256  : 69fd6dcd1bb1fb98dd407d4c2dece7283d0a9741f5744bb345c569774b7b0449
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open KaehlerDifferential
r2nos_open_dual "KaehlerDifferential"

namespace AlgebraicCurve
r2nos_namespace_dual

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def RiemannInequality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F, Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ)

def RiemannIndexFormula : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F,
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))

def WeilDualityAdelic : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (indexOfSpecialty D : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilDuality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))
        = (ell (canonicalDivisorOf hω - D) : ℤ)

def WeilOmegaEllAgrees : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (Module.finrank K ↥(omegaSpace D) : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

def FunctionFieldRiemannRoch : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (ell (canonicalDivisorOf hω - D) : ℤ)
        = Divisor.degree D + 1 - (genus K F : ℤ)

theorem functionFieldRiemannRoch_of_riemann_and_duality
    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F := by
  intro _ _ _ ω hω D
  linarith [hWD hω D]

theorem weilDuality_of_riemannIndex_of_adelic
    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :
    WeilDuality K F := by
  intro _ _ _ ω hω D
  have h1 := hRI D
  have h2 := hWD hω D
  linarith

end AlgebraicCurve

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
