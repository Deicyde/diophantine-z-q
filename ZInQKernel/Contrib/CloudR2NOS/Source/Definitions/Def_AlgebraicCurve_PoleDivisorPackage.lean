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
  Source file    : Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean
  Source sha256  : d2ec107df060c78b17179ae7f66619de72f0bbc9907b9db1ec03959c76d04532
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where

  x : F

  B : Divisor K F

  hB_eff : 0 ≤ B

  hx_mem : x ∈ LSpace B

  n : ℕ

  hn_pos : 0 < n

  degB_eq : Divisor.degree B = n

  c : ℕ

  u : Fin n → F

  hu_mem : ∀ i, u i ∈ LSpace (c • B)

  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

def HasPoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  Nonempty (PoleDivisorPackage K F)

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where

  x : E

  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)

  v : Place K E

  hvdeg : v.deg = 1

  hxv : v.ord x = -1

  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower
r2nos_namespace_dual

variable (T : TranscendenceTower K E F)

abbrev xF : F := algebraMap E F T.x

def poleDivisor [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] : Divisor K F :=
  Divisor.pullback F (Finsupp.single T.v 1)

def RegularOutside (A : Type*) [CommRing A] [Algebra A E] (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

end TranscendenceTower

structure IntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) where

  c : ℕ

  u : Fin (Module.finrank E F) → F

  hu_indep : LinearIndependent E u

  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in

def HasIntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

variable (K E F) in

def HasIntegralBasisRegularOutside [Algebra.IsSeparable E F] (T : TranscendenceTower K E F) : Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

variable (K E F) in

def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

end AlgebraicCurve

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
