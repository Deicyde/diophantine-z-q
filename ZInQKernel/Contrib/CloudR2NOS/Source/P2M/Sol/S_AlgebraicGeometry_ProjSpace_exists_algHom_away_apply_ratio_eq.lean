/-
NEW EDITION (H5 lane4 , 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean
  Source sha256  : 43bc6677cda2efeeb9568b055b22f230ae5d36f616720749d55b0463f4f530af
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
r2nos_namespace_dual

set_option autoImplicit false

universe u v

w03_open "MvPolynomial HomogeneousLocalization AlgebraicGeometry P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "ProjSpace.ratio ProjSpace.val_algebraMap"
namespace ProjSpace
r2nos_namespace_dual
w03_export "AlgebraicGeometry.ProjSpace" "ratio val_algebraMap map"
namespace ChartLift
r2nos_namespace_dual
w03_open "AlgebraicGeometry.ProjSpace AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
  {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

noncomputable def lift0 : Localization.Away (X i : MvPolynomial (Fin (n + 1)) R) →+* B :=
  IsLocalization.Away.lift (X i : MvPolynomial (Fin (n + 1)) R)
    (g := (MvPolynomial.aeval b : MvPolynomial (Fin (n + 1)) R →ₐ[R] B).toRingHom)
    (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X, hb]; exact isUnit_one)

theorem lift0_algebraMap (p : MvPolynomial (Fin (n + 1)) R) :
    lift0 R n i b hb (algebraMap _ _ p) = MvPolynomial.aeval b p :=
  IsLocalization.Away.lift_eq _ _ _

noncomputable def liftAway : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B where
  toRingHom := (lift0 R n i b hb).comp (algebraMap (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R)) (Localization.Away (X i : MvPolynomial (Fin (n + 1)) R)))
  commutes' r := by
    show lift0 R n i b hb ((algebraMap R (Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R)) r).val) = algebraMap R B r
    rw [ProjSpace.val_algebraMap, lift0_algebraMap, MvPolynomial.aeval_C]

theorem liftAway_ratio (k : Fin (n + 1)) : liftAway R n i b hb (ProjSpace.ratio R n i k) = b k := by
  show lift0 R n i b hb (ProjSpace.ratio R n i k).val = b k
  rw [ProjSpace.ratio, Away.val_mk, Localization.mk_eq_mk', lift0, IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]

  show MvPolynomial.aeval b (X k) = MvPolynomial.aeval b (X i ^ 1) * b k
  simp [hb]

include hb in
theorem exists_algHom :
    ∃ φ : Away 𝒜 (X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B, ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  ⟨liftAway R n i b hb, liftAway_ratio R n i b hb⟩

end AlgebraicGeometry.ProjSpace.ChartLift

section
attribute [local instance] MvPolynomial.gradedAlgebra
theorem solution
    (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1))
    {B : Type v} [CommRing B] [Algebra R B] (b : Fin (n + 1) → B) (hb : b i = 1) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) →ₐ[R] B,
      ∀ k, φ (ProjSpace.ratio R n i k) = b k :=
  AlgebraicGeometry.ProjSpace.ChartLift.exists_algHom R n i b hb
end
end S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
