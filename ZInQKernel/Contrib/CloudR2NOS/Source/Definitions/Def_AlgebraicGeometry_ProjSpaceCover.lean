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
  Source file    : Definitions/Def_AlgebraicGeometry_ProjSpaceCover.lean
  Source sha256  : c0f42f4cd038153f6d545efed3e07bb1811eb5413e3cd91e0d6a53952d8da28f
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
r2nos_open_dual "CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial"

namespace AlgebraicGeometry
r2nos_namespace_dual

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace
r2nos_namespace_dual

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

def stdCover : Scheme.OrderedAffineCover.{u} (Proj 𝒜) where
  ι := ULift.{u} (Fin (n + 1))
  U j := AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  isAffineOpen j := AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j.down)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j.down))
    one_pos
  iSup_eq_top := by
    have key : (⨆ j : ULift.{u} (Fin (n + 1)),
        AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down))
        = ⨆ j : Fin (n + 1), AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
      refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
      · exact le_iSup (fun j' : Fin (n + 1) => AlgebraicGeometry.Proj.basicOpen 𝒜 (X j')) j.down
      · exact le_iSup (fun j' : ULift.{u} (Fin (n + 1)) =>
          AlgebraicGeometry.Proj.basicOpen 𝒜 (X j'.down)) (ULift.up j)
    rw [key]
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 _
      (irrelevant_le_span_X R n)

theorem stdCover_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCover R n).U j = AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down) := rfl

end StdCover

section StdCoverPullback

variable {A : Type u} [CommRing A] {n : ℕ}
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

def stdCoverPullback : Scheme.OrderedAffineCover.{u} W :=
  let f := ι
  { ι := ULift.{u} (Fin (n + 1))
    U := fun j => f ⁻¹ᵁ ((stdCover A n).U j)
    isAffineOpen := fun j => ((stdCover A n).isAffineOpen j).preimage f
    iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top f (stdCover A n).iSup_eq_top }

theorem stdCoverPullback_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCoverPullback ι).U j = ι ⁻¹ᵁ (stdCover A n).U j := rfl

end StdCoverPullback

end ProjSpace

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
