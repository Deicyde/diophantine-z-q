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
  Source file    : Definitions/Def_AlgebraicCurve_IsCurveOver.lean
  Source sha256  : ddc4f1ffdde98e5a811bb6f1749ff1084d23ba0ed260ebc639f755147ec5354e
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
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

class IsCurveOver : Prop extends HasPrincipalDivisors K F where

  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField

  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

namespace IsCurveOver
r2nos_namespace_dual

variable {K F}

theorem hasPrincipalDivisors [h : IsCurveOver K F] : HasPrincipalDivisors K F :=
  h.toHasPrincipalDivisors

theorem finite_residueField [IsCurveOver K F] (v : Place K F) :
    Module.Finite K v.ResidueField :=
  IsCurveOver.finiteResidue v

instance instFiniteResidue [IsCurveOver K F] (v : Place K F) : v.FiniteResidue :=
  ⟨IsCurveOver.finiteResidue v⟩

instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=
  h.kaehler_free_rank_one.1

theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=
  h.kaehler_free_rank_one.2

instance instNontrivialKaehler [IsCurveOver K F] : Nontrivial Ω[F⁄K] :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) finrank_kaehler

end IsCurveOver

namespace Place
r2nos_namespace_dual

variable {K F}

theorem deg_eq_one_of_isAlgClosed_of_finite [IsAlgClosed K] (v : Place K F)
    [Module.Finite K v.ResidueField] : v.deg = 1 := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  show Module.finrank K v.ResidueField = 1
  rw [← Module.finrank_self K]
  exact ((AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).toLinearEquiv.finrank_eq).symm

end Place

namespace IsCurveOver
r2nos_namespace_dual

variable {K F}

theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.deg = 1 :=
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  v.deg_eq_one_of_isAlgClosed_of_finite

theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :
    ∀ w : Place K F, w.deg = 1 :=
  deg_eq_one_of_isAlgClosed

end IsCurveOver

end AlgebraicCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
