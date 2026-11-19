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
  Source file    : Definitions/Def_ModularCurve_JqCoeff.lean
  Source sha256  : e8c047f9647b8d732714c11627757eb739b92a3c9297d19d1185a935cd87fdf2
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

open HahnSeries
r2nos_open_dual "HahnSeries"

namespace ModularCurve
r2nos_namespace_dual

section JExpansion

variable (K : Type*) [CommRing K]

def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

@[simp]
theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _

theorem jqModC_rat : jqModC ℚ = jq := rfl

variable {K} in

theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') :
    (jqModC K).map f = jqModC K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (-1 : ℤ) (1 : K)).map f = HahnSeries.single (-1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
      map_one, map_zero]
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqModC, jqModC, hmul, hsingle, hseries,
    show (jNum.map (Int.castRingHom K)).map f = jNum.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNum)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNum from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNum).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) :=
  (map_jqModC (Int.castRingHom K)).symm

end JExpansion

section FunctionField

variable (K : Type*) [Field K]

def modularFunctionFieldC (N : ℕ) [NeZero N] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqModC K, jqNModC K N}

theorem jqModC_mem (N : ℕ) [NeZero N] : jqModC K ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

theorem jqNModC_mem (N : ℕ) [NeZero N] : jqNModC K N ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

theorem modularFunctionFieldC_rat (N : ℕ) [NeZero N] :
    modularFunctionFieldC ℚ N = modularFunctionField N := rfl

theorem modularFunctionFieldC_one :
    modularFunctionFieldC K 1 = IntermediateField.adjoin K {jqModC K} := by
  unfold modularFunctionFieldC
  rw [jqNModC_one, Set.pair_eq_singleton]

end FunctionField

end ModularCurve

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
