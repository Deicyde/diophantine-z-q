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
  Source file    : P2M/Sol/S_AlgebraicCurve_finite_H1_of_genusReached.lean
  Source sha256  : f1696975ce2d0f9432e76638039311516b941fe2b35a0a2777e6e15c531ab821
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 8 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_finite_H1_of_genusReached
r2nos_namespace_dual

set_option autoImplicit false

open AlgebraicCurve in
r2nos_open_dual "AlgebraicCurve" in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (H1 D) := by
  obtain ⟨hfin, -⟩ := indexOfSpecialty_eq_of_genusReached h D
  let e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F) :=
    { toFun := fun a => ⟨(a : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mp a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ : ↥(adeleSpace K F) →ₗ[K] H1 D := (repartitionsOf D ⊔ principalRepartitions K F).mkQ ∘ₗ e
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨⟨(β : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr β.2⟩, ?_⟩
    rfl
  have hker : adeleBddPrincipal K F D ≤ LinearMap.ker φ := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left (mem_repartitionsOf_iff_coe_mem_adeleBdd.mpr ha)
    · intro a ha
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨f, hf⟩ := LinearMap.mem_range.mp ha
      refine Submodule.mem_sup_right (mem_principalRepartitions_iff.mpr ⟨f, ?_⟩)
      funext v
      have hv := congrFun hf v
      rw [diagonalHom_apply] at hv
      exact hv.symm
  have hψ : Function.Surjective ((adeleBddPrincipal K F D).liftQ φ hker) := by
    intro q
    obtain ⟨a, rfl⟩ := hφ q
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  exact Module.Finite.of_surjective _ hψ
end S_AlgebraicCurve_finite_H1_of_genusReached
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
