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
  Source file    : P2M/Sol/S_HopfAlgebra_antipode_antipode.lean
  Source sha256  : f57782c6801bf2e477a7060c07da4742ce9568156d4fef5c751423d970e6e695
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_HopfAlgebra_antipode_antipode
r2nos_namespace_dual

w03_open "Coalgebra HopfAlgebra P2MW.S_HopfAlgebra_antipode_antipode.HopfAlgebra"
r2nos_open_scoped "TensorProduct Coalgebra.TensorProduct"

namespace HopfAlgebra
r2nos_namespace_dual
w03_export "HopfAlgebra" "antipode_one antipode_mul sum_antipode_mul_eq_algebraMap_counit"
w03_open "HopfAlgebra"

section GeneralHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [HopfAlgebra R A]

private theorem antipode_algebraMap' (r : R) :
    antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

private theorem toConv_antipode_mul_toConv_id' :
    WithConv.toConv (antipode R (A := A)) * WithConv.toConv (LinearMap.id : A →ₗ[R] A)
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact sum_antipode_mul_eq_algebraMap_counit (ℛ R a)

end GeneralHopf

section CommutativeHopf
variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]

private theorem sum_antipode_antipode_mul_antipode' {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = algebraMap R A (counit (R := R) a) := by
  calc ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
      = ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i) * 𝓡.right i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [antipode_mul (antipode R (𝓡.left i)) (𝓡.right i)]
        exact mul_comm _ _
    _ = antipode R (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
        rw [map_sum]
    _ = antipode R (algebraMap R A (counit (R := R) a)) := by
        rw [sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (counit (R := R) a) := antipode_algebraMap' _

private theorem toConv_antipode_comp_antipode_mul_toConv_antipode' :
    WithConv.toConv (antipode R ∘ₗ antipode R : A →ₗ[R] A)
        * WithConv.toConv (antipode R (A := A))
      = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode' (ℛ R a)

private theorem antipode_comp_antipode' :
    (antipode R ∘ₗ antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode'
      toConv_antipode_mul_toConv_id')

end CommutativeHopf
end HopfAlgebra

theorem solution {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] [HopfAlgebra R A] (a : A) :
    HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (HopfAlgebra.antipode_comp_antipode' (R := R) (A := A)) a
end S_HopfAlgebra_antipode_antipode
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
