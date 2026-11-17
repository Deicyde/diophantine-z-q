/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.integralTopForms_eq_span_and_ord_smul_of_basis
    (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    integralTopForms R' K' O F d =
        Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} ∧
      ∀ a : F, a ≠ 0 → topFormMap R' K' O F d (exteriorPower.ιMulti O d b) ≠ 0 →
        ord R' K' O d F (a • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) = addOrd O F a := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis.solution
