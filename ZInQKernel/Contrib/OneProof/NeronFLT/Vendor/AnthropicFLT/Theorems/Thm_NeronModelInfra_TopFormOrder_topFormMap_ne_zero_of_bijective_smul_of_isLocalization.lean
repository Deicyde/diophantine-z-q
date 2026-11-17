/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open NeronModelInfra

theorem NeronModelInfra.TopFormOrder.topFormMap_ne_zero_of_bijective_smul_of_isLocalization
    (K A F : Type u) [Field K] [CommRing A] [Algebra K A] [Field F] [Algebra A F] [Algebra K F]
    [IsScalarTower K A F] (M : Submonoid A) [IsLocalization M F]
    (d : ℕ) (b : Module.Basis (Fin d) A (Ω[A⁄K]))
    (ω : ⋀[A]^d (Ω[A⁄K])) (hω : Function.Bijective fun g : A => g • ω) :
    TopFormOrder.topFormMap K K A F d ω ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_topFormMap_ne_zero_of_bijective_smul_of_isLocalization.solution
