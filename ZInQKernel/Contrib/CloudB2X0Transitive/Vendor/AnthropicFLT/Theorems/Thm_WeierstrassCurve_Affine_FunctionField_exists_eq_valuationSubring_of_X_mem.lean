/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem WeierstrassCurve.Affine.FunctionField.exists_eq_valuationSubring_of_X_mem {K : Type*} [Field K] (W : WeierstrassCurve K) [IsDedekindDomain W.toAffine.CoordinateRing] (O : ValuationSubring W.toAffine.FunctionField) (hO : O ≠ ⊤) (hK : ∀ c : K, algebraMap K W.toAffine.FunctionField c ∈ O) (hX : algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X)) ∈ O) : ∃ v : IsDedekindDomain.HeightOneSpectrum W.toAffine.CoordinateRing, O = (v.valuation W.toAffine.FunctionField).valuationSubring := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_exists_eq_valuationSubring_of_X_mem.solution
