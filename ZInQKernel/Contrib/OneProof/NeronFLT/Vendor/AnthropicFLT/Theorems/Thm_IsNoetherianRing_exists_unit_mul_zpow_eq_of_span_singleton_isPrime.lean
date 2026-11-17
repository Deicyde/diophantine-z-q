/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem IsNoetherianRing.exists_unit_mul_zpow_eq_of_span_singleton_isPrime
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (π : A) (hπ : (Ideal.span {π}).IsPrime) (hπ0 : π ≠ 0)
    (a : K) (hab : ∃ (m : ℕ) (b : A), a * algebraMap A K π ^ m = algebraMap A K b)
    (hac : ∃ (m : ℕ) (c : A), a⁻¹ * algebraMap A K π ^ m = algebraMap A K c) (ha0 : a ≠ 0) :
    ∃ (n : ℤ) (u : Aˣ), a = algebraMap A K (u : A) * algebraMap A K π ^ n := by p2m_exact_reverting @_root_.P2MW.S_IsNoetherianRing_exists_unit_mul_zpow_eq_of_span_singleton_isPrime.solution
