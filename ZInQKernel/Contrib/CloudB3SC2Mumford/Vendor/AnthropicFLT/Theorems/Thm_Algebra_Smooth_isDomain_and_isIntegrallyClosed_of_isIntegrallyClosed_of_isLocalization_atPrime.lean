/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.solution
