/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.solution
