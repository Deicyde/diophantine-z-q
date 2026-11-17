/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WittVector_exists_valuationSubring_lift_with_transcendental
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WittVector_exists_valuationSubring_lift_with_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem WittVector.exists_valuationSubring_lift_with_transcendental
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] [PerfectRing K p] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : WittVector p K →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : K →+* IsLocalRing.ResidueField A),
      (∀ a : K, IsLocalRing.residue A ⟨φ (WittVector.teichmuller p a), hφ _⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial (WittVector p K), P ≠ 0 → P.eval₂ φ t ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_valuationSubring_lift_with_transcendental.solution
