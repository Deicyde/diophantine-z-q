/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

theorem fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le
    {R : Type*} [Field R] [CharZero R] (f : ℤ → R) (d : ℕ) :
    (∀ n : ℤ, (fwdDiff (1 : ℤ))^[d + 1] f n = 0) ↔
      ∃ p : Polynomial R, p.natDegree ≤ d ∧ ∀ n : ℤ, f n = p.eval (n : R) := by p2m_exact_reverting @_root_.P2MW.S_fwdDiff_iter_succ_eq_zero_iff_exists_polynomial_natDegree_le.solution
