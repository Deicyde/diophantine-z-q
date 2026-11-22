/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

theorem AddCommGroup.exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add
    {M : Type*} [AddCommGroup M] {R : Type*} [Field R] [CharZero R] (f : M → R) (d : ℕ)
    (hf : ∀ x y : M, ∃ p : Polynomial R, p.natDegree ≤ d ∧
      ∀ n : ℤ, f (n • x + y) = p.eval (n : R))
    {ι : Type*} [Fintype ι] (e : ι → M) :
    ∃ P : MvPolynomial ι R, P.totalDegree ≤ d ∧
      ∀ c : ι → ℤ, MvPolynomial.eval (fun i => (c i : R)) P = f (∑ i, c i • e i) := by p2m_exact_reverting @_root_.P2MW.S_AddCommGroup_exists_mvPolynomial_totalDegree_le_eval_eq_of_forall_exists_polynomial_zsmul_add.solution

