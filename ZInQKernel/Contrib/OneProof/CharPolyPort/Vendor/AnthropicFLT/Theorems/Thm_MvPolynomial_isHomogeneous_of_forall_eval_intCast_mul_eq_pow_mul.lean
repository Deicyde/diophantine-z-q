/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul. Apache-2.0.
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
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

theorem MvPolynomial.isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] {ι : Type*} (P : MvPolynomial ι R) (d : ℕ)
    (h : ∀ (n : ℤ) (c : ι → ℤ), MvPolynomial.eval (fun i => ((n * c i : ℤ) : R)) P =
      (n : R) ^ d * MvPolynomial.eval (fun i => (c i : R)) P) :
    P.IsHomogeneous d := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_isHomogeneous_of_forall_eval_intCast_mul_eq_pow_mul.solution

