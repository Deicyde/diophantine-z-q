/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_isRegularLocalRing_localization_atPrime_mvPolynomial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_Mathlib_RingTheory_KmfloorsFiberPolynomialRegularAscent
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_mvPolynomial

set_option autoImplicit false

theorem solution (k : Type*) [Field k] (n : ℕ) (q : Ideal (MvPolynomial (Fin n) k)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := kmf2_polyasc_isRegularRing_mvPolynomial_fin k n
  exact IsRegularRing.isRegularLocalRing_localization q
