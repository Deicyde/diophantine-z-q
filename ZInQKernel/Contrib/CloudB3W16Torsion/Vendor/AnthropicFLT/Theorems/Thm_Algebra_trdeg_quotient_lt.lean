/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_trdeg_quotient_lt. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_trdeg_quotient_lt

set_option backward.isDefEq.respectTransparency false

universe u v

theorem Algebra.trdeg_quotient_lt {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R]
    [Algebra K R] [Algebra.FiniteType K R] (I : Ideal R) (hI : I ≠ ⊥) (hI' : I ≠ ⊤) :
    Algebra.trdeg K (R ⧸ I) < Algebra.trdeg K R := by p2m_exact_reverting @_root_.P2MW.S_Algebra_trdeg_quotient_lt.solution
