/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one

set_option backward.isDefEq.respectTransparency false

universe u

open Polynomial

theorem Algebra.finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one
    {K : Type u} [Field K] {D E O : Type u} [CommRing D] [CommRing E] [CommRing O]
    [IsDomain D] [IsDomain E] [Algebra K D] [Algebra K E] [Algebra K O]
    (φ : D →ₐ[K] O) (ψ : E →ₐ[K] O) (a : D) (b : E)
    (hφ : letI := φ.toRingHom.toAlgebra; IsLocalization.Away a O)
    (hψ : letI := ψ.toRingHom.toAlgebra; IsLocalization.Away b O)
    (hab : φ a * ψ b = 1)
    (hfinD : (Polynomial.aeval a : K[X] →ₐ[K] D).toRingHom.Finite)
    (hfinE : (Polynomial.aeval b : K[X] →ₐ[K] E).toRingHom.Finite)
    (hinj : Function.Injective (Polynomial.aeval a : K[X] →ₐ[K] D))
    (x : K) :
    Module.finrank K (D ⧸ Ideal.span {a - algebraMap K D x}) =
      Module.finrank K (E ⧸ Ideal.span {b}) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_finrank_quotient_span_sub_eq_of_isLocalization_away_of_mul_eq_one.solution
