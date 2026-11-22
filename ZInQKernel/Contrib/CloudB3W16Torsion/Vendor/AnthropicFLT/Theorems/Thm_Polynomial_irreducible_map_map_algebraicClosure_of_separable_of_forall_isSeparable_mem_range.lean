/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

theorem Polynomial.irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (hsc : ∀ θ : L, IsSeparable K θ → θ ∈ (algebraMap K L).range)
    {d : ℕ} (x : Fin d → L) (hx : AlgebraicIndependent K x) (y : L)
    (F : Polynomial (MvPolynomial (Fin d) K)) (hFm : F.Monic)
    (hFirr : Irreducible (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))))
    (hFsep : (F.map (algebraMap (MvPolynomial (Fin d) K)
      (FractionRing (MvPolynomial (Fin d) K)))).Separable)
    (hroot : F.eval₂ (MvPolynomial.aeval x : MvPolynomial (Fin d) K →ₐ[K] L).toRingHom y = 0) :
    Irreducible (F.map (MvPolynomial.map (algebraMap K (AlgebraicClosure K)))) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_map_map_algebraicClosure_of_separable_of_forall_isSeparable_mem_range.solution
