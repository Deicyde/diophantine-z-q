/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v w

open AlgebraicCurve

theorem AlgebraicCurve.exists_placeEquiv_ord_eq_and_ell_mapDomain_eq
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']
    (σ : F ≃ₐ[K] F') :
    ∃ π : Place K F ≃ Place K F',
      (∀ v : Place K F, ((π v).toValuationSubring : Set F') = σ '' (v.toValuationSubring : Set F)) ∧
      (∀ (v : Place K F) (f : F), (π v).ord (σ f) = v.ord f) ∧
      (∀ v : Place K F, (π v).deg = v.deg) ∧
      (∀ D : Divisor K F, ell (Finsupp.mapDomain π D) = ell D) ∧
      (∀ D : Divisor K F, Divisor.degree (Finsupp.mapDomain π D) = Divisor.degree D) ∧
      (∀ D : Divisor K F, Divisor.IsPrincipal (Finsupp.mapDomain π D) ↔ Divisor.IsPrincipal D) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_placeEquiv_ord_eq_and_ell_mapDomain_eq.solution
