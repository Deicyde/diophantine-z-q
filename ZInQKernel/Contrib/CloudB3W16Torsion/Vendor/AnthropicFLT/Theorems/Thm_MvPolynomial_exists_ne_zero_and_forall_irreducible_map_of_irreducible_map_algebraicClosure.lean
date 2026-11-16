/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v w

theorem MvPolynomial.exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure
    {R : Type u} [CommRing R] [IsDomain R] {σ : Type v} [Finite σ] (F : MvPolynomial σ R)
    (hF : Irreducible (MvPolynomial.map (algebraMap R (AlgebraicClosure (FractionRing R))) F)) :
    ∃ c : R, c ≠ 0 ∧ ∀ (E : Type w) [Field E] (φ : R →+* E), φ c ≠ 0 →
      Irreducible (MvPolynomial.map φ F) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_ne_zero_and_forall_irreducible_map_of_irreducible_map_algebraicClosure.solution
