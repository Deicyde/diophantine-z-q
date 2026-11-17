/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv

set_option backward.isDefEq.respectTransparency false

universe u

open TensorProduct

set_option autoImplicit false

theorem Module.finrank_baseChange_eq_of_quotient_squareZero_linearEquiv
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ^ 2 = ⊥)
    {S : Type u} [CommRing S] (φ : R ⧸ J ≃+* S)
    (P : Type u) [AddCommGroup P] [Module S P]
    (P' : Type u) [AddCommGroup P'] [Module R P'] {n : ℕ}
    (hrk : ∀ (K : Type u) [Field K] [Algebra S K], Module.finrank K (K ⊗[S] P) = n) :
    letI : Module (R ⧸ J) P := Module.compHom P φ.toRingHom
    ((R ⧸ J) ⊗[R] P' ≃ₗ[R ⧸ J] P) →
    ∀ (K : Type u) [Field K] [Algebra R K], Module.finrank K (K ⊗[R] P') = n := by p2m_exact_reverting @_root_.P2MW.S_Module_finrank_baseChange_eq_of_quotient_squareZero_linearEquiv.solution
