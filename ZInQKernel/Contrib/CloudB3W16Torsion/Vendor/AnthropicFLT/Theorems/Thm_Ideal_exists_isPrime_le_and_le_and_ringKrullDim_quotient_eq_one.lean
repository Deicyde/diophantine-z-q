/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u v

theorem Ideal.exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one
    (k : Type u) [Field k] [IsAlgClosed k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (hA : 1 ≤ ringKrullDim A)
    (m₀ m₁ : Ideal A) [m₀.IsMaximal] [m₁.IsMaximal] :
    ∃ P : Ideal A, P.IsPrime ∧ P ≤ m₀ ∧ P ≤ m₁ ∧ ringKrullDim (A ⧸ P) = 1 := by p2m_exact_reverting @_root_.P2MW.S_Ideal_exists_isPrime_le_and_le_and_ringKrullDim_quotient_eq_one.solution
