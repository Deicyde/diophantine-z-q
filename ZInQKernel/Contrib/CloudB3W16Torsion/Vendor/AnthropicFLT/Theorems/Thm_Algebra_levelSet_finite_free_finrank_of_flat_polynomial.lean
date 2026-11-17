/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_levelSet_finite_free_finrank_of_flat_polynomial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial

set_option backward.isDefEq.respectTransparency false

universe u

open Polynomial
open scoped TensorProduct

theorem Algebra.levelSet_finite_free_finrank_of_flat_polynomial
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (f : A) (d : ℕ)
    (hfin : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Finite)
    (hflat : (Polynomial.aeval f : R[X] →ₐ[R] A).toRingHom.Flat)
    (hrank : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] A ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : A)}) = d) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      Module.Finite S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.Free S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) ∧
        Module.finrank S (S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : A)}) = d := by p2m_exact_reverting @_root_.P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.solution
