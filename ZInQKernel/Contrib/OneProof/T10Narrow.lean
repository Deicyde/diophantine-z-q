import ZInQKernel.Contrib.OneProof.DeRhamPrint
import ZInQKernel.HDecomp.Textbook.T10Etale

/-! The local instance of Tate duality used in the manuscript's de Rham argument. -/

namespace T10Etale

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

/-- The integral Tate duality used in `diophantine_zq.tex` L10966–10972, over a finite
extension `F/ℚ_p` and with `ℓ = p`. There is no dimension restriction. The
`ℤ_p`-linear equivalence intertwines `galH` and the contragredient Tate action.

Milne, *Abelian Varieties* v2.0, Part I, Thm 12.1(a), p. 55, with Rem. 12.5,
p. 56 (Galois compatibility, stated without proof in the notes). The notes
are unrefereed; their status for the literature count is open. Comparing Mathlib's
pro-étale cohomology with classical étale cohomology is an on-the-spot step
(Bhatt–Scholze, *The pro-étale topology for schemes*, §5.6, locator UNVERIFIED).
Characteristic zero avoids the positive characteristic comparison of the algebraic
and separable closures. -/
def T10_TateDualityLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (A : PkgI3.AbVar F),
    ∃ φ : (A.baseChange (AlgebraicClosure F)).X.left.EllAdicCohomology p 1 ≃ₗ[ℤ_[p]]
        Module.Dual ℤ_[p] (A.T p),
      ∀ (σ : Field.absoluteGaloisGroup F) x,
        φ (galH A p σ x) = (A.galT (ℓ := p) σ⁻¹).dualMap (φ x)

/-- Restrict the old row to the local field and its residue prime. -/
theorem t10Local_of_tateDuality (h : T10_TateDuality) : T10_TateDualityLocal :=
  fun p _ F _ _ _ A => h F A p (DeRhamPrint.natCast_p_ne_zero p F)

end T10Etale

#print axioms T10Etale.t10Local_of_tateDuality
