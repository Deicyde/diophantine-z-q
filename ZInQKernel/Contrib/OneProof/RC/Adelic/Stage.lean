import ZInQKernel.Contrib.OneProof.RC.Adelic.Operations
import ZInQKernel.Contrib.OneProof.RC.Adelic.Hecke
import ZInQKernel.Contrib.OneProof.RC.ExplicitSplit.Ramification

/-!
# The algebraic inputs to the supersingular stage
Tex 8462–8490. The algebraic fields have the types of the corresponding
fields of RC/PM. The adelic class set is ready to be composed with the
geometric identification of supersingular pairs.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler

structure AlgebraicGeometry {a b : ℚ} (ell N : ℕ) (R : Order a b) where
  ram : AppF.RamifiedExactlyAtEll0Infty ell a b
  eichler : IsEichler ell N R
  classes : ClassSet R ≃ DoubleCosets R
  atkin : ∀ p : ℕ, p.Prime → 0 < N.factorization p → ClassSet R → ClassSet R
  atkin_involutive : ∀ p hp he, Function.Involutive (atkin p hp he)
  uniformizer : Equiv.Perm (ClassSet R)

/-- The adelic class set is finite for a definite quaternion order. -/
theorem finite_doubleCosets {a b : ℚ} (R : Order a b) (ha : a < 0) (hb : b < 0) :
    Finite (DoubleCosets R) := by
  let _ := finite_classSet R ha hb
  exact Finite.of_equiv _ (classesEquiv R)

/-- Assemble the algebraic data for the level order in the explicit quaternion algebra. -/
def algebraicGeometry (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3) (N : ℕ) (hN : 0 < N)
    (hcop : N.Coprime ell) : AlgebraicGeometry ell N (levelOrder ell h N hN) where
  ram := ExplicitSplit.explicit_ramifiedExactlyAtEll0Infty Fact.out h
  eichler := levelOrder_isEichler ell h N hN hcop
  classes := classesEquiv _
  atkin p hp he := atkin ell h N hN hcop p hp he
  atkin_involutive := atkin_involutive ell h N hN hcop
  uniformizer := uniformizer ell h N hN


end ZInQ.Manuscript.RC.Adelic
