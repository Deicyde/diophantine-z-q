import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Finite homogeneous rectangular expansions and exact weight normalization

Finite products of n-term sums expand over the independent choice of one
rectangular translate for each factor. The rational scaling coefficient is
proved from the actual integral-weight power normalization.
-/

open Complex
open scoped BigOperators

namespace RectangularProductExpansion

lemma product_of_sums (k n : ℕ) (c : ℂ) (f : Fin k → Fin n → ℂ) :
    (∏ i : Fin k, c * ∑ b : Fin n, f i b) =
      c ^ k * ∑ choice : Fin k → Fin n, ∏ i : Fin k, f i (choice i) := by
  rw [Finset.prod_mul_distrib,Fin.prod_const,Fintype.prod_sum]

lemma forward_weight_factor {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℂ) ^ ((k : ℤ)-1) * (1/(n : ℂ)) ^ k = 1/(n : ℂ) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  rw [one_div,inv_pow,← zpow_natCast,← zpow_neg,← zpow_add₀ hnC]
  rw [show (k : ℤ)-1 + -(k : ℤ) = -1 by ring,zpow_neg_one]

end RectangularProductExpansion
