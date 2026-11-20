import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The minimal-cohomology-degree Kunneth cancellation argument

H-72 L1 continuation (B). If h^0(N)=0 and Kunneth plus the multiplicative
bundle identity gives P_N^2 = P_O P_N, then all cohomology of N vanishes.
This proves the cancellation/minimal-degree argument; it does NOT assume the
Kunneth identity as a Fact or assert that the required bundle identity is
already proved from pointwise translation invariance. Those actual inputs
remain explicit and are the next geometric comparisons to construct.
-/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Coefficientwise minimal-degree proof of P_N²=P_OP_N, with h^0(N)=0 and h^0(O)=1. -/
theorem vanish_of_square_convolution (h o : ℕ → ℕ)
    (hh0 : h 0 = 0) (ho0 : o 0 = 1)
    (hconv : ∀ n : ℕ,
      (∑ i ∈ Finset.range (n + 1), h i * h (n - i)) =
        ∑ i ∈ Finset.range (n + 1), o i * h (n - i)) :
    ∀ n : ℕ, h n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have left_zero : (∑ i ∈ Finset.range (n + 1), h i * h (n - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases hin : i < n
      · rw [ih i hin, zero_mul]
      · have hin' : i = n := by omega
        rw [hin', Nat.sub_self, hh0, mul_zero]
    have right_eq : (∑ i ∈ Finset.range (n + 1), o i * h (n - i)) = h n := by
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.sub_zero, ho0, one_mul]
      · intro i hi hi0
        have hin : n - i < n := by
          have hi_le : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          omega
        rw [ih (n - i) hin, mul_zero]
      · simp
    exact right_eq.symm.trans ((hconv n).symm.trans left_zero)

/-- The actual W07 H^q groups vanish once their genuine Kunneth rank identity is supplied.
This is an ordinary conditional local lemma, NOT a desired Picard/vanishing Fact. -/
theorem native_cohomology_vanish_of_kunneth_ranks
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (N : X.Modules) [∀ q : ℕ, Module.Finite k (N.H q)]
    (hN0 : N.finrankH k 0 = 0)
    (hO0 : Scheme.Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 0 = 1)
    (hkunneth : ∀ q : ℕ,
      (∑ i ∈ Finset.range (q + 1), N.finrankH k i * N.finrankH k (q - i)) =
        ∑ i ∈ Finset.range (q + 1), Scheme.Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) i * N.finrankH k (q - i)) :
    ∀ q : ℕ, Subsingleton (N.H q) := by
  have hzero := vanish_of_square_convolution (N.finrankH k)
    (Scheme.Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf)) hN0 hO0 hkunneth
  intro q
  exact (Module.finrank_zero_iff (R := k) (M := N.H q)).mp (hzero q)

end ZInQ.Contrib.CloudR2Poincare.L1
