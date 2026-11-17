import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.SmallLevels
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LevelFive

/-!
# The prime-Hecke rationality contract at levels one through six

This combines the sign-only cases with the independently constructed level-five
case. The bound on the level is explicit. It is not the original all-level
`CoeffRational.HeckePrimeIntegralToRational` leaf.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2

/-- At every nonzero level at most six, the actual Hecke operator satisfies
exactly the original integral-input, good-prime rationality conclusion. -/
theorem integral_input_hecke_rational_le_six (N : ℕ) [NeZero N]
    (k : ℤ) (p : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hN : N ≤ 6) (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hg : ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff m = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff m =
        (q : ℂ) := by
  by_cases h5 : N = 5
  · subst N
    exact LevelFive.integral_input_hecke_rational k p g hk hp hgood hg
  · have h0 : N ≠ 0 := NeZero.ne N
    have hsign : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 6 := by omega
    exact rational_hecke_small_levels hsign hp hgood g hg

end ZInQ.Contrib.HeckePrimeRationality
