import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveRationalGenerators
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveDiamondFromBasis

/-!
# Prime Hecke rationality at level five

The weight-one generators used here are explicitly constructed torsion-theta
modular forms. Their rational coefficients, normalizations and integer
non-sign diamond matrix are proved in the imported contributions, so no
basis, Galois, generator-existence or rationality premise remains in these
exports. This proves the level-five specialization only, not the original
all-level `CoeffRational.HeckePrimeIntegralToRational` leaf.
-/

noncomputable section

namespace ZInQ.Contrib.HeckePrimeRationality.LevelFive

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open NormalizedFive

/-- Every diamond class preserves rational coefficients at every natural
weight, on the actual analytic modular-form space at level five. -/
theorem rational_diamond (n : ℕ)
    (g : ModularForm ((Gamma1 5).map (mapGL ℝ)) (n : ℤ))
    (hg : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff m = (q : ℂ))
    (u : (ZMod 5)ˣ) :
    ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 (diamondOp (n : ℤ) u g)).coeff m = (q : ℂ) := by
  exact ThetaFiveDiamondFromBasis.isRat_diamondOp
    (A := A) (B := B) A_rational B_rational diamond_two_A diamond_two_B
    (by simpa only [coefficient_apply] using A_coeff_zero)
    (by simpa only [coefficient_apply] using A_coeff_one)
    (by simpa only [coefficient_apply] using B_coeff_zero) n g hg u

/-- The actual prime-Hecke operator preserves rational cusp-form coefficients
at level five, including the bad-prime case, for every nonnegative weight. -/
theorem rational_hecke (k : ℤ) (hk : 0 ≤ k) (p : ℕ) (hp : p.Prime)
    (g : CuspForm ((Gamma1 5).map (mapGL ℝ)) k)
    (hg : ∀ m : ℕ, ∃ q : ℚ, (qExpansion 1 g).coeff m = (q : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 5 p) g)).coeff m =
        (q : ℂ) := by
  exact ThetaFiveDiamondFromBasis.isRat_hecke
    (A := A) (B := B) A_rational B_rational diamond_two_A diamond_two_B
    (by simpa only [coefficient_apply] using A_coeff_zero)
    (by simpa only [coefficient_apply] using A_coeff_one)
    (by simpa only [coefficient_apply] using B_coeff_zero) k hk hp g hg

/-- The exact integral-input, good-prime conclusion of the original leaf
specialized to level five. Only the original input hypotheses remain.
The unused good-prime restriction is retained to match that contract. -/
theorem integral_input_hecke_rational (k : ℤ) (p : ℕ)
    (g : CuspForm ((Gamma1 5).map (mapGL ℝ)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (_hgood : ¬ p ∣ 5)
    (hg : ∀ m : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff m = (z : ℂ)) :
    ∀ m : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 5 p) g)).coeff m =
        (q : ℂ) := by
  apply rational_hecke k (by omega) p hp g
  intro m
  obtain ⟨z, hz⟩ := hg m
  exact ⟨(z : ℚ), by simpa using hz⟩

end ZInQ.Contrib.HeckePrimeRationality.LevelFive
