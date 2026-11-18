import BridgeDiamondRationalityV002
import ZInQKernel.Contrib.OneProof.CoeffRational
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.LowLevels

/-!
# The exact unrestricted prime-Hecke coefficient rationality contract

At levels at least three, actual localized coefficient descent proves
rationality of every actual diamond translate. The remaining smaller
positive levels use the earlier concrete coefficient proof. The guarded
actual prime-Hecke recurrence then gives precisely the original contract,
with no arithmetic-model, basis, spanning, or closure premise.
-/

noncomputable section
set_option autoImplicit false

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2
open scoped MatrixGroups ModularForm

namespace BridgeHeckeClosure

/-- The original predicate, retaining every nonzero level, integer weight,
actual cusp form, good prime, coefficient map, slash endomorphism and coset. -/
theorem heckePrimeIntegralToRational : CoeffRational.HeckePrimeIntegralToRational := by
  intro N _ k p g hk hp hgood hg
  by_cases hN : 3 ≤ N
  · have hQ : CoeffRational.IsRatForm g := CoeffRational.isRatForm_of_int hg
    exact CoeffRational.isRatForm_hecke hp hQ
      (fun u => BridgeDiamondRationality.cusp_diamond_coefficients_rational N hN k g hQ u)
  · exact ZInQ.Contrib.HeckePrimeRationality.integral_input_hecke_rational_le_six
      N k p g (by omega) hk hp hgood hg

/-- The same conclusion displayed with all original binders and operators literally. -/
theorem actual_integral_input_hecke_rational (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hk : 2 ≤ k) (hp : p.Prime) (hgood : ¬ p ∣ N)
    (hg : ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = (z : ℂ)) :
    ∀ n : ℕ, ∃ q : ℚ,
      (qExpansion 1 (heckeSlashGamma1CuspFormEnd k (diagCosetGamma1 N p) g)).coeff n = (q : ℂ) :=
  heckePrimeIntegralToRational N k p g hk hp hgood hg

end BridgeHeckeClosure
