import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTracePartial
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Common factorial levels for independent Eisenstein-series corrections

Only level divisibility and the proved upward maps are used. No correlation,
row-constraint, Eisenstein-membership supplier or whole-space span theorem is
an input or a conclusion.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- Recursive smaller factorial levels all divide the same canonical level. -/
theorem factorial_level_dvd (L r n : ℕ) (hrn : r < n) :
    Nat.factorial r * L ∣ Nat.factorial (n - 1) * L := by
  exact Nat.mul_dvd_mul (Nat.factorial_dvd_factorial (by omega : r ≤ n - 1)) (dvd_refl L)

/-- Upward inclusion into the canonical factorial correction level. -/
theorem restriction_mem_canonical_factorial (L : ℕ) (hL : 0 < L) (r n : ℕ) (hrn : r < n)
    {f : _root_.ModularForm (ΓP (Nat.factorial r * L)) 2}
    (hf : f ∈ seriesSpan (Nat.factorial r * L) (Nat.mul_pos (Nat.factorial_pos r) hL)) :
    restriction (Nat.factorial r * L) (Nat.factorial (n - 1) * L) (factorial_level_dvd L r n hrn) f ∈
      seriesSpan (Nat.factorial (n - 1) * L) (Nat.mul_pos (Nat.factorial_pos (n - 1)) hL) :=
  restriction_mem_seriesSpan (Nat.mul_pos (Nat.factorial_pos r) hL)
    (Nat.mul_pos (Nat.factorial_pos (n - 1)) hL) (factorial_level_dvd L r n hrn) hf

/-- The factorial correction convention for an ambient level n times L. -/
theorem canonical_factorial_level_eq (n L : ℕ) (hn : 0 < n) :
    Nat.factorial (n - 1) * (n * L) = Nat.factorial n * L := by
  rw [← mul_assoc, Nat.mul_comm (Nat.factorial (n - 1)) n,
    Nat.mul_factorial_pred hn.ne']

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLevelMaps
