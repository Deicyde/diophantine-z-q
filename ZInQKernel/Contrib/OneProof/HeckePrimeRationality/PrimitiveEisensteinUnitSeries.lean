import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinNormalization

/-!
# Absolutely convergent primitive unit convolution

The actual gcd decomposition supplies the convergence of the unit series.
The zero gcd term and the d=1 primitive term are separated before the
finite-permutation tail is used. No invertibility or desired decomposition
hypothesis is introduced.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinUnitSeries

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinGcdData PrimitiveEisensteinNormalization

/-- The actual primitive row values, retaining the gcd-one definition. -/
def primitiveValues (N k : ℕ) (τ : ℍ) (a : PrimitiveRow N) : ℂ := eisensteinSeries a.1 (k : ℤ) τ

/-- Actual inverse-unit row permutations for divisors coprime to the level. -/
def unitPermutation (N d : ℕ) : Equiv.Perm (PrimitiveRow N) :=
  if hd : d.Coprime N then primitiveUnitEquiv N (ZMod.unitOfCoprime d hd)⁻¹ else Equiv.refl _

/-- The genuine Dirichlet coefficient, independent of τ and zero only for nonunit divisors. -/
def unitCoefficient (N k d : ℕ) : ℂ := if d.Coprime N then ((d : ℂ)^k)⁻¹ else 0

/-- The actual gcd-normalized primitive summands in the unrestricted row. -/
def unitTerm (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (τ : ℍ) (d : ℕ) : ℂ :=
  if hd : d.Coprime N then ((d : ℂ)^k)⁻¹ *
    eisensteinSeries (scaleResidue (ZMod.unitOfCoprime d hd)⁻¹ a) (k : ℤ) τ else 0

lemma unitTerm_eq_value (N k d : ℕ) (τ : ℍ) (a : PrimitiveRow N) :
    unitTerm N a.1 k τ d = unitCoefficient N k d * primitiveValues N k τ (unitPermutation N d a) := by
  unfold unitTerm unitCoefficient unitPermutation primitiveValues
  split_ifs with hd
  · rfl
  · simp only [zero_mul]

/-- The actual gcd-fiber values are summable by the actual full-vector absolute convergence. -/
lemma summable_gcd_values (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    Summable (fun d : ℕ => ∑' v : EisensteinSeries.gammaSet N d a,
      EisensteinSeries.eisSummand (k : ℤ) v.1 τ) := by
  have hs := (summable_eisSummand_vector k hk τ).subtype (congruenceSet N a)
  have hg := (congruenceGcdEquiv N a).symm.hasSum_iff.mpr hs.hasSum
  simpa only [Function.comp_apply, congruenceGcdEquiv_symm_val] using! hg.summable.sigma

/-- Each actual gcd-fiber sum is the corresponding canonical unit term on a primitive residue row. -/
lemma gcd_value_eq_unitTerm (N : ℕ) (hN : 3 ≤ N) (a : Fin 2 → ZMod N)
    (ha : IsCoprime (a 0) (a 1)) (k : ℕ) (τ : ℍ) (d : ℕ) :
    (∑' v : EisensteinSeries.gammaSet N d a, EisensteinSeries.eisSummand (k : ℤ) v.1 τ) =
      unitTerm N a k τ d := by
  unfold unitTerm
  split_ifs with hd
  · have hdpos : 0 < d := by
      by_contra h
      have hd0 : d = 0 := by omega
      subst d
      simp only [Nat.coprime_zero_left] at hd
      omega
    simpa only [_root_.zpow_neg, _root_.zpow_natCast] using!
      gammaSet_tsum_eq_primitive N d hdpos a (ZMod.unitOfCoprime d hd) (by rfl) k τ
  · let _ : IsEmpty (EisensteinSeries.gammaSet N d a) := gammaSet_isEmpty_nonunit_gcd ha hd
    simp

/-- The unit-normalized series is summable, without a primitive spanning or coefficient premise. -/
lemma summable_unitTerm (N : ℕ) (hN : 3 ≤ N) (a : PrimitiveRow N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    Summable (unitTerm N a.1 k τ) :=
  (summable_gcd_values N a.1 k hk τ).congr (gcd_value_eq_unitTerm N hN a.1 a.2 k τ)

lemma unitTerm_zero (N : ℕ) (hN : 3 ≤ N) (a : Fin 2 → ZMod N) (k : ℕ) (τ : ℍ) :
    unitTerm N a k τ 0 = 0 := by
  have hn : ¬ (0 : ℕ).Coprime N := by simp only [Nat.coprime_zero_left]; omega
  simp only [unitTerm, dite_eq_right hn]

lemma unitTerm_one (N : ℕ) (a : Fin 2 → ZMod N) (k : ℕ) (τ : ℍ) :
    unitTerm N a k τ 1 = eisensteinSeries a (k : ℤ) τ := by
  have hscale : scaleResidue (ZMod.unitOfCoprime 1 (Nat.coprime_one_left N))⁻¹ a = a := by
    funext i
    simp [scaleResidue, ZMod.unitOfCoprime]
  simp only [unitTerm, dite_eq_left (Nat.coprime_one_left N), Nat.cast_one, one_pow, inv_one,
    one_mul, hscale]

/-- The actual raw series equals the actual primitive value plus its convergent finite-permutation tail. -/
theorem unrestrictedSeries_eq_primitive_add_tail (N : ℕ) (hN : 3 ≤ N)
    (a : PrimitiveRow N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    unrestrictedSeries N a.1 k τ = primitiveValues N k τ a +
      ∑' n : ℕ, unitCoefficient N k (n+2) * primitiveValues N k τ (unitPermutation N (n+2) a) := by
  have hs := summable_unitTerm N hN a k hk τ
  have ht := Summable.sum_add_tsum_nat_add 2 hs
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at ht
  simp only [unitTerm_zero N hN, unitTerm_one, zero_add] at ht
  have htail : (fun n : ℕ => unitTerm N a.1 k τ (n+2)) =
      (fun n : ℕ => unitCoefficient N k (n+2) * primitiveValues N k τ (unitPermutation N (n+2) a)) :=
    funext fun n => unitTerm_eq_value N k (n+2) τ a
  rw [htail] at ht
  have hu := unrestrictedSeries_eq_unit_series N hN a.1 a.2 k hk τ
  simp only [_root_.zpow_neg, _root_.zpow_natCast] at hu
  change unrestrictedSeries N a.1 k τ = ∑' d : ℕ, unitTerm N a.1 k τ d at hu
  exact hu.trans ht.symm

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinUnitSeries
