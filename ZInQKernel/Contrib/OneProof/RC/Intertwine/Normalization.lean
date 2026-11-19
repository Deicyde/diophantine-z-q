import ZInQKernel.Contrib.OneProof.RC.Intertwine.FinitePlaces
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Nat.Factorization.Defs

/-! The determinant factor for the rectangular polar form, tex 8647–8652,
9004–9007 and 9027–9029. Prime factorization is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open scoped BigOperators

def determinant (a : Fin 3 → ℕ) : ℕ := ∏ i, 2 * a i

def primeFactorPlace (d : ℕ) : {p // p ∈ d.primeFactors} ↪ Place :=
  ⟨fun p => ⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩,
    fun _ _ h => Subtype.ext (congrArg (fun p : Place => p.val) h)⟩

def badPlaces (d : ℕ) : Finset Place := d.primeFactors.attach.map (primeFactorPlace d)

def localNorm (d : ℕ) (p : Place) : ℝ := ‖(d : ℚ_[p.val])‖

theorem product_localNorm (d : ℕ) (hd : d ≠ 0) :
    (∏ p ∈ badPlaces d, localNorm d p) = (d : ℝ)⁻¹ := by
  have h (p : Place) : localNorm d p = ((p.val : ℝ) ^ d.factorization p.val)⁻¹ := by
    rw [localNorm, Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr hd),
      Padic.valuation_natCast, Nat.factorization_def _ p.property, zpow_neg, zpow_natCast]
  simp_rw [h, Finset.prod_inv_distrib]
  congr 1
  have hcast := congrArg (fun k : ℕ => (k : ℝ)) (Nat.prod_factorization_pow_eq_self hd)
  simp only [Finsupp.prod, Nat.support_factorization, Nat.cast_prod, Nat.cast_pow] at hcast
  rw [← hcast, badPlaces, Finset.prod_map]
  change (∏ p ∈ d.primeFactors.attach, ((p.val : ℕ) : ℝ) ^ d.factorization p.val) = _
  exact Finset.prod_attach d.primeFactors (fun p : ℕ => (p : ℝ) ^ d.factorization p)

theorem localNorm_good {d : ℕ} (hd : d ≠ 0) {p : Place} (hp : p ∉ badPlaces d) :
    localNorm d p = 1 := by
  apply Padic.norm_natCast_eq_one_iff.mpr
  apply p.property.coprime_iff_not_dvd.mpr
  intro h
  have hmem : p.val ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨p.property, h, hd⟩
  apply hp
  rw [badPlaces, Finset.mem_map]
  exact ⟨⟨p.val, hmem⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

def finiteVolume (a : Fin 3 → ℕ) : ℝ :=
  ∏ p ∈ badPlaces (determinant a), Real.sqrt (localNorm (determinant a) p)

theorem finiteVolume_eq {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] :
    (finiteVolume a : ℂ) = ∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ) := by
  have hd : determinant a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (2 * a i)
  have hloc : (∏ p ∈ badPlaces (determinant a), (localNorm (determinant a) p) ^ (1 / 2 : ℝ)) =
      (∏ p ∈ badPlaces (determinant a), localNorm (determinant a) p) ^ (1 / 2 : ℝ) :=
    Real.finsetProd_rpow _ _ (fun p _ => show 0 ≤ localNorm (determinant a) p from norm_nonneg _) _
  have hdet : ((determinant a : ℕ) : ℝ) ^ (1 / 2 : ℝ) =
      ∏ i, (((2 * a i : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
    rw [determinant, Nat.cast_prod]
    exact (Real.finsetProd_rpow _ _ (fun i _ => Nat.cast_nonneg _) _).symm
  unfold finiteVolume
  simp_rw [Real.sqrt_eq_rpow]
  rw [hloc, product_localNorm _ hd, Real.inv_rpow (Nat.cast_nonneg _), hdet,
    ← Finset.prod_inv_distrib]
  change Complex.ofRealHom (∏ i : Fin 3, (((2 * a i : ℕ) : ℝ) ^ (1 / 2 : ℝ))⁻¹) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (((((2 * a i : ℕ) : ℝ) ^ (1 / 2 : ℝ))⁻¹ : ℝ) : ℂ) = _
  rw [Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast <;> norm_num [one_div]

#print axioms product_localNorm
#print axioms localNorm_good
#print axioms finiteVolume_eq

end ZInQ.Manuscript.RC.Intertwine
