import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Local
import Mathlib.Data.Nat.Squarefree

/-! Weil reciprocity for the explicit local factors, tex 9000–9004.
Reduction to squarefree rational representatives and bookkeeping of the
restricted product are on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2 Visibility
open scoped BigOperators

private def signedCoefficient (negative oddValuation : Bool) (s : Finset ℕ) : ℤ :=
  coefficientSign negative * (twoPart oddValuation : ℤ) * ((∏ p ∈ s, p : ℕ) : ℤ)

private theorem signedCoefficient_ne_zero (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) : signedCoefficient negative oddValuation s ≠ 0 := by
  have hn : ((∏ p ∈ s, p : ℕ) : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr (odd_prod s fun p hp => (h p hp).2).pos.ne'
  have hs : coefficientSign negative ≠ 0 := by cases negative <;> decide
  have ht : (twoPart oddValuation : ℤ) ≠ 0 := by cases oddValuation <;> decide
  exact mul_ne_zero (mul_ne_zero hs ht) hn

private def rationalUnit (z : ℤ) (h : z ≠ 0) : ℚˣ :=
  Units.mk0 (z : ℚ) (Int.cast_ne_zero.mpr h)

/-- Base change of a nonzero rational scalar to a finite place. -/
def atPrime (p : Place) : ℚˣ →* ℚ_[p.val]ˣ :=
  Units.map (algebraMap ℚ ℚ_[p.val]).toMonoidHom

/-- Base change of a nonzero rational scalar to the real place. -/
def atReal : ℚˣ →* ℝˣ := Units.map (algebraMap ℚ ℝ).toMonoidHom

private theorem atPrime_rationalUnit (p : Place) (z : ℤ) (hz : z ≠ 0) :
    (atPrime p (rationalUnit z hz) : ℚ_[p.val]) = z := by
  change (algebraMap ℚ ℚ_[p.val]) (z : ℚ) = _
  rw [map_intCast]

private theorem atReal_rationalUnit (z : ℤ) (hz : z ≠ 0) :
    (atReal (rationalUnit z hz) : ℝ) = z := by
  change (algebraMap ℚ ℝ) (z : ℚ) = _
  rw [map_intCast]

private theorem not_dvd_signedCoefficient {s : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hps : p ∉ s) (h : ∀ q ∈ s, q.Prime ∧ Odd q)
    (negative oddValuation : Bool) : ¬ (p : ℤ) ∣ signedCoefficient negative oddValuation s := by
  have hn := prime_coprime_prod hp hps fun q hq => (h q hq).1
  have h2 : p.Coprime (twoPart oddValuation) := by
    cases oddValuation
    · simp [twoPart]
    · exact odd_coprime_two (hp.odd_of_ne_two hp2)
  have hnot := hp.coprime_iff_not_dvd.mp (h2.mul_right hn)
  have hnotZ : ¬ (p : ℤ) ∣ ((twoPart oddValuation * ∏ q ∈ s, q : ℕ) : ℤ) :=
    fun hdiv => hnot (Int.natCast_dvd_natCast.mp hdiv)
  cases negative <;>
    simpa only [signedCoefficient, coefficientSign, Bool.false_eq_true, ite_false, ite_true,
      one_mul, neg_one_mul, neg_mul, Int.dvd_neg, Int.natCast_mul] using hnotZ

private theorem dyadic_signed (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) :
    finiteExponent dyadicPlace
      (atPrime dyadicPlace (rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h))) =
      dyadicExponent oddValuation
        (if negative then -((∏ p ∈ s, p : ℕ) : ZMod 8) else ((∏ p ∈ s, p : ℕ) : ZMod 8)) := by
  let n := ∏ p ∈ s, p
  let q := rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h)
  let z := coefficientSign negative * (n : ℤ)
  have hn : Odd n := odd_prod s fun p hp => (h p hp).2
  have hnd : ¬ (2 : ℤ) ∣ z := by
    have hn' : ¬ (2 : ℤ) ∣ (n : ℤ) := by
      change ¬ ((2 : ℕ) : ℤ) ∣ (n : ℤ)
      rw [Int.natCast_dvd_natCast]
      exact fun hd => by have := Nat.mod_eq_zero_of_dvd hd; have := Nat.odd_iff.mp hn; omega
    cases negative <;> simpa [z, coefficientSign] using hn'
  have hz : (atPrime dyadicPlace q : ℚ_[dyadicPlace.val]) =
      (z : ℚ_[dyadicPlace.val]) * (dyadicPlace.val : ℚ_[dyadicPlace.val]) ^ (if oddValuation then 1 else 0 : ℕ) := by
    rw [atPrime_rationalUnit]
    cases oddValuation <;> push_cast <;> simp [z, signedCoefficient, twoPart, n]; ring
  obtain ⟨hv, hu⟩ := unitAt_of_int_times_pow dyadicPlace _ z _ hnd hz
  change finiteExponent dyadicPlace (atPrime dyadicPlace q) = _
  rw [finiteExponent_dyadic, hv]
  have hres : (dyadicUnitResidue (atPrime dyadicPlace q) : ZMod 8) = (z : ZMod 8) := by
    change (PadicInt.toZModPow (p := 2) 3) (unitAt dyadicPlace (atPrime dyadicPlace q) : ℤ_[2]) = _
    rw [hu, map_intCast]
  rw [hres]
  cases negative <;> cases oddValuation <;> simp [z, coefficientSign, n]

private theorem odd_signed (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) (p : Place) (hp : p.val ∈ s) :
    finiteExponent p
      (atPrime p (rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h))) =
      oddBase (p.val : ZMod 4) +
        signExponent (jacobiSym (signedCoefficient negative oddValuation (s.erase p.val)) p.val) := by
  have hp2 : p.val ≠ 2 := by
    intro he
    have := (h p.val hp).2
    rw [he] at this
    norm_num at this
  have hp' : p ≠ dyadicPlace := fun he => hp2 (congrArg Subtype.val he)
  let q := rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h)
  let z := signedCoefficient negative oddValuation (s.erase p.val)
  have hz : (atPrime p q : ℚ_[p.val]) = (z : ℚ_[p.val]) * (p.val : ℚ_[p.val]) ^ (1 : ℕ) := by
    rw [atPrime_rationalUnit]
    simp only [z, signedCoefficient, pow_one, Int.cast_mul, Int.cast_natCast]
    rw [mul_assoc ((coefficientSign negative : ℚ_[p.val]) * (twoPart oddValuation : ℚ_[p.val])), ← Nat.cast_mul,
      Finset.prod_erase_mul _ (fun q : ℕ => q) hp]
  obtain ⟨hv, hu⟩ := unitAt_of_int_times_pow p _ z 1
    (not_dvd_signedCoefficient p.property hp2 (Finset.notMem_erase _ _)
      (fun r hr => h r (Finset.mem_of_mem_erase hr)) negative oddValuation) hz
  change finiteExponent p (atPrime p q) = _
  rw [finiteExponent_odd p hp', oddExponent, hv]
  rw [show (↑(1 : ℕ) : ℤ) % 2 = 1 by decide, ite_eq_right (by decide)]
  have hres : (oddUnitResidue p (atPrime p q) : ZMod p.val) = (z : ZMod p.val) := by
    change PadicInt.toZMod (unitAt p (atPrime p q) : ℤ_[p.val]) = _
    rw [hu, map_intCast]
  rw [hres, ← legendreSym, jacobiSym.legendreSym.to_jacobiSym]

private theorem odd_outside (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) (p : Place) (hp : p.val ∉ s) (hp' : p ≠ dyadicPlace) :
    finiteExponent p
      (atPrime p (rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h))) = 0 := by
  have hp2 : p.val ≠ 2 := fun he => hp' (Subtype.ext he)
  have hz := atPrime_rationalUnit p _ (signedCoefficient_ne_zero negative oddValuation s h)
  obtain ⟨hv, _⟩ := unitAt_of_int_times_pow p _ _ 0
    (not_dvd_signedCoefficient p.property hp2 hp h negative oddValuation) (by simpa using hz)
  rw [finiteExponent_odd p hp', oddExponent, hv]
  rfl

private theorem atReal_signed (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) :
    gammaReal (atReal (rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h))) =
      exponentRoot (if negative then -1 else 1) := by
  have hn : 0 < ((∏ p ∈ s, p : ℕ) : ℝ) := Nat.cast_pos.mpr (odd_prod s fun p hp => (h p hp).2).pos
  have ht : 0 < (twoPart oddValuation : ℝ) := by cases oddValuation <;> norm_num [twoPart]
  have he : (signedCoefficient negative oddValuation s : ℝ) =
      (coefficientSign negative : ℝ) * (twoPart oddValuation : ℝ) * ((∏ p ∈ s, p : ℕ) : ℝ) := by
    simp only [signedCoefficient, Int.cast_mul, Int.cast_natCast]
  cases negative
  · simp only [Bool.false_eq_true, ite_false, exponentRoot_one]
    apply gammaReal_pos
    rw [atReal_rationalUnit, he]
    simpa only [coefficientSign, Bool.false_eq_true, ite_false, Int.cast_one, one_mul] using mul_pos ht hn
  · simp only [ite_true, exponentRoot_neg, exponentRoot_one]
    apply gammaReal_neg
    rw [atReal_rationalUnit, he]
    simpa only [coefficientSign, ite_true, Int.cast_neg, Int.cast_one, neg_one_mul, neg_mul, one_mul] using
      neg_lt_zero.mpr (mul_pos ht hn)

private theorem exponentRoot_sum {α : Type*} (s : Finset α) (f : α → ZMod 8) :
    exponentRoot (∑ x ∈ s, f x) = ∏ x ∈ s, exponentRoot (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, exponentRoot_add, ih]

private theorem signed_product (negative oddValuation : Bool) (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) :
    let q := rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h)
    (fun p => finiteGamma p (atPrime p q)).HasFiniteMulSupport ∧
      gammaReal (atReal q) * ∏ᶠ p, finiteGamma p (atPrime p q) = 1 := by
  classical
  dsimp only
  let q := rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h)
  let f : ↥s ↪ Place := ⟨fun p => ⟨p.val, (h p.val p.property).1⟩,
    fun a b he => Subtype.ext (congrArg (fun p : Place => p.val) he)⟩
  let t := s.attach.map f
  have hmem (p : Place) : p ∈ t ↔ p.val ∈ s := by
    simp only [t, Finset.mem_map, Finset.mem_attach, true_and]
    exact ⟨fun ⟨z, hz⟩ => congrArg (fun p : Place => p.val) hz ▸ z.property,
      fun hp => ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩⟩
  have htwo : dyadicPlace ∉ t := by
    intro ht
    have := (h _ ((hmem dyadicPlace).mp ht)).2
    change Odd 2 at this
    norm_num at this
  have hsupp : Function.mulSupport (fun p => finiteGamma p (atPrime p q)) ⊆
      (↑(insert dyadicPlace t) : Set Place) := by
    intro p hp
    by_contra hn
    have hp2 : p ≠ dyadicPlace := fun he => hn (he ▸ Finset.mem_insert_self ..)
    have hps : p.val ∉ s := fun hm => hn (Finset.mem_insert_of_mem ((hmem p).mpr hm))
    apply hp
    change exponentRoot (finiteExponent p (atPrime p q)) = 1
    rw [odd_outside negative oddValuation s h p hps hp2, exponentRoot_zero]
  refine ⟨(insert dyadicPlace t).finite_toSet.subset hsupp, ?_⟩
  change gammaReal (atReal q) * (∏ᶠ p, finiteGamma p (atPrime p q)) = 1
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_insert htwo,
    atReal_signed negative oddValuation s h]
  simp only [finiteGamma]
  rw [← exponentRoot_sum, ← exponentRoot_add, ← exponentRoot_add, dyadic_signed negative oddValuation s h]
  have hsum : (∑ p ∈ t, finiteExponent p (atPrime p q)) =
      ∑ p ∈ s, (oddBase (p : ZMod 4) +
        signExponent (jacobiSym (signedCoefficient negative oddValuation (s.erase p)) p)) := by
    rw [Finset.sum_map]
    calc
      _ = ∑ p ∈ s.attach, (oddBase (p.val : ZMod 4) +
        signExponent (jacobiSym (signedCoefficient negative oddValuation (s.erase p.val)) p.val)) := by
          apply Finset.sum_congr rfl
          intro p hp
          exact odd_signed negative oddValuation s h (f p) p.property
      _ = _ := Finset.sum_attach s (fun p : ℕ => oddBase (p : ZMod 4) +
        signExponent (jacobiSym (signedCoefficient negative oddValuation (s.erase p)) p))
  rw [hsum]
  change exponentRoot (_ + (_ + ∑ p ∈ s, (oddBase (p : ZMod 4) +
    signExponent (jacobiSym (coefficientSign negative * (twoPart oddValuation : ℤ) *
      ((∏ r ∈ s.erase p, r : ℕ) : ℤ)) p)))) = 1
  rw [signed_odd_squarefree_exponents s h, ← add_assoc]
  let n := ∏ p ∈ s, p
  have hn : Odd n := odd_prod s fun p hp => (h p hp).2
  have hn8 : IsUnit (n : ZMod 8) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (p := 2) (d := 3) Nat.prime_two (by decide)).2
      (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; have := Nat.odd_iff.mp hn; omega)
  have hcast : (ZMod.cast (n : ZMod 8) : ZMod 4) = n := ZMod.cast_natCast (by decide) n
  have he := total_exponent (n : ZMod 8) hn8 negative oddValuation
  rw [hcast] at he
  exact congrArg exponentRoot he

private theorem rational_squarefree (q : ℚˣ) :
    ∃ (negative oddValuation : Bool) (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime ∧ Odd p) (u : ℚˣ),
      q = rationalUnit _ (signedCoefficient_ne_zero negative oddValuation s h) * u ^ 2 := by
  let r := (q : ℚ)
  have hr : r ≠ 0 := q.ne_zero
  let n := r.num.natAbs * r.den
  have hn : n ≠ 0 := mul_ne_zero (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hr)) r.den_nz
  obtain ⟨e, d, hed, hsf⟩ := exists_sq_mul_squarefree n
  have he : e ≠ 0 := fun hz => hn (by simpa [hz] using hed.symm)
  let negative := decide (r.num < 0)
  let oddValuation := decide (2 ∈ d.primeFactors)
  let s := d.primeFactors.erase 2
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime ∧ Odd p := by
    have hm := Finset.mem_erase.mp hp
    have hp' := Nat.prime_of_mem_primeFactors hm.2
    exact ⟨hp', hp'.odd_of_ne_two hm.1⟩
  let u := Units.mk0 ((e : ℚ) / (r.den : ℚ))
    (div_ne_zero (Nat.cast_ne_zero.mpr he) (Nat.cast_ne_zero.mpr r.den_nz))
  refine ⟨negative, oddValuation, s, hs, u, ?_⟩
  have hd : twoPart oddValuation * (∏ p ∈ s, p) = d := by
    by_cases h2 : 2 ∈ d.primeFactors
    · simpa [s, oddValuation, twoPart, h2, Nat.mul_comm] using
        (Finset.prod_erase_mul d.primeFactors id h2).trans (Nat.prod_primeFactors_of_squarefree hsf)
    · simp [s, oddValuation, twoPart, h2,
        Nat.prod_primeFactors_of_squarefree hsf]
  have hsg : coefficientSign negative * (r.num.natAbs : ℤ) = r.num := by
    by_cases hneg : r.num < 0
    · simp only [negative, hneg, decide_true, coefficientSign, ite_true, neg_one_mul]
      rcases Int.natAbs_eq r.num with hpos | hneg'
      · have := Int.natCast_nonneg r.num.natAbs
        omega
      · exact hneg'.symm
    · simp only [negative, hneg, decide_false, coefficientSign, Bool.false_eq_true, ite_false, one_mul]
      rcases Int.natAbs_eq r.num with hpos | hneg'
      · exact hpos.symm
      · have := Int.natCast_nonneg r.num.natAbs
        omega
  apply Units.ext
  change r = (signedCoefficient negative oddValuation s : ℚ) * ((e : ℚ) / (r.den : ℚ)) ^ 2
  have hdq : (twoPart oddValuation : ℚ) * (↑(∏ p ∈ s, p) : ℚ) = (d : ℚ) := by exact_mod_cast hd
  have hsgq : (coefficientSign negative : ℚ) * (r.num.natAbs : ℚ) = (r.num : ℚ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hsg
  have hedq : (e : ℚ) ^ 2 * (d : ℚ) = (r.num.natAbs : ℚ) * (r.den : ℚ) := by exact_mod_cast hed
  have hd0 : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  calc
    r = (r.num : ℚ) / (r.den : ℚ) := (Rat.num_div_den r).symm
    _ = (coefficientSign negative : ℚ) * (d : ℚ) * ((e : ℚ) / (r.den : ℚ)) ^ 2 := by
      rw [← hsgq, div_pow]
      field_simp
      linear_combination -(coefficientSign negative : ℚ) * hedq
    _ = _ := by
      simp only [signedCoefficient, Int.cast_mul, Int.cast_natCast]
      rw [mul_assoc (coefficientSign negative : ℚ) (twoPart oddValuation : ℚ), hdq]

private theorem gammaReal_sq (a b : ℝˣ) : gammaReal (a * b ^ 2) = gammaReal a := by
  have hb : 0 < (b : ℝ) ^ 2 := sq_pos_of_ne_zero b.ne_zero
  simp [gammaReal, Units.val_mul, Units.val_pow_eq_pow_val, mul_pos_iff_of_pos_right hb]

/-- Scalar reciprocity for every nonzero rational coefficient. -/
theorem rational_weil_product (q : ℚˣ) :
    (fun p => finiteGamma p (atPrime p q)).HasFiniteMulSupport ∧
      gammaReal (atReal q) * ∏ᶠ p, finiteGamma p (atPrime p q) = 1 := by
  obtain ⟨negative, oddValuation, s, h, u, hq⟩ := rational_squarefree q
  rw [hq]
  simp only [map_mul, map_pow, finiteGamma_mul_sq, gammaReal_sq]
  exact signed_product negative oddValuation s h

/-- The explicit finite family satisfies the existing product-formula
interface for all rational diagonal lists, including the two rectangular
forms. The operator normalization is a separate local assertion. -/
theorem finiteGamma_productFormula : WeilIndexProductFormula finiteGamma := by
  intro q
  induction q with
  | nil =>
    have hx : indexAt finiteGamma [] = 1 := rfl
    simp [hx, realIndex, finiteIndex, gammaDiag, Function.HasFiniteMulSupport]
  | cons a q ih =>
    have ha := rational_weil_product a
    have hi : indexAt finiteGamma (a :: q) =
        (fun p => finiteGamma p (atPrime p a)) * indexAt finiteGamma q := rfl
    rw [hi]
    refine ⟨ha.1.mul ih.1, ?_⟩
    rw [finiteIndex, hi]
    change (gammaReal (atReal a) * realIndex q) *
      (∏ᶠ p, finiteGamma p (atPrime p a) * indexAt finiteGamma q p) = 1
    rw [finprod_mul_distrib ha.1 ih.1]
    change (gammaReal (atReal a) * realIndex q) *
      ((∏ᶠ p, finiteGamma p (atPrime p a)) * finiteIndex finiteGamma q) = 1
    rw [mul_mul_mul_comm, ha.2, ih.2, one_mul]

#print axioms signedCoefficient_ne_zero
#print axioms atPrime_rationalUnit
#print axioms atReal_rationalUnit
#print axioms not_dvd_signedCoefficient
#print axioms dyadic_signed
#print axioms odd_signed
#print axioms odd_outside
#print axioms atReal_signed
#print axioms exponentRoot_sum
#print axioms signed_product
#print axioms rational_squarefree
#print axioms gammaReal_sq
#print axioms rational_weil_product
#print axioms finiteGamma_productFormula

end ZInQ.Manuscript.RC.WeilIndex
