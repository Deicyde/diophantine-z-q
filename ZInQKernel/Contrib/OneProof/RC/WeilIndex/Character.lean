import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Basic.Complex.Basic

/-! The signed residue character of the extracted form, tex 8891–8936.
The passage from the odd Jacobi symbol and the dyadic sign to a homomorphism
at the old level is on-the-spot (c). -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

private theorem jacobi_congr {m : ℕ} {a b : ℤ}
    (h : (a : ZMod m) = (b : ZMod m)) : jacobiSym a m = jacobiSym b m := by
  rw [jacobiSym.mod_left a, jacobiSym.mod_left b, (ZMod.intCast_eq_intCast_iff' a b m).mp h]

private def jacobiOn (m : ℕ) (x : ZMod m) : ℤ := jacobiSym (x.val : ℤ) m

private theorem jacobiOn_intCast (m : ℕ) [NeZero m] (a : ℤ) :
    jacobiOn m a = jacobiSym a m := by
  apply jacobi_congr
  simp

private theorem jacobiOn_unit (m : ℕ) (u : (ZMod m)ˣ) : IsUnit (jacobiOn m u) := by
  have hc : ((u : ZMod m).val : ℤ).gcd m = 1 := by
    simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using ZMod.val_coe_unit_coprime u
  rcases jacobiSym.eq_one_or_neg_one hc with h | h <;> simp [jacobiOn, h]

/-- The product of the odd factors on residues modulo the odd part (m).
This also gives a convenient homomorphism when (m) has repeated primes. -/
def oddDeterminant (m : ℕ) [NeZero m] : (ZMod m)ˣ →* ℤˣ where
  toFun u := (jacobiOn_unit m u).unit
  map_one' := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_one]
    simpa only [Int.cast_one, jacobiSym.one_left] using jacobiOn_intCast m 1
  map_mul' u v := by
    apply Units.ext
    simp only [Units.val_mul, IsUnit.unit_spec]
    have h (w : ZMod m) : ((w.val : ℤ) : ZMod m) = w := by simp
    rw [← h (u : ZMod m), ← h (v : ZMod m), ← Int.cast_mul,
      jacobiOn_intCast, jacobiSym.mul_left, jacobiOn_intCast, jacobiOn_intCast]

/-- The determinant character is the product of the dyadic sign and the
odd factors, pulled back along the two reductions of the actual old level. -/
def determinantCharacter {m N : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N) :
    (ZMod N)ˣ →* ℤˣ :=
  ZMod.χ₄.toUnitHom.comp (ZMod.unitsMap h4) *
    (oddDeterminant m).comp (ZMod.unitsMap hm)

private theorem unitsMap_intCast {n N : ℕ} (h : n ∣ N) (u : (ZMod N)ˣ)
    {d : ℤ} (hd : (u : ZMod N) = (d : ZMod N)) :
    (ZMod.unitsMap h u : ZMod n) = (d : ZMod n) := by
  change (ZMod.castHom h (ZMod n)) (u : ZMod N) = (d : ZMod n)
  rw [hd, map_intCast]

/-- Evaluation on an arbitrary signed representative of an old-level unit. -/
theorem determinantCharacter_intCast {m N : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N)
    (u : (ZMod N)ˣ) {d : ℤ} (hd : (u : ZMod N) = (d : ZMod N)) :
    (determinantCharacter h4 hm u : ℤ) = ZMod.χ₄ (d : ZMod 4) * jacobiSym d m := by
  simp only [determinantCharacter, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  change (ZMod.χ₄.toUnitHom (ZMod.unitsMap h4 u) : ℤ) *
    ((jacobiOn_unit m (ZMod.unitsMap hm u)).unit : ℤ) = _
  rw [IsUnit.unit_spec]
  rw [MulChar.coe_toUnitHom, unitsMap_intCast h4 u hd, unitsMap_intCast hm u hd,
    jacobiOn_intCast]

/-- Jacobi reciprocity assembles the local determinants on an odd positive
representative, including the dyadic contribution. The identity even holds
without assuming coprimality. -/
theorem determinant_reciprocity {m d : ℕ} (hm : m % 4 = 3) (hd : Odd d) :
    ZMod.χ₄ (d : ZMod 4) * jacobiSym (d : ℤ) m = jacobiSym (m : ℤ) d := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hd) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul]
    exact (jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) h).symm
  · rw [ZMod.χ₄_nat_three_mod_four h, neg_one_mul]
    exact (jacobiSym.quadratic_reciprocity_three_mod_four hm h).symm

/-- On odd positive representatives the determinant character is ((m/d)). -/
theorem determinantCharacter_natCast {m N d : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N)
    (h3 : m % 4 = 3) (u : (ZMod N)ˣ) (hu : (u : ZMod N) = (d : ZMod N))
    (hd : Odd d) : (determinantCharacter h4 hm u : ℤ) = jacobiSym (m : ℤ) d := by
  rw [determinantCharacter_intCast h4 hm u (d := (d : ℤ)) (by simpa using hu)]
  simpa using determinant_reciprocity h3 hd

/-- The determinant character is even: the nontrivial odd and dyadic values
at (-1) cancel. -/
theorem determinantCharacter_neg_one {m N : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N)
    (h3 : m % 4 = 3) : determinantCharacter h4 hm (-1) = 1 := by
  apply Units.ext
  rw [determinantCharacter_intCast h4 hm (-1) (d := -1) (by simp),
    jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₄_nat_three_mod_four h3,
    ZMod.χ₄_int_three_mod_four (n := -1) (by decide)]
  rfl

/-- The old-stage character at the supplied old level, given the individual
root-weight characters on their conductor quotients. -/
def oldCharacter {m N : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ N)
    (α : ∀ i, (ZMod (c i))ˣ →* ℂˣ) : (ZMod N)ˣ →* ℂˣ :=
  (∏ i ∈ s, (α i).comp (ZMod.unitsMap (hc i))) *
    (Units.map (Int.castRingHom ℂ)).comp (determinantCharacter h4 hm)

/-- Evaluation of the old character on positive odd representatives.
Each `α i` is evaluated at the reduction to its own conductor. -/
theorem oldCharacter_natCast {m N d : ℕ} [NeZero m] (h4 : 4 ∣ N) (hm : m ∣ N)
    {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ N)
    (α : ∀ i, (ZMod (c i))ˣ →* ℂˣ) (h3 : m % 4 = 3) (u : (ZMod N)ˣ)
    (hu : (u : ZMod N) = (d : ZMod N)) (hd : Odd d) :
    (oldCharacter h4 hm s c hc α u : ℂ) =
      (∏ i ∈ s, (α i (ZMod.unitsMap (hc i) u) : ℂ)) * (jacobiSym (m : ℤ) d : ℂ) := by
  classical
  simp [oldCharacter, MonoidHom.finsetProd_apply, determinantCharacter_natCast h4 hm h3 u hu hd]

private theorem jacobi_prod_right {ι : Type*} (s : Finset ι) (f : ι → ℕ) (d : ℤ)
    (h : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym d (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym d (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs (i : ι) (hi : i ∈ s) := h i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      jacobiSym.mul_right' _ (h a (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hs),
      ih hs]

/-- The individual prime contributions to the odd determinant character
are precisely the Legendre symbols raised to the valuation of (m). -/
theorem oddFactors_eq_jacobi {m : ℕ} (hm : m ≠ 0) (d : ℤ) :
    (∏ p ∈ m.primeFactors, jacobiSym d p ^ padicValNat p m) = jacobiSym d m := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hm]
  rw [jacobi_prod_right _ _ _ (fun p hp => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Finset.prod_congr rfl
  intro p hp
  rw [jacobiSym.pow_right, Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]

/-- The dyadic exponent in tex 8895 gives the mod-four character when
(m\equiv3\pmod4). This statement uses signed integer representatives. -/
theorem dyadic_sign {m : ℕ} (hm : m % 4 = 3) (d : ℤ) (hd : Odd d) :
    (if ((d - 1) / 2 * (((m : ℤ) - 1) / 2)) % 2 = 0 then (1 : ℤ) else -1) =
      ZMod.χ₄ (d : ZMod 4) := by
  have hm' : ((m : ℤ) - 1) / 2 % 2 = 1 := by omega
  have h' : ((d - 1) / 2 * (((m : ℤ) - 1) / 2)) % 2 = (d - 1) / 2 % 2 := by
    rw [Int.mul_emod, hm', mul_one, Int.emod_emod]
  rw [h', ZMod.χ₄_int_eq_if_mod_four]
  have hd' := Int.odd_iff.mp hd
  rw [ite_eq_right (show d % 2 ≠ 0 by omega)]
  have he : (d - 1) / 2 % 2 = 0 ↔ d % 4 = 1 := by omega
  by_cases h : d % 4 = 1 <;> simp [h, he]

/-- On any computational level over the old one, the homomorphism
identification can be checked on the canonical positive residues.
Taking `χ = (Units.map κ).comp (bCharacter C ∅)` is the input of
`oldStageLaw_of_finiteAction`. -/
theorem oldCharacter_comp_eq_iff {m N M : ℕ} [NeZero m] [NeZero M]
    (h4 : 4 ∣ N) (hm : m ∣ N) {ι : Type*} (s : Finset ι) (c : ι → ℕ) (hc : ∀ i, c i ∣ N)
    (α : ∀ i, (ZMod (c i))ˣ →* ℂˣ) (h3 : m % 4 = 3) (hNM : N ∣ M)
    (χ : (ZMod M)ˣ →* ℂˣ) :
    (oldCharacter h4 hm s c hc α).comp (ZMod.unitsMap hNM) = χ ↔
      ∀ u : (ZMod M)ˣ, (χ u : ℂ) =
        (∏ i ∈ s, (α i (ZMod.unitsMap (dvd_trans (hc i) hNM) u) : ℂ)) *
          (jacobiSym (m : ℤ) (u : ZMod M).val : ℂ) := by
  have he (u : (ZMod M)ˣ) :
      ((oldCharacter h4 hm s c hc α).comp (ZMod.unitsMap hNM) u : ℂ) =
        (∏ i ∈ s, (α i (ZMod.unitsMap (dvd_trans (hc i) hNM) u) : ℂ)) *
          (jacobiSym (m : ℤ) (u : ZMod M).val : ℂ) := by
    have hd : Odd (u : ZMod M).val := by
      have hc2 := (ZMod.val_coe_unit_coprime u).of_dvd_right
        (dvd_trans (by decide : 2 ∣ 4) (dvd_trans h4 hNM))
      apply Nat.odd_iff.mpr
      have hn := Nat.prime_two.coprime_iff_not_dvd.mp hc2.symm
      omega
    have hr : (ZMod.unitsMap hNM u : ZMod N) = ((u : ZMod M).val : ZMod N) := by
      rw [ZMod.unitsMap_val, ← ZMod.cast_natCast hNM (u : ZMod M).val, ZMod.natCast_zmod_val]
    rw [MonoidHom.comp_apply, oldCharacter_natCast h4 hm s c hc α h3 _ hr hd]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact congrArg (fun f : (ZMod M)ˣ →* (ZMod (c i))ˣ => (α i (f u) : ℂ))
      (ZMod.unitsMap_comp (hc i) hNM)
  constructor
  · intro h u
    rw [← h, he]
  · intro h
    ext u
    exact (he u).trans (h u).symm

#print axioms jacobi_prod_right
#print axioms oddFactors_eq_jacobi
#print axioms dyadic_sign
#print axioms oldCharacter_comp_eq_iff
#print axioms jacobi_congr
#print axioms jacobiOn_intCast
#print axioms jacobiOn_unit
#print axioms unitsMap_intCast
#print axioms determinantCharacter_intCast
#print axioms determinant_reciprocity
#print axioms determinantCharacter_natCast
#print axioms determinantCharacter_neg_one
#print axioms oldCharacter_natCast

end ZInQ.Manuscript.RC.WeilIndex
