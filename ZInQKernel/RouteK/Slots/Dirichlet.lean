import ZInQKernel.RouteK.Slots.Symbols

/-!
# Route K slots: the general slot lemma

`docs/research/slot-k.md` §2.4, "Existence of the slots": a prime in a prescribed odd class
mod 8, with prescribed Legendre symbols `(q/p) = ±1` at finitely many distinct odd primes `p`,
avoiding a finite set. Each symbol condition is a nonempty union of invertible classes mod `p`
(an odd prime has non-residues); the Chinese remainder theorem combines them with the class mod 8,
and Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_zmodEq`) gives a prime in the combined
class, as large as we like.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-- For an odd prime `p` and a sign `ε = ±1` there is a residue `r` prime to `p` with
`(r/p) = ε`. -/
theorem exists_residue_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : ∃ r : ℕ, ¬ p ∣ r ∧ legendreSym p r = ε := by
  rcases hε with rfl | rfl
  · exact ⟨1, (Fact.out : p.Prime).not_dvd_one, by simp [legendreSym.at_one]⟩
  · obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    refine ⟨a.val, fun hd => ha ?_, ?_⟩
    · have : (a.val : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
      rw [ZMod.natCast_zmod_val] at this
      exact ⟨0, by rw [this]; ring⟩
    · exact (legendreSym.eq_neg_one_iff' p).mpr (by rwa [ZMod.natCast_zmod_val])

/-- **Slot lemma** (slot-k §2.4): let `S` be a finite set of odd primes with prescribed signs
`ε p = ±1`, let `a` be odd and `A` finite. There is a prime `q ∉ A`, `q ≡ a (mod 8)`, with
`(q/p) = ε p` for every `p ∈ S`. -/
theorem exists_prime_slot (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (ε : ℕ → ℤ)
    (hε : ∀ p ∈ S, ε p = 1 ∨ ε p = -1) {a : ℤ} (ha : Odd a) (A : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ (q : ℤ) ≡ a [ZMOD 8] ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∈ S → legendreSym p q = ε p := by
  classical
  -- residues mod each `p ∈ S`
  have hr : ∀ p ∈ S, ∃ r : ℕ, ¬ p ∣ r ∧ ∀ _ : Fact p.Prime, legendreSym p r = ε p := by
    intro p hp
    have := Fact.mk (hS p hp).1
    obtain ⟨r, h1, h2⟩ := exists_residue_legendreSym (hS p hp).2 (hε p hp)
    exact ⟨r, h1, fun _ => h2⟩
  choose! r hr1 hr2 using hr
  -- the Chinese remainder theorem, with the modulus `8` attached to the index `2 ∉ S`
  have h2S : 2 ∉ S := fun h => (hS 2 h).2 rfl
  have ha8 : 0 ≤ a % 8 := Int.emod_nonneg a (by norm_num)
  obtain ⟨x, hx⟩ := Nat.chineseRemainderOfFinset (fun i => if i = 2 then (a % 8).toNat else r i)
    (fun i => if i = 2 then 8 else i) (insert 2 S)
    (fun i hi => by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simp
      · simp only [show i ≠ 2 from fun h => h2S (h ▸ hi), ite_false]
        exact (hS i hi).1.ne_zero)
    (fun i hi j hj hij => by
      have key : ∀ i j, i ∈ insert 2 S → j ∈ S → i ≠ j →
          Nat.Coprime (if i = 2 then 8 else i) j := by
        intro i j hi hj hij
        have hjp := (hS j hj).1
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp only [ite_true]
          exact Nat.Coprime.pow_left 3 ((Nat.coprime_primes Nat.prime_two hjp).mpr hij)
        · simp only [show i ≠ 2 from fun h => h2S (h ▸ hi), ite_false]
          exact (Nat.coprime_primes (hS i hi).1 hjp).mpr hij
      rcases Finset.mem_insert.mp hj with rfl | hj
      · have hi' : i ∈ S := (Finset.mem_insert.mp hi).resolve_left hij
        have := key 2 i (Finset.mem_insert_self _ _) hi' (Ne.symm hij)
        simp only [Function.onFun, show i ≠ 2 from hij, ite_false, ite_true] at this ⊢
        exact this.symm
      · have := key i j hi hj hij
        simp only [Function.onFun, show j ≠ 2 from fun h => h2S (h ▸ hj), ite_false] at this ⊢
        exact this)
  have hx8 : x ≡ (a % 8).toNat [MOD 8] := by simpa using hx 2 (Finset.mem_insert_self _ _)
  have hxp : ∀ p ∈ S, x ≡ r p [MOD p] := fun p hp => by
    have := hx p (Finset.mem_insert_of_mem hp)
    simpa [show p ≠ 2 from fun h => h2S (h ▸ hp)] using this
  have hx8' : (x : ℤ) ≡ a [ZMOD 8] := by
    have h1 : ((x : ℕ) : ℤ) ≡ (((a % 8).toNat : ℕ) : ℤ) [ZMOD ((8 : ℕ) : ℤ)] :=
      Int.natCast_modEq_iff.mpr hx8
    rw [Int.toNat_of_nonneg ha8] at h1
    exact h1.trans (Int.mod_modEq a 8)
  -- `x` is prime to `N = 8 ∏ p`
  set N : ℕ := 8 * ∏ p ∈ S, p with hN
  have hcop : Nat.Coprime x N := by
    refine Nat.Coprime.mul_right ?_ (Nat.coprime_prod_right_iff.mpr fun p hp => ?_)
    · refine Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr ?_)
      have h1 : (x : ℤ) % 8 = a % 8 := hx8'
      have h2 : a % 2 = 1 := Int.odd_iff.mp ha
      rw [Nat.odd_iff]; omega
    · refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (hS p hp).1).mpr fun hd => ?_))
      apply hr1 p hp
      have := hxp p hp
      rw [Nat.ModEq, (Nat.dvd_iff_mod_eq_zero).mp hd] at this
      exact Nat.dvd_of_mod_eq_zero this.symm
  have hN0 : N ≠ 0 :=
    mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).1.ne_zero)
  obtain ⟨q, hqA, hq, hqx⟩ := Nat.forall_exists_prime_gt_and_zmodEq (A.sup id) hN0
    (Nat.isCoprime_iff_coprime.mpr hcop)
  refine ⟨q, hq, fun h => absurd (Finset.le_sup (f := id) h) (not_le.mpr hqA), ?_, ?_⟩
  · exact (hqx.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_right 8 _))).trans hx8'
  · intro p _ hp
    have h1 : (q : ℤ) ≡ x [ZMOD p] := hqx.of_dvd (Int.natCast_dvd_natCast.mpr
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) 8))
    have h2 : (q : ℤ) ≡ r p [ZMOD p] := h1.trans (Int.natCast_modEq_iff.mpr (hxp p hp))
    rw [legendreSym.mod, h2, ← legendreSym.mod]
    exact hr2 p hp _

/-- **Slot lemma, bit form**: prescribed bits `[q/p] = b p` at the odd primes `p ∈ S`, a class
`a` mod 8 and a finite set `A` to avoid; the prime `q` is also outside `S`. -/
theorem exists_prime_slot_bits (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (b : ℕ → ZMod 2)
    {a : ℤ} (ha : Odd a) (A : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ A ∧ q ∉ S ∧ (q : ℤ) ≡ a [ZMOD 8] ∧ ∀ p ∈ S, legBit p q = b p := by
  classical
  obtain ⟨q, hq, hqA, hq8, hqS⟩ := exists_prime_slot S hS (fun p => if b p = 0 then 1 else -1)
    (fun p _ => by by_cases h : b p = 0 <;> simp [h]) ha (A ∪ S)
  refine ⟨q, hq, fun h => hqA (Finset.mem_union_left _ h),
    fun h => hqA (Finset.mem_union_right _ h), hq8, fun p hp => ?_⟩
  have := Fact.mk (hS p hp).1
  have hpq : p ≠ q := fun h => hqA (Finset.mem_union_right _ (h ▸ hp))
  exact (legBit_eq_iff_legendreSym (natCast_zmod_ne_zero_of_prime_ne (hS p hp).1 hq hpq) _).mpr
    (hqS p hp)

end ZInQ.RouteK
