import ZInQKernel.Contrib.OneProof.PoleS12.SharpAlg
import ZInQKernel.Contrib.PoleRC.QClass

/-!
# From the support-level linear algebra to `MatrixConditions`

`kmat_mulVec_eq`: the manuscript's matrix `Kmat ℓ` (indexed by the prime support of `ℓ`) acts as
`KS lsymS ℓ.primeFactors` on vectors extended by zero. `matrixConditions_of_KS` turns the
support-level statements into `ZInQ.Manuscript.PoleRC.MatrixConditions`.

Also: the parity of the number of prime factors in a residue class (`card_filter_mod_four`,
`card_filter_mod_three`) and the multiplicativity of the additive Legendre symbol over a product
of primes (`lsym_prod`).
-/

namespace ZInQ.Manuscript.PoleS12

open Finset Matrix ZInQ.Manuscript.PoleRC

/-- The symbol `[k/i]` as a function of two naturals. -/
noncomputable def lsymS (k i : ℕ) : ZMod 2 := lsym (k : ℤ) i

open Classical in
/-- A vector on the prime support of `ℓ`, extended by `0`. -/
noncomputable def extV {ℓ : ℕ} (v : Supp ℓ → ZMod 2) (k : ℕ) : ZMod 2 :=
  if h : k ∈ ℓ.primeFactors then v ⟨k, h⟩ else 0

theorem sum_erase_supp {ℓ : ℕ} (i : Supp ℓ) (f : ℕ → ZMod 2) :
    ∑ k ∈ ℓ.primeFactors.erase i, f k = ∑ j ∈ (univ : Finset (Supp ℓ)).erase i, f j := by
  classical
  rw [sum_erase_eq_sub i.2, sum_erase_eq_sub (mem_univ i)]
  congr 1
  exact (sum_coe_sort ℓ.primeFactors f).symm

theorem kmat_mulVec_eq {ℓ : ℕ} (v : Supp ℓ → ZMod 2) (i : Supp ℓ) :
    (Kmat ℓ *ᵥ v) i = KS lsymS ℓ.primeFactors (extV v) i := by
  classical
  have hext : ∀ j : Supp ℓ, extV v j = v j := fun j => by simp [extV, j.2]
  rw [KS, sum_erase_supp i (fun k => lsymS k i * (extV v k + extV v i))]
  simp only [hext]
  rw [mulVec, dotProduct, ← add_sum_erase _ _ (mem_univ i)]
  have h1 : Kmat ℓ i i = ∑ k ∈ (univ : Finset (Supp ℓ)).erase i, lsym ((k : ℕ) : ℤ) i := by
    simp [Kmat]
  have h2 : ∀ j ∈ (univ : Finset (Supp ℓ)).erase i, Kmat ℓ i j = lsym ((j : ℕ) : ℤ) i := by
    intro j hj
    simp [Kmat, Ne.symm (ne_of_mem_erase hj)]
  rw [h1, sum_congr rfl fun j hj =>
    show Kmat ℓ i j * v j = lsym ((j : ℕ) : ℤ) i * v j by rw [h2 j hj]]
  simp only [mul_add, sum_add_distrib, ← sum_mul, lsymS]
  ring

theorem extV_one {ℓ : ℕ} {k : ℕ} (hk : k ∈ ℓ.primeFactors) :
    extV (1 : Supp ℓ → ZMod 2) k = 1 := by simp [extV, hk]

/-- **`MatrixConditions` from the support-level statements.** -/
theorem matrixConditions_of_KS {ℓ β : ℕ}
    (hB0 : ∃ i ∈ ℓ.primeFactors, i ∣ β) (hB1 : ∃ i ∈ ℓ.primeFactors, ¬ i ∣ β)
    (hKb : ∀ i ∈ ℓ.primeFactors, KS lsymS ℓ.primeFactors (fun k => if k ∣ β then 1 else 0) i = 0)
    (hK : ∀ x : ℕ → ZMod 2, (∀ i ∈ ℓ.primeFactors, KS lsymS ℓ.primeFactors x i = 0) →
      ∃ c e : ZMod 2, ∀ i ∈ ℓ.primeFactors, x i = c + e * (if i ∣ β then 1 else 0))
    (hlam : ¬ ∃ x : ℕ → ZMod 2, ∀ i ∈ ℓ.primeFactors, KS lsymS ℓ.primeFactors x i = lsym 3 i) :
    MatrixConditions ℓ β := by
  classical
  have hextB : ∀ k ∈ ℓ.primeFactors, extV (oneB ℓ β) k = if k ∣ β then 1 else 0 := by
    intro k hk; simp [extV, hk, oneB]
  refine ⟨fun h => ?_, fun h => ?_, ?_, fun v hv => ?_, fun u hu => ?_⟩
  · obtain ⟨i, hi, hiβ⟩ := hB0
    have := congrFun h ⟨i, hi⟩
    simp [oneB, hiβ] at this
  · obtain ⟨i, hi, hiβ⟩ := hB1
    have := congrFun h ⟨i, hi⟩
    simp [oneB, hiβ] at this
  · funext i
    rw [kmat_mulVec_eq, KS_congr hextB i.2]
    exact hKb i i.2
  · obtain ⟨c, e, hce⟩ := hK (extV v) fun i hi => by
      have := congrFun hv ⟨i, hi⟩
      rwa [kmat_mulVec_eq] at this
    have hv' : v = (fun _ => c) + e • oneB ℓ β := by
      funext j
      have := hce j j.2
      simp only [extV, j.2, dif_pos] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, oneB, this]
    rcases z2_cases c with rfl | rfl <;> rcases z2_cases e with rfl | rfl
    · left; rw [hv']; funext j; simp
    · right; right; left; rw [hv']; funext j; simp
    · right; left; rw [hv']; funext j; simp
    · right; right; right; rw [hv']; funext j; simp
  · exact hlam ⟨extV u, fun i hi => by
      have := congrFun hu ⟨i, hi⟩
      rwa [kmat_mulVec_eq] at this⟩

/-! ### Parities of prime factors in residue classes, and `lsym` of products -/

/-- For squarefree odd `m`, `m ≡ (−1)^{#{q ∣ m : q ≡ 3 (4)}} (mod 4)`. -/
theorem zmod4_eq_pow (m : ℕ) (hsf : Squarefree m) (h2 : m % 2 = 1) :
    (m : ZMod 4) = (-1) ^ (m.primeFactors.filter (fun q => q % 4 = 3)).card := by
  have hprod : ∏ q ∈ m.primeFactors, q = m := Nat.prod_primeFactors_of_squarefree hsf
  have hq : ∀ q ∈ m.primeFactors, (q : ZMod 4) = if q % 4 = 3 then -1 else 1 := by
    intro q hq
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have hq2 : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h
      · rw [h] at hqd; omega
      · exact h
    rw [← ZMod.natCast_mod q 4]
    have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  conv_lhs => rw [← hprod]
  push_cast
  rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]

/-- For squarefree `m` prime to `3`, `m ≡ (−1)^{#{q ∣ m : q ≡ 2 (3)}} (mod 3)`. -/
theorem zmod3_eq_pow (m : ℕ) (hsf : Squarefree m) (h3 : m % 3 ≠ 0) :
    (m : ZMod 3) = (-1) ^ (m.primeFactors.filter (fun q => q % 3 = 2)).card := by
  have hprod : ∏ q ∈ m.primeFactors, q = m := Nat.prod_primeFactors_of_squarefree hsf
  have hq : ∀ q ∈ m.primeFactors, (q : ZMod 3) = if q % 3 = 2 then -1 else 1 := by
    intro q hq
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have hq3 : q % 3 ≠ 0 := by
      intro h; have : 3 ∣ m := (Nat.dvd_of_mod_eq_zero h).trans hqd; omega
    rw [← ZMod.natCast_mod q 3]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  conv_lhs => rw [← hprod]
  push_cast
  rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
    Finset.prod_const]

theorem card_mod_two_of_pow {R : Type*} [Ring R] (hR : (-1 : R) ≠ 1) {n : ℕ} {x : R}
    (h : x = (-1) ^ n) : ((n : ZMod 2) = 1 ↔ x = -1) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at h
    rw [h, ZMod.natCast_eq_zero_iff_even.mpr he]
    exact ⟨fun h => absurd h (by decide), fun h => absurd h.symm hR⟩
  · rw [ho.neg_one_pow] at h
    rw [h, ZMod.natCast_eq_one_iff_odd.mpr ho]
    exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem card_mod_two_of_pow' {R : Type*} [Ring R] {n : ℕ} {x : R}
    (h : x = (-1) ^ n) (h1 : x = 1) (hR : (-1 : R) ≠ 1) : (n : ZMod 2) = 0 := by
  rcases Nat.even_or_odd n with he | ho
  · exact ZMod.natCast_eq_zero_iff_even.mpr he
  · rw [ho.neg_one_pow, h1] at h; exact absurd h.symm hR

/-- **`Σ_{q ∣ m} s_q`** is `[m ≡ 3 (mod 4)]` for squarefree odd `m`. -/
theorem sum_sgn_eq (m : ℕ) (hsf : Squarefree m) (h2 : m % 2 = 1) :
    ∑ q ∈ m.primeFactors, lsym (-1) q = if m % 4 = 3 then 1 else 0 := by
  classical
  have hq : ∀ q ∈ m.primeFactors, lsym (-1) q = if q % 4 = 3 then 1 else 0 := by
    intro q hq
    have := Fact.mk (Nat.mem_primeFactors.mp hq).1
    exact lsym_neg_one q
  rw [sum_congr rfl hq, sum_boole]
  have hZ := zmod4_eq_pow m hsf h2
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases hm4 with h | h
  · rw [if_neg (by omega)]
    refine card_mod_two_of_pow' hZ ?_ (by decide)
    rw [← ZMod.natCast_mod m 4, h]; rfl
  · rw [if_pos h]
    refine (card_mod_two_of_pow (by decide) hZ).mpr ?_
    rw [← ZMod.natCast_mod m 4, h]; decide

/-- **`Σ_{q ∣ m} λ_q`** is `[m ≡ 2 (3)] + [m ≡ 3 (4)]` for squarefree `m` prime to `6`. -/
theorem sum_lam_eq (m : ℕ) (hsf : Squarefree m) (h2 : m % 2 = 1) (h3 : m % 3 ≠ 0) :
    ∑ q ∈ m.primeFactors, lsym 3 q =
      (if m % 3 = 2 then 1 else 0) + (if m % 4 = 3 then 1 else 0) := by
  classical
  have hq : ∀ q ∈ m.primeFactors, lsym 3 q =
      (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by
    intro q hq
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have := Fact.mk hqp
    refine lsym_three q ?_ ?_
    · rcases hqp.eq_two_or_odd with h | h
      · rw [h] at hqd; omega
      · exact h
    · rintro rfl; omega
  rw [sum_congr rfl hq, sum_add_distrib, sum_boole, sum_boole]
  congr 1
  · have hZ := zmod3_eq_pow m hsf h3
    have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases hm3 with h | h
    · rw [if_neg (by omega)]
      refine card_mod_two_of_pow' hZ ?_ (by decide)
      rw [← ZMod.natCast_mod m 3, h]; rfl
    · rw [if_pos h]
      refine (card_mod_two_of_pow (by decide) hZ).mpr ?_
      rw [← ZMod.natCast_mod m 3, h]; decide
  · have hZ := zmod4_eq_pow m hsf h2
    have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases hm4 with h | h
    · rw [if_neg (by omega)]
      refine card_mod_two_of_pow' hZ ?_ (by decide)
      rw [← ZMod.natCast_mod m 4, h]; rfl
    · rw [if_pos h]
      refine (card_mod_two_of_pow (by decide) hZ).mpr ?_
      rw [← ZMod.natCast_mod m 4, h]; decide

/-- **`[∏_{k ∈ T} k / q] = Σ_{k ∈ T} [k/q]`** when `q` is prime and divides no `k ∈ T`. -/
theorem lsym_prod (q : ℕ) [Fact q.Prime] (T : Finset ℕ) (hT : ∀ k ∈ T, ¬ q ∣ k) :
    lsym (∏ k ∈ T, (k : ℤ)) q = ∑ k ∈ T, lsym (k : ℤ) q := by
  induction T using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sum_empty]
    exact lsym_of_isSquare ⟨1, by simp⟩
  | insert k T hkT ih =>
    rw [prod_insert hkT, sum_insert hkT]
    have hk : ((k : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hT k (mem_insert_self _ _)
    have hP : ((∏ k ∈ T, (k : ℤ) : ℤ) : ZMod q) ≠ 0 := by
      rw [Int.cast_prod]
      refine prod_ne_zero_iff.mpr fun k' hk' => ?_
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact hT k' (mem_insert_of_mem hk')
    rw [lsym_mul q hk hP, ih fun k' hk' => hT k' (mem_insert_of_mem hk')]

/-- **`Σ_{k ∣ m} [k/q] = [m/q]`** for squarefree `m` and a prime `q ∤ m`. -/
theorem sum_lsym_primeFactors (q : ℕ) [Fact q.Prime] (m : ℕ) (hsf : Squarefree m)
    (hqm : ¬ q ∣ m) : ∑ k ∈ m.primeFactors, lsym (k : ℤ) q = lsym (m : ℤ) q := by
  rw [← lsym_prod q _ fun k hk h => hqm (h.trans (Nat.mem_primeFactors.mp hk).2.1)]
  congr 1
  rw [← Nat.prod_primeFactors_of_squarefree hsf]
  push_cast
  rw [Nat.prod_primeFactors_of_squarefree hsf]

end ZInQ.Manuscript.PoleS12
