import ZInQKernel.Contrib.OneProof.PoleS12.NecS12
import ZInQKernel.Contrib.OneProof.PoleS12.Convert

/-!
# The eight classes are local everywhere (S12 L436–454)

ELLIOT (supplement S12, `par:descent`, lines 436–454): `(β, 1)` is an actual local Kummer class
everywhere: "At 2 and at the real place it is the identity class … At 3 it is `τ₁` … At `q_i ∣ l`,
take `u = 1_B` and `v = 0` … At every other finite odd prime it is unramified, so lies in the local
image". The other candidates `(3^σ c, (−ℓ)^σ)`, `c ∈ {1, ℓ, β, ℓ/β}`, are products of `(β, 1)` with
torsion classes.

Here each candidate is shown to be, at `2`, at `3` and at each `q ∣ ℓ`, the class of a torsion
point times squares (`locM_cand`); at the real place `localReal` applies; at a prime of good
reduction the hypothesis `LocalGoodUnram` (unramified classes are local) is used.
-/

namespace ZInQ.Manuscript.PoleS12

open Matrix ZInQ.RouteK.Selmer ZInQ.Manuscript.PoleRC

/-! ### `LocM` on square classes, and the torsion classes -/

section Field

variable {K : Type*} [Field K]

theorem locM_congr {ℓ a b a' b' : K} (ha : SqEq a' a) (hb : SqEq b' b) (h : LocM K ℓ a b) :
    LocM K ℓ a' b' := by
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  rcases h with ⟨⟨r, hr⟩, ⟨w, hw⟩⟩ | ⟨x, h1, h2, h3⟩
  · exact Or.inl ⟨⟨r * s, by rw [hr]; ring⟩, ⟨w * t, by rw [hw]; ring⟩⟩
  · refine Or.inr ⟨x, ?_, ?_, ?_⟩
    · rw [← div_div, isSquare_div_sq_iff hs]; exact h1
    · rw [← div_div, isSquare_div_sq_iff ht]; exact h2
    · rw [show a * s ^ 2 * (b * t ^ 2) = a * b * (s * t) ^ 2 by ring, ← div_div,
        isSquare_div_sq_iff (mul_ne_zero hs ht)]
      exact h3

theorem locM_one_one (ℓ : K) : LocM K ℓ 1 1 := Or.inl ⟨⟨1, by ring⟩, ⟨1, by ring⟩⟩

/-- The class of `(ℓ, 0)`: `(ℓ, 1)` (S12 L320). -/
theorem locM_ell_one {ℓ : K} (hℓ : ℓ ≠ 0) : LocM K ℓ ℓ 1 :=
  Or.inr ⟨ℓ, ⟨2, by field_simp; ring⟩, ⟨0, by ring⟩, ⟨1, by field_simp⟩⟩

/-- The class of `(0, 0)`: `(3ℓ, −ℓ)`. -/
theorem locM_threeEll {ℓ : K} (hℓ : ℓ ≠ 0) (h3 : (3 : K) ≠ 0) : LocM K ℓ (3 * ℓ) (-ℓ) :=
  Or.inr ⟨0, ⟨1, by field_simp; ring⟩, ⟨1, by field_simp; ring⟩, ⟨0, by ring⟩⟩

/-- The class of `(−3ℓ, 0)`: `(3, −ℓ)` (S12 L320). -/
theorem locM_three {ℓ : K} (hℓ : ℓ ≠ 0) (h3 : (3 : K) ≠ 0) : LocM K ℓ 3 (-ℓ) :=
  Or.inr ⟨-3 * ℓ, ⟨0, by ring⟩, ⟨2, by field_simp; ring⟩, ⟨1, by field_simp⟩⟩

/-- **A candidate `(3^σ c, (−ℓ)^σ)` with `c ≡ 1` or `c ≡ ℓ` modulo squares is a torsion class.** -/
theorem locM_cand {ℓ c : K} (hℓ : ℓ ≠ 0) (h3 : (3 : K) ≠ 0) (hc : SqEq c 1 ∨ SqEq c ℓ)
    (σ : Bool) : LocM K ℓ ((if σ then 3 else 1) * c) (if σ then -ℓ else 1) := by
  cases σ with
  | false =>
    simp only [Bool.false_eq_true, if_false, one_mul]
    rcases hc with hc | hc
    · exact locM_congr hc (SqEq.refl 1) (locM_one_one ℓ)
    · exact locM_congr hc (SqEq.refl 1) (locM_ell_one hℓ)
  | true =>
    simp only [if_true]
    rcases hc with hc | hc
    · exact locM_congr (by simpa using (SqEq.refl (3 : K)).mul hc) (SqEq.refl _)
        (locM_three hℓ h3)
    · exact locM_congr ((SqEq.refl (3 : K)).mul hc) (SqEq.refl _) (locM_threeEll hℓ h3)

end Field

/-! ### The square class of `c ∣ ℓ` with `K 1_c = 0` at a prime of `ℓ` -/

theorem filter_dvd_eq {ℓ c : ℕ} (hsf : Squarefree ℓ) (hcl : c ∣ ℓ) :
    ℓ.primeFactors.filter (fun k => k ∣ c) = c.primeFactors := by
  have hc0 : c ≠ 0 := fun h => hsf.ne_zero (zero_dvd_iff.mp (h ▸ hcl))
  ext k
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  exact ⟨fun ⟨⟨hk, _, _⟩, hkc⟩ => ⟨hk, hkc, hc0⟩, fun ⟨hk, hkc, _⟩ =>
    ⟨⟨hk, hkc.trans hcl, hsf.ne_zero⟩, hkc⟩⟩

theorem filter_not_dvd_eq {ℓ c : ℕ} (hsf : Squarefree ℓ) (hcl : c ∣ ℓ) :
    ℓ.primeFactors.filter (fun k => ¬ k ∣ c) = (ℓ / c).primeFactors := by
  have hℓ0 := hsf.ne_zero
  have heq : ℓ = c * (ℓ / c) := (Nat.mul_div_cancel' hcl).symm
  have hd0 : ℓ / c ≠ 0 := by intro h; rw [h, mul_zero] at heq; exact hℓ0 heq
  have hcop : Nat.Coprime c (ℓ / c) := (Nat.squarefree_mul_iff.mp (heq ▸ hsf)).1
  ext k
  simp only [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hk, hkl, _⟩, hkc⟩
    refine ⟨hk, ?_, hd0⟩
    rw [heq] at hkl
    exact (hk.dvd_mul.mp hkl).resolve_left hkc
  · rintro ⟨hk, hkd, _⟩
    refine ⟨⟨hk, hkd.trans (Nat.div_dvd_of_dvd hcl), hℓ0⟩, fun hkc => ?_⟩
    exact hk.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hkc hcop).eq_one_of_dvd hkd)

theorem isSquare_of_lsym_zero {a : ℤ} {q : ℕ} (h : lsym a q = 0) : IsSquare (a : ZMod q) := by
  unfold lsym at h
  split_ifs at h with h'
  · exact h'
  · exact absurd h one_ne_zero

theorem sqEq_of_eq_mul_sq {K : Type*} [Field K] {u x y : K} (h : u = x * y) (hy : y ≠ 0)
    (hsq : IsSquare y) : SqEq u x := by
  obtain ⟨r, rfl⟩ := hsq
  have hr : r ≠ 0 := by rintro rfl; exact hy (mul_zero 0)
  exact ⟨r, hr, by rw [h]; ring⟩

/-- **The square class at a prime `q ∣ ℓ` of a divisor `c` with `K 1_c = 0`** (S12 L444–446,
for `c = β`): `c ≡ 1` if `q ∤ c` (`[c/q] = (K1_c)_q = 0`) and `c ≡ ℓ` if `q ∣ c`
(`[(ℓ/c)/q] = (K1_c)_q = 0`). -/
theorem sqClass_at_bad {ℓ : ℕ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {c : ℕ} (hcl : c ∣ ℓ)
    (hK : Kmat ℓ *ᵥ ind ℓ (c : ℤ) = 0) (i : Supp ℓ) :
    haveI := Fact.mk (supp_prime i)
    SqEq ((c : ℤ) : ℚ_[(i : ℕ)]) 1 ∨ SqEq ((c : ℤ) : ℚ_[(i : ℕ)]) ((ℓ : ℕ) : ℚ_[(i : ℕ)]) := by
  classical
  have hq := Fact.mk (supp_prime i)
  set q : ℕ := (i : ℕ) with hqdef
  have hq2 : q ≠ 2 := by have := supp_mod_two (ℓ := ℓ) (by omega) i; omega
  have hc0 : c ≠ 0 := fun h => hsf.ne_zero (zero_dvd_iff.mp (h ▸ hcl))
  have hrow := congrFun hK i
  rw [kmat_mulVec_eq, Pi.zero_apply] at hrow
  have hext : ∀ k ∈ ℓ.primeFactors, extV (ind ℓ (c : ℤ)) k = if k ∣ c then 1 else 0 := by
    intro k hk
    simp only [extV, dif_pos hk, ind_natCast_of_dvd hc0]
  rw [KS_congr hext i.2, KS] at hrow
  -- add the vanishing `k = q` term
  have hfull : ∑ k ∈ ℓ.primeFactors, lsymS k q *
      ((if k ∣ c then (1 : ZMod 2) else 0) + (if q ∣ c then 1 else 0)) = 0 := by
    rw [← Finset.add_sum_erase _ _ i.2, hrow, add_zero, z2_add_self, mul_zero]
  have hqℓ : q ∣ ℓ := supp_dvd i
  by_cases hqc : q ∣ c
  · right
    set d := ℓ / c with hd
    have heq : ℓ = c * d := (Nat.mul_div_cancel' hcl).symm
    have hqd : ¬ q ∣ d := by
      intro h
      have hcop : Nat.Coprime c d := (Nat.squarefree_mul_iff.mp (heq ▸ hsf)).1
      exact (supp_prime i).one_lt.ne' ((Nat.Coprime.coprime_dvd_left hqc hcop).eq_one_of_dvd h)
    have hs : ∑ k ∈ ℓ.primeFactors, lsymS k q *
        ((if k ∣ c then (1 : ZMod 2) else 0) + (if q ∣ c then 1 else 0)) =
        ∑ k ∈ ℓ.primeFactors.filter (fun k => ¬ k ∣ c), lsymS k q := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_pos hqc]
      split_ifs <;> simp [z2_add_self]
    rw [hs, filter_not_dvd_eq hsf hcl] at hfull
    simp only [lsymS] at hfull
    rw [sum_lsym_primeFactors q d (Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hcl) hsf)
      hqd] at hfull
    have hsq := isSquare_intCast_of_residue hq2 (c := (d : ℤ))
      (fun h => hqd (by exact_mod_cast h)) (isSquare_of_lsym_zero hfull)
    have hd0 : ((d : ℤ) : ℚ_[q]) ≠ 0 := by
      have : d ≠ 0 := fun h => hsf.ne_zero (by rw [heq, h, mul_zero])
      exact_mod_cast this
    refine (sqEq_of_eq_mul_sq (x := ((c : ℤ) : ℚ_[q])) ?_ hd0 hsq).symm
    have := congrArg (fun n : ℕ => (n : ℚ_[q])) heq
    rw [this]; push_cast; ring
  · left
    have hs : ∑ k ∈ ℓ.primeFactors, lsymS k q *
        ((if k ∣ c then (1 : ZMod 2) else 0) + (if q ∣ c then 1 else 0)) =
        ∑ k ∈ ℓ.primeFactors.filter (fun k => k ∣ c), lsymS k q := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [if_neg hqc]
      split_ifs <;> simp
    rw [hs, filter_dvd_eq hsf hcl] at hfull
    simp only [lsymS] at hfull
    rw [sum_lsym_primeFactors q c (Squarefree.squarefree_of_dvd hcl hsf) hqc] at hfull
    have hsq := isSquare_intCast_of_residue hq2 (c := (c : ℤ))
      (fun h => hqc (by exact_mod_cast h)) (isSquare_of_lsym_zero hfull)
    exact sqEq_one_of_isSquare (by exact_mod_cast hc0) hsq

/-- **The square class at `3` of an integer prime to `3`**, for `ℓ ≡ 2 (mod 3)`: `c ≡ 1` or
`c ≡ ℓ` (the units of `ℚ₃` modulo squares are `{1, ℓ}`; S12 L361–363). -/
theorem sqClass_three {ℓ : ℕ} (hℓ3 : ℓ % 3 = 2) {c : ℤ} (hc : c % 3 ≠ 0) :
    SqEq (c : ℚ_[3]) 1 ∨ SqEq (c : ℚ_[3]) ((ℓ : ℕ) : ℚ_[3]) := by
  have hc0 : (c : ℚ_[3]) ≠ 0 := Int.cast_ne_zero.mpr (by rintro rfl; simp at hc)
  have hc3 : c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hc3 with h1 | h2
  · left
    refine sqEq_one_of_isSquare hc0 (isSquare_intCast_of_residue (p := 3) (by norm_num)
      (by intro h; push_cast at h; omega) ⟨1, ?_⟩)
    have h1' : c % ((3 : ℕ) : ℤ) = 1 := by simpa using h1
    rw [← ZMod.intCast_mod, h1']; rfl
  · right
    have hℓ0 : ((ℓ : ℕ) : ℚ_[3]) ≠ 0 := by
      have : ℓ ≠ 0 := by omega
      exact_mod_cast this
    refine (sqEq_iff_isSquare_mul hc0 hℓ0).mpr ?_
    have hm : (c * ℓ) % 3 = 1 := by
      rw [Int.mul_emod, h2]
      have : (ℓ : ℤ) % 3 = 2 := by omega
      rw [this]; rfl
    have := isSquare_intCast_of_residue (p := 3) (c := c * ℓ) (by norm_num)
      (by intro h; push_cast at h; omega) ⟨1, by
        have hm' : c * ℓ % ((3 : ℕ) : ℤ) = 1 := by simpa using hm
        rw [← ZMod.intCast_mod, hm']; rfl⟩
    push_cast at this
    exact this

/-- **Unramified classes are local at a prime of good reduction** (the "if" half of round 1's
`LocalGood`; S12 L351–355 and L337–345: the image has order four and contains the unramified
subgroup of order four). GLUE; see `GoodUnram.lean` for its status. -/
def LocalGoodUnram : Prop :=
  ∀ (ℓ p : ℕ) [Fact p.Prime] (a b : ℤ), Squarefree ℓ → ¬ p ∣ 6 * ℓ →
    ¬ (p : ℤ) ∣ a → ¬ (p : ℤ) ∣ b → LocM ℚ_[p] ℓ a b

/-- **A candidate `(3^σ c, (−ℓ)^σ)` is in `SelM ℓ`** when `c ∣ ℓ`, `K 1_c = 0` and `c ≡ 1` or
`c ≡ ℓ` in `ℚ₂` (S12 L436–454). -/
theorem cand_mem_S12 (hG : LocalGoodUnram) {ℓ : ℕ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11)
    {c : ℕ} (hcl : c ∣ ℓ) (hK : Kmat ℓ *ᵥ ind ℓ (c : ℤ) = 0)
    (h2 : SqEq ((c : ℤ) : ℚ_[2]) 1 ∨ SqEq ((c : ℤ) : ℚ_[2]) ((ℓ : ℕ) : ℚ_[2])) (σ : Bool) :
    ((if σ then 3 else 1) * (c : ℤ), if σ then -(ℓ : ℤ) else 1) ∈ SelM ℓ := by
  have hℓ : 0 < ℓ := by omega
  have hc0 : c ≠ 0 := fun h => hsf.ne_zero (zero_dvd_iff.mp (h ▸ hcl))
  have hcsf : Squarefree (c : ℤ) := Int.squarefree_natCast.mpr (Squarefree.squarefree_of_dvd hcl hsf)
  have hcpos : (0 : ℤ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc0
  have hcl' : (c : ℤ).natAbs.primeFactors ⊆ ℓ.primeFactors := by
    rw [Int.natAbs_natCast]; exact Nat.primeFactors_mono hcl hsf.ne_zero
  have hsa : Squarefree ((if σ then 3 else 1) * (c : ℤ)) := by
    cases σ
    · simpa using hcsf
    · simpa using squarefree_three_mul h12 hcsf hcl'
  have hsb : Squarefree (if σ then -(ℓ : ℤ) else 1) := by
    cases σ
    · simpa using squarefree_one
    · simp only [if_true]; rw [← Int.squarefree_natAbs]; simpa using hsf
  have hapos : 0 < (if σ then 3 else 1) * (c : ℤ) := by cases σ <;> simp <;> omega
  refine ⟨hsa, hsb, (localReal ℓ _ _ hℓ hsa.ne_zero hsb.ne_zero).mpr hapos, ?_⟩
  intro p hp
  -- the local statement from `locM_cand`
  have hloc : ∀ (hc : SqEq ((c : ℤ) : ℚ_[p]) 1 ∨ SqEq ((c : ℤ) : ℚ_[p]) ((ℓ : ℕ) : ℚ_[p])),
      LocM ℚ_[p] ((ℓ : ℕ) : ℚ_[p]) (((if σ then 3 else 1) * (c : ℤ) : ℤ) : ℚ_[p])
        ((if σ then -(ℓ : ℤ) else 1 : ℤ) : ℚ_[p]) := by
    intro hc
    have hℓ0 : ((ℓ : ℕ) : ℚ_[p]) ≠ 0 := by exact_mod_cast hℓ.ne'
    have key := locM_cand hℓ0 three_ne_zero hc σ
    cases σ <;> simpa using key
  by_cases hp2 : p = 2
  · subst hp2; exact hloc h2
  by_cases hp3 : p = 3
  · subst hp3
    refine hloc (sqClass_three (by omega) ?_)
    intro h
    have : 3 ∈ ℓ.primeFactors := hcl' (Nat.mem_primeFactors.mpr ⟨Nat.prime_three,
      by have := Int.natCast_dvd.mp (Int.dvd_of_emod_eq_zero h); simpa using this, by
        simpa using hc0⟩)
    exact three_not_mem h12 this
  by_cases hpl : p ∣ ℓ
  · exact hloc (sqClass_at_bad hsf h12 hcl hK
      ⟨p, Nat.mem_primeFactors.mpr ⟨hp.out, hpl, hsf.ne_zero⟩⟩)
  · have hnd : ¬ p ∣ 6 * ℓ := fun h => by
      rcases prime_dvd_six_mul hp.out h with h | h | h
      · exact hp2 h
      · exact hp3 h
      · exact hpl h
    refine hG ℓ p _ _ hsf hnd ?_ ?_
    · intro h
      have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
      rcases hp'.dvd_or_dvd h with h | h
      · cases σ
        · simp at h
          exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
        · simp only [if_true] at h
          have : p ∣ 3 := by exact_mod_cast h
          exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp this)
      · exact hpl ((Int.natCast_dvd_natCast.mp h).trans hcl)
    · intro h
      cases σ
      · simp at h
        exact hp.out.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) h)
      · simp only [if_true, dvd_neg] at h
        exact hpl (Int.natCast_dvd_natCast.mp h)

end ZInQ.Manuscript.PoleS12
