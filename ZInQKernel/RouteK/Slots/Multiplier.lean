import ZInQKernel.RouteK.Slots.Basic

/-!
# Route K slots: the multiplier (lemma L1)

`docs/research/slot-k.md` §2.4, step 0: for every admissible `B` (indeed every `B ≠ 0`) there is a
signed divisor `m` of 2730 with `β = sqf(mB)` odd and `|β| ≡ 7 (mod 8)`.

Proof: write `sqf B = 2^f b'` with `b'` odd and take `m = 2^f m₀` with `m₀ ∈ {1, 3, 5, 7}` and
`m₀ |b'| ≡ 7 (mod 8)`. Then `mB ∈ m₀b' · ℚ*²`, and `sqf(m₀b')` is `m₀b'` or `b'/m₀`; both are odd
and `≡ m₀ |b'|` in absolute value mod 8, since odd squares are `≡ 1 (mod 8)`.
-/

namespace ZInQ.RouteK

/-- Multiplying an odd squarefree integer by `1` or by an odd prime `m₀`: the squarefree part of
the product is odd and its absolute value is `≡ m₀ |b| (mod 8)`. -/
theorem sqfInt_mul_odd_prime {m₀ : ℕ} {b : ℤ} (hm : m₀ = 1 ∨ m₀.Prime) (hm2 : Odd m₀)
    (hb : Squarefree b) (hbo : Odd b) :
    Odd (sqfInt (m₀ * b)) ∧ (sqfInt (m₀ * b)).natAbs % 8 = (m₀ * b.natAbs) % 8 := by
  have hm8 : m₀ * m₀ % 8 = 1 := by
    obtain ⟨j, rfl⟩ := hm2
    obtain ⟨i, hi⟩ := Nat.even_mul_succ_self j
    have : (2 * j + 1) * (2 * j + 1) = 4 * (j * (j + 1)) + 1 := by ring
    rw [this, hi]; omega
  have hm0 : (m₀ : ℤ) ≠ 0 := by exact_mod_cast hm2.pos.ne'
  by_cases hd : (m₀ : ℤ) ∣ b
  · obtain ⟨b'', rfl⟩ := hd
    have hb'' : Squarefree b'' := hb.of_mul_right
    rw [sqfInt_eq_of_eq_mul_sq hb'' hm0 (by ring)]
    refine ⟨Int.Odd.of_mul_right hbo, ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_natCast, ← mul_assoc, Nat.mul_mod, hm8, one_mul, Nat.mod_mod]
  · have hprime : m₀.Prime := hm.resolve_left (by rintro rfl; exact hd (by simp))
    have hp : Prime (m₀ : ℤ) := Nat.prime_iff_prime_int.mp hprime
    have hsq : Squarefree ((m₀ : ℤ) * b) :=
      squarefree_mul_iff.mpr ⟨hp.irreducible.isRelPrime_iff_not_dvd.mpr hd, hp.squarefree, hb⟩
    rw [sqfInt_eq_of_eq_mul_sq hsq one_ne_zero (by ring)]
    exact ⟨Odd.mul (by exact_mod_cast hm2) hbo, by rw [Int.natAbs_mul, Int.natAbs_natCast]⟩

/-- **L1** (strong form): for `B ≠ 0` there is a positive divisor `m` of 2730 with `β = sqf(mB)`
odd and `|β| ≡ 7 (mod 8)`. -/
theorem exists_multiplier_pos {B : ℚ} (hB : B ≠ 0) :
    ∃ m : ℤ, 0 < m ∧ m ∣ 2730 ∧ Odd (betaOf B m) ∧ (betaOf B m).natAbs % 8 = 7 := by
  obtain ⟨hs, t, ht, hBt⟩ := sqf_spec hB
  obtain ⟨b, hb⟩ : ∃ b, sqf B = b := ⟨_, rfl⟩
  rw [hb] at hs hBt
  have hβ : ∀ m : ℤ, m ≠ 0 → betaOf B m = sqfInt (m * b) := by
    intro m hm
    rw [betaOf, hBt, show (m : ℚ) * (b * t ^ 2) = ((m * b : ℤ) : ℚ) * t ^ 2 by push_cast; ring,
      sqf_mul_sq (by exact_mod_cast mul_ne_zero hm hs.ne_zero) ht, sqf_intCast]
  -- `b = 2^f b'` with `b'` odd and squarefree
  obtain ⟨f, b', hf, hb'sq, hb'odd, hbb'⟩ :
      ∃ f : ℕ, ∃ b' : ℤ, f ≤ 1 ∧ Squarefree b' ∧ Odd b' ∧ b = 2 ^ f * b' := by
    rcases Int.even_or_odd b with he | ho
    · obtain ⟨b', hb'⟩ := even_iff_two_dvd.mp he
      refine ⟨1, b', le_rfl, (hb' ▸ hs).of_mul_right, ?_, by simp [hb']⟩
      by_contra hne
      obtain ⟨c, hc⟩ := even_iff_two_dvd.mp (Int.not_odd_iff_even.mp hne)
      have := hs 2 ⟨c, by rw [hb', hc]; ring⟩
      rw [Int.isUnit_iff] at this; omega
    · exact ⟨0, b, by norm_num, hs, ho, by simp⟩
  have hc : b'.natAbs % 8 = 1 ∨ b'.natAbs % 8 = 3 ∨ b'.natAbs % 8 = 5 ∨ b'.natAbs % 8 = 7 := by
    have : b'.natAbs % 2 = 1 := Nat.odd_iff.mp (Int.natAbs_odd.mpr hb'odd)
    omega
  have hf' : f = 0 ∨ f = 1 := by omega
  obtain ⟨m₀, hm₀, hm₀o, hm₀8, hm₀d⟩ : ∃ m₀ : ℕ, (m₀ = 1 ∨ m₀.Prime) ∧ Odd m₀ ∧
      (m₀ * b'.natAbs) % 8 = 7 ∧ (2 : ℤ) ^ f * m₀ ∣ 2730 := by
    rcases hc with h | h | h | h
    · exact ⟨7, Or.inr (by norm_num), by decide, by rw [Nat.mul_mod, h],
        by rcases hf' with rfl | rfl <;> decide⟩
    · exact ⟨5, Or.inr (by norm_num), by decide, by rw [Nat.mul_mod, h],
        by rcases hf' with rfl | rfl <;> decide⟩
    · exact ⟨3, Or.inr (by norm_num), by decide, by rw [Nat.mul_mod, h],
        by rcases hf' with rfl | rfl <;> decide⟩
    · exact ⟨1, Or.inl rfl, by decide, by rw [Nat.mul_mod, h],
        by rcases hf' with rfl | rfl <;> decide⟩
  have hm0 : (2 : ℤ) ^ f * m₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast hm₀o.pos.ne')
  refine ⟨2 ^ f * m₀, by positivity, hm₀d, ?_⟩
  have hm0b : (m₀ : ℤ) * b' ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm₀o.pos.ne') hb'sq.ne_zero
  rw [hβ _ hm0, show (2 ^ f * m₀ : ℤ) * b = (m₀ * b') * (2 ^ f) ^ 2 by rw [hbb']; ring,
    sqfInt_mul_sq hm0b (pow_ne_zero _ two_ne_zero)]
  obtain ⟨h1, h2⟩ := sqfInt_mul_odd_prime hm₀ hm₀o hb'sq hb'odd
  exact ⟨h1, h2.trans hm₀8⟩

/-- **L1** (slot-k §2.4, step 0; §4.2): for every admissible `B` there is a signed divisor `m` of
2730 such that `β = sqf(mB)` is odd and `|β| ≡ 7 (mod 8)`. -/
theorem exists_multiplier {B : ℚ} (hB : Admissible B) :
    ∃ m : ℤ, m ∣ 2730 ∧ Odd (betaOf B m) ∧ (betaOf B m).natAbs % 8 = 7 := by
  obtain ⟨m, -, h⟩ := exists_multiplier_pos hB.ne_zero
  exact ⟨m, h⟩

end ZInQ.RouteK
