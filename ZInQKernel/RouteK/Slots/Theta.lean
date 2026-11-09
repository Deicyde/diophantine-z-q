import ZInQKernel.RouteK.Slots.Basic
import ZInQKernel.Multiplication.Certificate.Parity

/-!
# Route K slots: the properties (θ1)–(θ4) (lemma L2)

`docs/research/slot-k.md` §1.1. For an admissible `B` and a signed divisor `m` of 2730 let
`β = sqf(mB)` and `θ = sqf(m(m - B))`. Then

- (θ1) `θ > 0`, `θ ≡ 1 (mod 8)`, `gcd(θ, 2730) = 1`;
- (θ2) `β` and `θ` have disjoint supports;
- (θ3) `(β/ℓ) = 1` for every prime `ℓ ∣ θ`;
- (θ4) `(θ/p) = 1` for every odd prime `p ∣ β`.

We work with integers: with `B = a/k²` in lowest terms and `M = mk`, `ma = βs²` and
`θc² = M² - ma` (`betaOf_thetaOf_eq_sqfInt`). This is the note's `θc'² = 1 - βt'²` multiplied by
`M²`. The local analysis at a prime `p` is `local_unit_square`: if `p^(2v_p(M)+1) ∣ ma` then `p ∤ θ`
and `θ` is a nonzero square mod `p` (mod `8` when `p = 2`).
-/

namespace ZInQ.RouteK

/-- Odd squares are `≡ 1 (mod 8)`. -/
theorem int_sq_modEq_one_of_odd {x : ℤ} (hx : Odd x) : x ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨i, hi⟩ := Int.even_mul_succ_self y
  have : (2 * y + 1) ^ 2 = 4 * (y * (y + 1)) + 1 := by ring
  rw [this, hi, Int.ModEq]
  omega

/-- The local computation behind (θ1)–(θ4). If `θ c² = (p^e M₁)² - X` with `θ` squarefree,
`p ∤ M₁` and `p^(2e+j) ∣ X` for some `j ≥ 1`, then `p ∤ θ`, and `θ c₁² ≡ M₁² (mod p^j)` for some
`c₁` prime to `p`. -/
theorem local_unit_square {p : ℕ} (hp : p.Prime) {θ c M₁ X : ℤ} {e j : ℕ} (hj : 1 ≤ j)
    (hθ : Squarefree θ) (hM₁ : ¬ (p : ℤ) ∣ M₁) (hX : (p : ℤ) ^ (2 * e + j) ∣ X)
    (h : θ * c ^ 2 = ((p : ℤ) ^ e * M₁) ^ 2 - X) :
    ¬ (p : ℤ) ∣ θ ∧ ∃ c₁ : ℤ, ¬ (p : ℤ) ∣ c₁ ∧ θ * c₁ ^ 2 ≡ M₁ ^ 2 [ZMOD (p : ℤ) ^ j] := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨X₁, rfl⟩ := hX
  obtain ⟨N₁, hN₁⟩ : ∃ N₁, N₁ = M₁ ^ 2 - (p : ℤ) ^ j * X₁ := ⟨_, rfl⟩
  have hN₁p : ¬ (p : ℤ) ∣ N₁ := by
    intro hd
    apply hM₁
    apply hpZ.dvd_of_dvd_pow (n := 2)
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ j * X₁ := dvd_mul_of_dvd_left (dvd_pow_self _ (by omega)) _
    have := dvd_add hd h1
    rwa [hN₁, sub_add_cancel] at this
  have hpow0 : ∀ n : ℕ, ((p : ℤ) ^ n) ≠ 0 := fun n => pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have h' : θ * c ^ 2 = (p : ℤ) ^ (2 * e) * N₁ := by rw [h, hN₁]; ring
  have hc : c ≠ 0 := by
    rintro rfl
    have : (p : ℤ) ^ (2 * e) * N₁ = 0 := by rw [← h']; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hpow0 _ h0
    · exact hN₁p (h0 ▸ dvd_zero _)
  -- `c = p^u c₁` with `p ∤ c₁`
  obtain ⟨u, c₁, hc₁, hcu⟩ : ∃ u : ℕ, ∃ c₁ : ℤ, ¬ (p : ℤ) ∣ c₁ ∧ c = (p : ℤ) ^ u * c₁ := by
    obtain ⟨u, n, hn, hcn⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hc) p hp.ne_one
    refine ⟨u, c.sign * n, fun hd => hn ?_, ?_⟩
    · have := Int.natAbs_dvd_natAbs.mpr hd
      rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hc, one_mul, Int.natAbs_natCast,
        Int.natAbs_natCast] at this
    · conv_lhs => rw [← Int.sign_mul_natAbs c, hcn]
      push_cast; ring
  have hθc : θ * c₁ ^ 2 * (p : ℤ) ^ (2 * u) = (p : ℤ) ^ (2 * e) * N₁ := by rw [← h', hcu]; ring
  rcases lt_trichotomy u e with hue | rfl | hue
  · -- `u < e`: then `p² ∣ θ`
    exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hue
    have h2 : θ * c₁ ^ 2 = (p : ℤ) ^ 2 * ((p : ℤ) ^ (2 * d) * N₁) := by
      apply mul_right_cancel₀ (hpow0 (2 * u)); rw [hθc]; ring
    have hcop : IsCoprime ((p : ℤ) ^ 2) (c₁ ^ 2) :=
      ((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hc₁).pow
    have hdvd : (p : ℤ) * p ∣ θ := by
      rw [← sq]; exact hcop.dvd_of_dvd_mul_right ⟨_, h2⟩
    exact hpZ.not_isUnit (hθ _ hdvd)
  · -- `u = e`
    have h2 : θ * c₁ ^ 2 = N₁ := by apply mul_right_cancel₀ (hpow0 (2 * u)); rw [hθc]; ring
    refine ⟨fun hd => hN₁p (h2 ▸ dvd_mul_of_dvd_left hd _), c₁, hc₁, ?_⟩
    rw [h2, hN₁]
    exact Int.modEq_iff_dvd.mpr ⟨X₁, by ring⟩
  · -- `u > e`: then `p ∣ N₁`
    exfalso
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hue
    have h2 : θ * c₁ ^ 2 * (p : ℤ) ^ (2 * d + 2) = N₁ := by
      apply mul_left_cancel₀ (hpow0 (2 * e)); rw [← hθc]; ring
    exact hN₁p ⟨θ * c₁ ^ 2 * (p : ℤ) ^ (2 * d + 1), by rw [← h2]; ring⟩

/-- If `θ c₁² ≡ M₁² (mod p)` with `p ∤ c₁ M₁`, then `(θ/p) = 1`. -/
theorem legendreSym_eq_one_of_modEq {p : ℕ} [Fact p.Prime] {θ c₁ M₁ : ℤ} (hc₁ : ¬ (p : ℤ) ∣ c₁)
    (hM₁ : ¬ (p : ℤ) ∣ M₁) (h : θ * c₁ ^ 2 ≡ M₁ ^ 2 [ZMOD p]) : legendreSym p θ = 1 := by
  have h' := (ZMod.intCast_eq_intCast_iff _ _ p).mpr h
  push_cast at h'
  have hc : (c₁ : ZMod p) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c₁ p).not.mpr hc₁
  have hM : (M₁ : ZMod p) ≠ 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd M₁ p).not.mpr hM₁
  have hθ : (θ : ZMod p) = (M₁ / c₁ : ZMod p) * (M₁ / c₁ : ZMod p) := by
    field_simp; rw [← h']
  have hθ0 : (θ : ZMod p) ≠ 0 := by
    rw [hθ]; exact mul_ne_zero (div_ne_zero hM hc) (div_ne_zero hM hc)
  exact (legendreSym.eq_one_iff p hθ0).mpr ⟨_, hθ⟩

/-- A prime dividing a divisor `m` of 2730 lies in `S₀`, and `p² ∤ m`. -/
theorem prime_dvd_divisor_2730 {m : ℤ} (hm : m ∣ 2730) {p : ℕ} (hp : p.Prime)
    (hpm : (p : ℤ) ∣ m) : p ∈ poleS0 ∧ ¬ (p : ℤ) ^ 2 ∣ m := by
  have hS : p ∈ poleS0 := by
    by_contra hS
    exact Mult.not_dvd_2730_of_not_mem_poleS0 hp hS (Int.natCast_dvd_natCast.mp (hpm.trans hm))
  refine ⟨hS, fun h2 => ?_⟩
  have h2' := h2.trans hm
  simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl <;> revert h2' <;> decide

/-- Decoding admissibility: `B = a/k²` in lowest terms with `0 < 2a < k²`, and for `p ∈ S₀`,
`p ∤ k` and `p⁴ ∣ a`. -/
theorem Admissible.decode {B : ℚ} (hB : Admissible B) :
    ∃ k : ℕ, B.den = k ^ 2 ∧ 0 < B.num ∧ 2 * B.num < (k : ℤ) ^ 2 ∧ IsCoprime B.num k ∧
      ∀ p ∈ poleS0, ¬ (p : ℤ) ∣ k ∧ (p : ℤ) ^ 4 ∣ B.num := by
  obtain ⟨⟨r, hr⟩, hpos, hlt, hval⟩ := hB
  have hnum : 0 < B.num := Rat.num_pos.mpr hpos
  have hden : ((B.den : ℕ) : ℤ) = (r : ℤ) ^ 2 := by rw [hr]; push_cast; ring
  have hcop : Nat.Coprime B.num.natAbs r :=
    Nat.Coprime.coprime_dvd_right (by rw [hr]; exact dvd_mul_right r r) B.reduced
  refine ⟨r, by rw [hr, sq], hnum, ?_, ?_, ?_⟩
  · have h1 : (B.num : ℚ) / B.den < 1 / 2 := by rwa [Rat.num_div_den]
    have hd : (0 : ℚ) < B.den := by exact_mod_cast B.den_pos
    rw [div_lt_div_iff₀ hd (by norm_num)] at h1
    have h2 : B.num * 2 < (B.den : ℤ) := by exact_mod_cast (by linarith : (B.num : ℚ) * 2 < B.den)
    rw [hden] at h2; linarith
  · rw [← Int.natAbs_of_nonneg hnum.le]
    exact Nat.isCoprime_iff_coprime.mpr hcop
  · intro p hp
    have hpp : p.Prime := by
      simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have := Fact.mk hpp
    have hv := hval p hp
    rw [padicValRat] at hv
    have hpr : ¬ p ∣ r := by
      intro hd
      have hdd : p ∣ B.den := by rw [hr]; exact dvd_mul_of_dvd_left hd r
      have h1 := one_le_padicValNat_of_dvd B.den_ne_zero hdd
      have hpn : ¬ (p : ℤ) ∣ B.num := by
        intro hn
        have := Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (Int.natCast_dvd.mp hn) hd : p ∣ 1)
        exact hpp.ne_one this
      rw [padicValInt.eq_zero_of_not_dvd hpn] at hv
      omega
    refine ⟨fun hd => hpr (Int.natCast_dvd_natCast.mp hd), ?_⟩
    have h0 : padicValNat p B.den = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      rw [hr]; intro hd
      rcases (Nat.Prime.dvd_mul hpp).mp hd with h | h <;> exact hpr h
    rw [h0] at hv
    exact (padicValInt_dvd_iff 4 B.num).mpr (Or.inr (by omega))

/-- The integer data of `β` and `θ` (see the module docstring). -/
theorem slot_setup {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) :
    ∃ (k : ℕ) (a s c : ℤ), 0 < a ∧ 2 * a < (k : ℤ) ^ 2 ∧ IsCoprime a k ∧
      (∀ p ∈ poleS0, ¬ (p : ℤ) ∣ k ∧ (p : ℤ) ^ 4 ∣ a) ∧ m ≠ 0 ∧ s ≠ 0 ∧ c ≠ 0 ∧
      0 < (m * k) ^ 2 - m * a ∧
      Squarefree (betaOf B m) ∧ Squarefree (thetaOf B m) ∧
      m * a = betaOf B m * s ^ 2 ∧ thetaOf B m * c ^ 2 = (m * k) ^ 2 - m * a := by
  obtain ⟨k, hk, ha, hak, hcop, hS0⟩ := hB.decode
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm
  have hmB : (m : ℚ) ≠ B := by
    intro h
    have h1 : (0 : ℚ) < m := h ▸ hB.pos
    have h2 : (m : ℚ) < 1 / 2 := h ▸ hB.2.2.1
    have h3 : (0 : ℤ) < m := by exact_mod_cast h1
    have h4 : (m : ℚ) < 1 := by linarith
    have h5 : m < 1 := by exact_mod_cast h4
    omega
  obtain ⟨hβ, hθ⟩ := betaOf_thetaOf_eq_sqfInt hk hm0 hB.ne_zero hmB
  have hpos : 0 < (m * k) ^ 2 - m * B.num := by
    have h1 : m * B.num ≤ m ^ 2 * B.num := by
      have : m ≤ m ^ 2 := by nlinarith [sq_nonneg (m - 1)]
      nlinarith
    have h2 : m ^ 2 * B.num < m ^ 2 * (k : ℤ) ^ 2 := by
      have : 0 < m ^ 2 := by positivity
      nlinarith
    nlinarith
  obtain ⟨hβs, s, hs, hs'⟩ := sqfInt_spec (mul_ne_zero hm0 ha.ne')
  obtain ⟨hθs, c, hc, hc'⟩ := sqfInt_spec hpos.ne'
  rw [← hβ] at hβs hs'
  rw [← hθ] at hθs hc'
  exact ⟨k, B.num, s, c, ha, hak, hcop, hS0, hm0, hs, hc, hpos, hβs, hθs, hs', hc'.symm⟩

theorem prime_of_mem_poleS0' {p : ℕ} (hp : p ∈ poleS0) : p.Prime := by
  simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Local analysis at `p ∈ S₀`: `p ∤ θ`, and `θ c₁² ≡ M₁² (mod p³)` with `p ∤ c₁ M₁`. -/
theorem theta_local_S0 {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) {p : ℕ}
    (hp : p ∈ poleS0) :
    ¬ (p : ℤ) ∣ thetaOf B m ∧ ∃ c₁ M₁ : ℤ, ¬ (p : ℤ) ∣ c₁ ∧ ¬ (p : ℤ) ∣ M₁ ∧
      thetaOf B m * c₁ ^ 2 ≡ M₁ ^ 2 [ZMOD (p : ℤ) ^ 3] := by
  obtain ⟨k, a, s, c, ha, hak, hcop, hS0, hm0, hs, hc, hpos, hβs, hθs, hs', hc'⟩ :=
    slot_setup hB hm
  have hpp : p.Prime := prime_of_mem_poleS0' hp
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hpp
  obtain ⟨hpk, a', rfl⟩ := hS0 p hp
  by_cases hpm : (p : ℤ) ∣ m
  · obtain ⟨m', rfl⟩ := hpm
    have hpm' : ¬ (p : ℤ) ∣ m' := fun h =>
      (prime_dvd_divisor_2730 hm hpp (dvd_mul_right _ _)).2 (by rw [sq]; exact mul_dvd_mul_left _ h)
    have hM₁ : ¬ (p : ℤ) ∣ m' * k := fun h => (hpZ.dvd_or_dvd h).elim hpm' hpk
    obtain ⟨h1, c₁, hc₁, h2⟩ := local_unit_square (e := 1) (j := 3)
      (X := p * m' * (p ^ 4 * a')) hpp (by norm_num) hθs hM₁ ⟨m' * a', by ring⟩
      (by rw [hc']; ring)
    exact ⟨h1, c₁, m' * k, hc₁, hM₁, h2⟩
  · have hM₁ : ¬ (p : ℤ) ∣ m * k := fun h => (hpZ.dvd_or_dvd h).elim hpm hpk
    obtain ⟨h1, c₁, hc₁, h2⟩ := local_unit_square (e := 0) (j := 3)
      (X := m * (p ^ 4 * a')) hpp (by norm_num) hθs hM₁ ⟨m * a' * p, by ring⟩
      (by rw [hc']; ring)
    exact ⟨h1, c₁, m * k, hc₁, hM₁, h2⟩

/-- Local analysis at a prime `p ∣ β`: `p ∤ θ`, and `θ c₁² ≡ M₁² (mod p)` with `p ∤ c₁ M₁`. -/
theorem theta_local_beta {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) {p : ℕ}
    (hp : p.Prime) (hpβ : (p : ℤ) ∣ betaOf B m) :
    ¬ (p : ℤ) ∣ thetaOf B m ∧ ∃ c₁ M₁ : ℤ, ¬ (p : ℤ) ∣ c₁ ∧ ¬ (p : ℤ) ∣ M₁ ∧
      thetaOf B m * c₁ ^ 2 ≡ M₁ ^ 2 [ZMOD p] := by
  by_cases hS : p ∈ poleS0
  · obtain ⟨h1, c₁, M₁, h2, h3, h4⟩ := theta_local_S0 hB hm hS
    exact ⟨h1, c₁, M₁, h2, h3, h4.of_dvd (dvd_pow_self _ (by norm_num))⟩
  · obtain ⟨k, a, s, c, ha, hak, hcop, hS0, hm0, hs, hc, hpos, hβs, hθs, hs', hc'⟩ :=
      slot_setup hB hm
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpm : ¬ (p : ℤ) ∣ m := fun h => hS (prime_dvd_divisor_2730 hm hp h).1
    have hpma : (p : ℤ) ∣ m * a := by rw [hs']; exact dvd_mul_of_dvd_left hpβ _
    have hpk : ¬ (p : ℤ) ∣ k := by
      intro hk
      have hpa : (p : ℤ) ∣ a := (hpZ.dvd_or_dvd hpma).resolve_left hpm
      exact hpZ.not_isUnit (hcop.isUnit_of_dvd' hpa hk)
    have hM₁ : ¬ (p : ℤ) ∣ m * k := fun h => (hpZ.dvd_or_dvd h).elim hpm hpk
    obtain ⟨h1, c₁, hc₁, h2⟩ := local_unit_square (e := 0) (j := 1) (X := m * a) hp le_rfl hθs
      hM₁ (by simpa using hpma) (by rw [hc']; ring)
    exact ⟨h1, c₁, m * k, hc₁, hM₁, by simpa using h2⟩

/-- **(θ1)**: `θ > 0`, `θ ≡ 1 (mod 8)` and `gcd(θ, 2730) = 1`. -/
theorem theta1 {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) :
    0 < thetaOf B m ∧ thetaOf B m % 8 = 1 ∧ Int.gcd (thetaOf B m) 2730 = 1 := by
  obtain ⟨k, a, s, c, ha, hak, hcop, hS0, hm0, hs, hc, hpos, hβs, hθs, hs', hc'⟩ :=
    slot_setup hB hm
  refine ⟨?_, ?_, ?_⟩
  · have : 0 < thetaOf B m * c ^ 2 := hc' ▸ hpos
    exact pos_of_mul_pos_left this (sq_nonneg c)
  · obtain ⟨-, c₁, M₁, hc₁, hM₁, h⟩ := theta_local_S0 hB hm (p := 2) (by decide)
    have ho1 : Odd c₁ :=
      Int.not_even_iff_odd.mp fun he => hc₁ (by exact_mod_cast even_iff_two_dvd.mp he)
    have ho2 : Odd M₁ :=
      Int.not_even_iff_odd.mp fun he => hM₁ (by exact_mod_cast even_iff_two_dvd.mp he)
    have h' : thetaOf B m * c₁ ^ 2 ≡ M₁ ^ 2 [ZMOD 8] := by simpa using h
    have h8 : thetaOf B m ≡ 1 [ZMOD 8] := by
      have e1 := (int_sq_modEq_one_of_odd ho1).mul_left (thetaOf B m)
      rw [mul_one] at e1
      exact (e1.symm.trans h').trans (int_sq_modEq_one_of_odd ho2)
    unfold Int.ModEq at h8
    omega
  · rw [Int.gcd_eq_natAbs_gcd_natAbs]
    refine Nat.coprime_of_dvd fun q hq h1 h2 => ?_
    have hS : q ∈ poleS0 := by
      by_contra hS
      exact Mult.not_dvd_2730_of_not_mem_poleS0 hq hS (by simpa using h2)
    exact (theta_local_S0 hB hm hS).1 (Int.natCast_dvd.mpr h1)

/-- **(θ2)**: `β` and `θ` have disjoint supports. -/
theorem theta2 {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) (p : ℕ) (hp : p.Prime)
    (hpβ : (p : ℤ) ∣ betaOf B m) : ¬ (p : ℤ) ∣ thetaOf B m :=
  (theta_local_beta hB hm hp hpβ).1

/-- **(θ2)**, as coprimality. -/
theorem theta2_isCoprime {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) :
    IsCoprime (betaOf B m) (thetaOf B m) := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs_gcd_natAbs]
  exact Nat.coprime_of_dvd fun q hq h1 h2 =>
    theta2 hB hm q hq (Int.natCast_dvd.mpr h1) (Int.natCast_dvd.mpr h2)

/-- **(θ3)**: `(β/ℓ) = 1` for every prime `ℓ ∣ θ` (with the signed `β`). -/
theorem theta3 {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : ℤ) ∣ thetaOf B m) : legendreSym ℓ (betaOf B m) = 1 := by
  obtain ⟨k, a, s, c, ha, hak, hcop, hS0, hm0, hs, hc, hpos, hβs, hθs, hs', hc'⟩ :=
    slot_setup hB hm
  have hp : ℓ.Prime := Fact.out
  have hpZ : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hS : ℓ ∉ poleS0 := fun h => (theta_local_S0 hB hm h).1 hℓ
  have hpm : ¬ (ℓ : ℤ) ∣ m := fun h => hS (prime_dvd_divisor_2730 hm hp h).1
  have hdiff : (ℓ : ℤ) ∣ (m * k) ^ 2 - m * a := hc' ▸ dvd_mul_of_dvd_left hℓ _
  have hpk : ¬ (ℓ : ℤ) ∣ k := by
    intro hk
    have h1 : (ℓ : ℤ) ∣ (m * k) ^ 2 := dvd_pow (dvd_mul_of_dvd_right hk m) two_ne_zero
    have h2 : (ℓ : ℤ) ∣ m * a := by
      have := dvd_sub h1 hdiff; rwa [sub_sub_cancel] at this
    have hpa : (ℓ : ℤ) ∣ a := (hpZ.dvd_or_dvd h2).resolve_left hpm
    exact hpZ.not_isUnit (hcop.isUnit_of_dvd' hpa hk)
  have hM : ¬ (ℓ : ℤ) ∣ m * k := fun h => (hpZ.dvd_or_dvd h).elim hpm hpk
  have hma : ¬ (ℓ : ℤ) ∣ m * a := by
    intro h
    have := dvd_add hdiff h
    rw [sub_add_cancel] at this
    exact hM (hpZ.dvd_of_dvd_pow this)
  have hs_ : ¬ (ℓ : ℤ) ∣ s := fun h =>
    hma (hs' ▸ dvd_mul_of_dvd_right (dvd_pow h two_ne_zero) _)
  apply legendreSym_eq_one_of_modEq hs_ hM
  rw [← hs']
  exact Int.modEq_iff_dvd.mpr hdiff

/-- **(θ4)**: `(θ/p) = 1` for every prime `p ∣ β` (the note states it for odd `p`; it holds for
`p = 2` as well, since `θ` is odd). -/
theorem theta4 {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) (p : ℕ) [Fact p.Prime]
    (hpβ : (p : ℤ) ∣ betaOf B m) : legendreSym p (thetaOf B m) = 1 := by
  obtain ⟨-, c₁, M₁, hc₁, hM₁, h⟩ := theta_local_beta hB hm Fact.out hpβ
  exact legendreSym_eq_one_of_modEq hc₁ hM₁ h

/-- **L2** (slot-k §1.1, (θ1)–(θ4)): for every admissible `B` and every signed divisor `m` of
2730, with `β = sqf(mB)` and `θ = sqf(m(m - B))`:
(θ1) `θ > 0`, `θ ≡ 1 (mod 8)`, `gcd(θ, 2730) = 1`; (θ2) `β` and `θ` have disjoint supports;
(θ3) `(β/ℓ) = 1` for every prime `ℓ ∣ θ`; (θ4) `(θ/p) = 1` for every odd prime `p ∣ β`. -/
theorem theta_props {B : ℚ} (hB : Admissible B) {m : ℤ} (hm : m ∣ 2730) :
    (0 < thetaOf B m ∧ thetaOf B m % 8 = 1 ∧ Int.gcd (thetaOf B m) 2730 = 1) ∧
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ betaOf B m → ¬ (p : ℤ) ∣ thetaOf B m) ∧
    (∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : ℤ) ∣ thetaOf B m → legendreSym ℓ (betaOf B m) = 1) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → (p : ℤ) ∣ betaOf B m →
      legendreSym p (thetaOf B m) = 1) :=
  ⟨theta1 hB hm, theta2 hB hm, fun ℓ _ => theta3 hB hm ℓ, fun p _ _ => theta4 hB hm p⟩

end ZInQ.RouteK
