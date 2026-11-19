import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Lane RC33: the Kronecker character of a fundamental discriminant

For a fundamental discriminant `D` (`IsFundamentalDiscriminant D`), this file builds the quadratic
Dirichlet character `χ_D` modulo `|D|` out of the Kronecker symbol `kronecker D n = (D/n)` of
`PrintsAnalytic/Basic.lean`, and proves that it is primitive. Everything is PROVED.

* `kronecker_mul`, `kronecker_mul_left`: complete multiplicativity in `n` and in `D`.
* `exists_decomp`: `D = e * d` with `e ∈ {1, -4, 8, -8}` and `d ≡ 1 (mod 4)` squarefree.
* `kronecker_eq_jacobiSym_of_one_mod_four`: `(d/n) = J(n | |d|)` for `d ≡ 1 (mod 4)`
  (quadratic reciprocity); `kronecker_neg_four`, `kronecker_eight`, `kronecker_neg_eight`:
  explicit values of the `2`-parts.
* `kronecker_congr`: `(D/·)` is periodic modulo `|D|` on positive integers;
  `kronecker_eq_zero_of_not_coprime`: it vanishes off the residues prime to `|D|`.
* `kroneckerChar hD : DirichletCharacter ℂ |D|` with `kroneckerChar_natCast` (`χ_D(n) = (D/n)`
  for `n ≠ 0`), `kroneckerChar_neg_one` (`χ_D(-1) = sgn D`), `kroneckerChar_isQuadratic`.
* `kroneckerChar_isPrimitive`: for every prime `p ∣ |D|` an explicit `n ≡ 1 (mod |D|/p)` with
  `(D/n) = -1` (`exists_witness`, by the Chinese remainder theorem and a quadratic non-residue
  modulo `p`) shows that `χ_D` does not factor through `|D|/p`, so its conductor is `|D|`.
-/

namespace ZInQ.Manuscript.RC.PrintsAnalytic.TwistedFE

open ZInQ.Manuscript.RC.PrintsAnalytic

/-- **`kronecker D` is completely multiplicative** (PROVED) on positive integers. -/
theorem kronecker_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kronecker D (m * n) = kronecker D m * kronecker D n := by
  have hfac : (m * n).factorization 2 = m.factorization 2 + n.factorization 2 := by
    rw [Nat.factorization_mul hm hn, Finsupp.add_apply]
  have hdm : 2 ^ m.factorization 2 ∣ m := Nat.ordProj_dvd m 2
  have hdn : 2 ^ n.factorization 2 ∣ n := Nat.ordProj_dvd n 2
  have hodd : m * n / 2 ^ (m * n).factorization 2 =
      (m / 2 ^ m.factorization 2) * (n / 2 ^ n.factorization 2) := by
    rw [hfac, pow_add, Nat.div_mul_div_comm hdm hdn]
  have hm' : m / 2 ^ m.factorization 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdm) (by positivity)).ne'
  have hn' : n / 2 ^ n.factorization 2 ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdn) (by positivity)).ne'
  simp only [kronecker]
  rw [hodd, jacobiSym.mul_right' D hm' hn', hfac, pow_add]
  ring

/-- **A prime dividing `D` is ramified** (PROVED): `(D/p) = 0` for a prime `p ∣ D`. -/
theorem kronecker_eq_zero_of_dvd {D : ℤ} {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) :
    kronecker D p = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h2 : D % 2 = 0 := Int.emod_eq_zero_of_dvd hpD
    simp only [kronecker, Nat.Prime.factorization_self Nat.prime_two, pow_one,
      Nat.div_self (show 0 < 2 by norm_num), jacobiSym.one_right, mul_one, kroneckerTwo, h2,
      ite_true]
  · have hf : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd fun h2 =>
      hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
    simp only [kronecker, hf, pow_zero, one_mul, Nat.div_one]
    refine jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero, fun hg => hp.one_lt.ne' ?_⟩
    have hdvd := Int.dvd_gcd hpD (dvd_refl (p : ℤ))
    rw [hg] at hdvd
    exact Nat.dvd_one.mp hdvd

/-- **`(·/2)` is multiplicative in the top argument** (PROVED), by residues mod `8`. -/
theorem kroneckerTwo_mul (a b : ℤ) :
    kroneckerTwo (a * b) = kroneckerTwo a * kroneckerTwo b := by
  have hab : a * b % 8 = (a % 8) * (b % 8) % 8 := Int.mul_emod a b 8
  have h2 : ∀ x : ℤ, x % 2 = x % 8 % 2 := fun x => by omega
  simp only [kroneckerTwo, h2 a, h2 b, h2 (a * b), hab]
  have ha : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨ a % 8 = 5 ∨
      a % 8 = 6 ∨ a % 8 = 7 := by omega
  have hb : b % 8 = 0 ∨ b % 8 = 1 ∨ b % 8 = 2 ∨ b % 8 = 3 ∨ b % 8 = 4 ∨ b % 8 = 5 ∨
      b % 8 = 6 ∨ b % 8 = 7 := by omega
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha <;>
    rcases hb with hb | hb | hb | hb | hb | hb | hb | hb <;>
    simp only [ha, hb] <;> decide

/-- **`kronecker` is multiplicative in the top argument** (PROVED): `(ab/n) = (a/n)(b/n)`. -/
theorem kronecker_mul_left (a b : ℤ) (n : ℕ) :
    kronecker (a * b) n = kronecker a n * kronecker b n := by
  simp only [kronecker, kroneckerTwo_mul, jacobiSym.mul_left, mul_pow]
  ring

/-- `(D/1) = 1` (PROVED). -/
theorem kronecker_one (D : ℤ) : kronecker D 1 = 1 := by
  simp [kronecker]

/-- **Values of `kronecker` lie in `{0, 1, -1}`** (PROVED). -/
theorem kronecker_trichotomy (D : ℤ) (n : ℕ) :
    kronecker D n = 0 ∨ kronecker D n = 1 ∨ kronecker D n = -1 := by
  have hmul : ∀ x y : ℤ, (x = 0 ∨ x = 1 ∨ x = -1) → (y = 0 ∨ y = 1 ∨ y = -1) →
      (x * y = 0 ∨ x * y = 1 ∨ x * y = -1) := by
    rintro x y (rfl | rfl | rfl) (rfl | rfl | rfl) <;> norm_num
  have h2 : kroneckerTwo D = 0 ∨ kroneckerTwo D = 1 ∨ kroneckerTwo D = -1 := by
    unfold kroneckerTwo; split_ifs <;> simp
  have hpow : ∀ k : ℕ, kroneckerTwo D ^ k = 0 ∨ kroneckerTwo D ^ k = 1 ∨
      kroneckerTwo D ^ k = -1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih h2
  exact hmul _ _ (hpow _) (jacobiSym.trichotomy _ _)

/-- `(D/n)` at odd `n` is the Jacobi symbol `J(D | n)` (PROVED). -/
theorem kronecker_of_odd (D : ℤ) {n : ℕ} (hn : n % 2 = 1) : kronecker D n = jacobiSym D n := by
  have hf : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by omega)
  simp [kronecker, hf]

/-- `(D/n) = 0` for even `D` and even `n ≠ 0` (PROVED). -/
theorem kronecker_of_even (D : ℤ) (hD : D % 2 = 0) {n : ℕ} (hn0 : n ≠ 0) (hn : n % 2 = 0) :
    kronecker D n = 0 := by
  have hf : 0 < n.factorization 2 :=
    Nat.prime_two.factorization_pos_of_dvd hn0 (Nat.dvd_of_mod_eq_zero hn)
  have h2 : kroneckerTwo D = 0 := by simp [kroneckerTwo, hD]
  simp [kronecker, h2, zero_pow hf.ne']

/-- **`(-4/n)`** (PROVED): `0` for even `n`, `1` for `n ≡ 1`, `-1` for `n ≡ 3 (mod 4)`. -/
theorem kronecker_neg_four {n : ℕ} (hn : n ≠ 0) :
    kronecker (-4) n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1 := by
  by_cases h2 : n % 2 = 0
  · simp only [h2, ↓reduceIte]; exact kronecker_of_even _ (by decide) hn h2
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    rw [kronecker_of_odd _ (by omega), jacobiSym.neg _ hodd,
      jacobiSym.at_four hodd, mul_one,
      ZMod.χ₄_nat_eq_if_mod_four]

/-- **`(8/n)`** (PROVED): `0` for even `n`, `1` for `n ≡ ±1`, `-1` for `n ≡ ±3 (mod 8)`. -/
theorem kronecker_eight {n : ℕ} (hn : n ≠ 0) :
    kronecker 8 n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 7 then 1 else -1 := by
  by_cases h2 : n % 2 = 0
  · simp only [h2, ↓reduceIte]; exact kronecker_of_even _ (by decide) hn h2
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    rw [kronecker_of_odd _ (by omega), show (8 : ℤ) = 2 ^ 3 by norm_num, jacobiSym.pow_left,
      jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
    split_ifs <;> simp_all

/-- **`(-8/n)`** (PROVED): `0` for even `n`, `1` for `n ≡ 1, 3`, `-1` for `n ≡ 5, 7 (mod 8)`. -/
theorem kronecker_neg_eight {n : ℕ} (hn : n ≠ 0) :
    kronecker (-8) n = if n % 2 = 0 then 0 else if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  by_cases h2 : n % 2 = 0
  · simp only [h2, ↓reduceIte]; exact kronecker_of_even _ (by decide) hn h2
  · have hodd : Odd n := Nat.odd_iff.mpr (by omega)
    rw [kronecker_of_odd _ (by omega), show (-8 : ℤ) = -2 * 4 by norm_num,
      jacobiSym.mul_left, jacobiSym.at_four hodd, mul_one, jacobiSym.at_neg_two hodd,
      ZMod.χ₈'_nat_eq_if_mod_eight]

/-- `(1/n) = 1` (PROVED). -/
theorem kronecker_one_left (n : ℕ) : kronecker 1 n = 1 := by
  simp [kronecker, kroneckerTwo]

/-- **Reciprocity for the Kronecker symbol** (PROVED): for `d ≡ 1 (mod 4)` and `n ≠ 0`,
`(d/n) = J(n | |d|)`. -/
theorem kronecker_eq_jacobiSym_of_one_mod_four {d : ℤ} (hd : d % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    kronecker d n = jacobiSym n d.natAbs := by
  set b := d.natAbs with hb
  set k := n.factorization 2
  set m := n / 2 ^ k with hm
  have hnm : n = 2 ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n 2).symm
  have hcop : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hn
  have hm2 : m % 2 = 1 := by
    rcases Nat.even_or_odd m with h | h
    · exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.mp h) hcop)
        (by norm_num)
    · exact Nat.odd_iff.mp h
  have hmo : Odd m := Nat.odd_iff.mpr hm2
  have hdb : d = b ∨ d = -(b : ℤ) := Int.natAbs_eq d
  have hbo : Odd b := Nat.odd_iff.mpr (by omega)
  have htwo : kroneckerTwo d = jacobiSym 2 b := by
    rw [jacobiSym.at_two hbo, ZMod.χ₈_nat_eq_if_mod_eight]
    unfold kroneckerTwo
    split_ifs <;> omega
  have hrec : jacobiSym d m = jacobiSym m b := by
    rcases hdb with h | h
    · rw [h]
      exact jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hmo
    · rw [h, jacobiSym.neg _ hmo, ZMod.χ₄_nat_eq_if_mod_four]
      have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
      rcases hm4 with h4 | h4
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hbo h4]; simp [h4, hm2]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four (by omega) h4]
        simp [h4, hm2]
  have hcast : ((n : ℕ) : ℤ) = 2 ^ k * (m : ℤ) := by rw [hnm]; push_cast; ring
  unfold kronecker
  rw [← hm, hcast, jacobiSym.mul_left, jacobiSym.pow_left, htwo, hrec]

/-! ### Fundamental discriminants -/

/-- **A fundamental discriminant is nonzero** (PROVED): `0 < |D|`. -/
theorem natAbs_pos_of_isFundamentalDiscriminant {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    0 < D.natAbs := by
  refine Int.natAbs_pos.mpr ?_
  rcases hD with ⟨_, ⟨h4, _⟩ | ⟨m, rfl, hm, _⟩⟩ <;> omega

/-- **Decomposition of a fundamental discriminant** (PROVED): `D = e * d` with
`e ∈ {1, -4, 8, -8}` and `d ≡ 1 (mod 4)` squarefree. -/
theorem exists_decomp {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    ∃ e d : ℤ, D = e * d ∧ (e = 1 ∨ e = -4 ∨ e = 8 ∨ e = -8) ∧ d % 4 = 1 ∧ Squarefree d := by
  rcases hD with ⟨_, ⟨h4, hsq⟩ | ⟨m, rfl, hm, hsq⟩⟩
  · exact ⟨1, D, by ring, Or.inl rfl, h4, hsq⟩
  · rcases hm with hm | hm
    · obtain ⟨m₁, rfl⟩ : ∃ m₁, m = 2 * m₁ := ⟨m / 2, by omega⟩
      have hsq₁ : Squarefree m₁ := hsq.of_mul_right
      have h₁ : m₁ % 4 = 1 ∨ m₁ % 4 = 3 := by omega
      rcases h₁ with h₁ | h₁
      · exact ⟨8, m₁, by ring, Or.inr (Or.inr (Or.inl rfl)), h₁, hsq₁⟩
      · refine ⟨-8, -m₁, by ring, Or.inr (Or.inr (Or.inr rfl)), by omega, ?_⟩
        rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]
        exact hsq₁
    · refine ⟨-4, -m, by ring, Or.inr (Or.inl rfl), by omega, ?_⟩
      rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.squarefree_natAbs]
      exact hsq

/-! ### Periodicity and vanishing -/

/-- **`J(n | b)` depends only on `n mod b`** (PROVED). -/
theorem jacobiSym_congr {n n' b : ℕ} (h : n ≡ n' [MOD b]) :
    jacobiSym n b = jacobiSym n' b := by
  refine jacobiSym.mod_left' ?_
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at h'
  exact h'

/-- **Periodicity of the `2`-part** (PROVED): for `e ∈ {1, -4, 8, -8}`, `(e/n)` depends only on
`n mod |e|` (for `n, n' ≠ 0`). -/
theorem kronecker_unit_congr {e : ℤ} (he : e = 1 ∨ e = -4 ∨ e = 8 ∨ e = -8) {n n' : ℕ}
    (hn : n ≠ 0) (hn' : n' ≠ 0) (h : n ≡ n' [MOD e.natAbs]) :
    kronecker e n = kronecker e n' := by
  rcases he with rfl | rfl | rfl | rfl
  · rw [kronecker_one_left, kronecker_one_left]
  · have h4 : n % 4 = n' % 4 := h
    have h2 : n % 2 = n' % 2 := by omega
    rw [kronecker_neg_four hn, kronecker_neg_four hn', h4, h2]
  · have h8 : n % 8 = n' % 8 := h
    have h2 : n % 2 = n' % 2 := by omega
    rw [kronecker_eight hn, kronecker_eight hn', h8, h2]
  · have h8 : n % 8 = n' % 8 := h
    have h2 : n % 2 = n' % 2 := by omega
    rw [kronecker_neg_eight hn, kronecker_neg_eight hn', h8, h2]

/-- **Splitting `(ed/n)`** (PROVED): for `d ≡ 1 (mod 4)` and `n ≠ 0`,
`(ed/n) = (e/n) J(n | |d|)`. -/
theorem kronecker_mul_one_mod_four (e : ℤ) {d : ℤ} (hd : d % 4 = 1) {n : ℕ} (hn : n ≠ 0) :
    kronecker (e * d) n = kronecker e n * jacobiSym n d.natAbs := by
  rw [kronecker_mul_left, kronecker_eq_jacobiSym_of_one_mod_four hd hn]

/-- **Periodicity of `(D/·)` modulo `|D|`** (PROVED) on positive integers, for a fundamental
discriminant `D`. -/
theorem kronecker_congr {D : ℤ} (hD : IsFundamentalDiscriminant D) {n n' : ℕ} (hn : n ≠ 0)
    (hn' : n' ≠ 0) (h : n ≡ n' [MOD D.natAbs]) : kronecker D n = kronecker D n' := by
  obtain ⟨e, d, rfl, he, hd, -⟩ := exists_decomp hD
  rw [Int.natAbs_mul] at h
  rw [kronecker_mul_one_mod_four e hd hn, kronecker_mul_one_mod_four e hd hn',
    kronecker_unit_congr he hn hn' (h.of_mul_right _), jacobiSym_congr (h.of_mul_left _)]

/-- **Periodicity in `ZMod |D|` form** (PROVED). -/
theorem kronecker_congr_zmod {D : ℤ} (hD : IsFundamentalDiscriminant D) {n n' : ℕ}
    (hn : n ≠ 0) (hn' : n' ≠ 0) (h : (n : ZMod D.natAbs) = n') :
    kronecker D n = kronecker D n' :=
  kronecker_congr hD hn hn' ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)

/-- **Vanishing off the units** (PROVED): `(D/n) = 0` when `n ≠ 0` is not coprime to `|D|`. -/
theorem kronecker_eq_zero_of_not_coprime (D : ℤ) {n : ℕ} (hn : n ≠ 0)
    (h : ¬ n.Coprime D.natAbs) : kronecker D n = 0 := by
  obtain ⟨p, hp, hpn, hpD⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  obtain ⟨c, rfl⟩ := hpn
  have hc : c ≠ 0 := by rintro rfl; simp at hn
  rw [kronecker_mul D hp.ne_zero hc, kronecker_eq_zero_of_dvd hp (Int.ofNat_dvd_left.mpr hpD),
    zero_mul]

/-! ### The value at `-1` -/

/-- **`(D/(2|D| - 1)) = sgn D`** (PROVED) for a fundamental discriminant `D`. -/
theorem kronecker_two_mul_natAbs_sub_one {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    kronecker D (2 * D.natAbs - 1) = Int.sign D := by
  obtain ⟨e, d, rfl, he, hd, -⟩ := exists_decomp hD
  have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
  set b := d.natAbs with hb
  have hdb : d = b ∨ d = -(b : ℤ) := Int.natAbs_eq d
  have hbo : Odd b := Nat.odd_iff.mpr (by omega)
  have hb0 : 0 < b := hbo.pos
  rw [Int.natAbs_mul] at hpos ⊢
  rw [← hb] at hpos ⊢
  have hn : 2 * (e.natAbs * b) - 1 ≠ 0 := by
    have : 0 < e.natAbs * b := hpos
    omega
  rw [kronecker_mul_one_mod_four e hd hn, ← hb]
  have hJ : jacobiSym ((2 * (e.natAbs * b) - 1 : ℕ) : ℤ) b = jacobiSym (-1) b := by
    refine jacobiSym.mod_left' ?_
    have : ((2 * (e.natAbs * b) - 1 : ℕ) : ℤ) = -1 + (b : ℤ) * (2 * e.natAbs) := by
      have : 1 ≤ 2 * (e.natAbs * b) := by omega
      push_cast [this]
      ring
    rw [this, Int.add_mul_emod_self_left]
  have hsd : jacobiSym (-1) b = Int.sign d := by
    rw [jacobiSym.at_neg_one hbo, ZMod.χ₄_nat_eq_if_mod_four]
    rcases hdb with h | h
    · have : 0 < d := by omega
      rw [Int.sign_eq_one_of_pos this]
      split_ifs <;> omega
    · have : d < 0 := by omega
      rw [Int.sign_eq_neg_one_of_neg this]
      split_ifs <;> omega
  rw [hJ, hsd, Int.sign_mul]
  rcases he with rfl | rfl | rfl | rfl
  · rw [kronecker_one_left]; rfl
  · rw [kronecker_neg_four hn]
    have h4 : (Int.natAbs (-4)) = 4 := rfl
    rw [h4]
    have h1 : (2 * (4 * b) - 1) % 2 = 1 := by omega
    have h3 : (2 * (4 * b) - 1) % 4 = 3 := by omega
    simp only [h1, h3]
    rfl
  · rw [kronecker_eight hn]
    have h4 : (Int.natAbs 8) = 8 := rfl
    rw [h4]
    have h1 : (2 * (8 * b) - 1) % 2 = 1 := by omega
    have h3 : (2 * (8 * b) - 1) % 8 = 7 := by omega
    simp only [h1, h3]
    rfl
  · rw [kronecker_neg_eight hn]
    have h4 : (Int.natAbs (-8)) = 8 := rfl
    rw [h4]
    have h1 : (2 * (8 * b) - 1) % 2 = 1 := by omega
    have h3 : (2 * (8 * b) - 1) % 8 = 7 := by omega
    simp only [h1, h3]
    rfl

/-! ### The character -/

/-- `x.val + N` reduces to `x` in `ZMod N` (PROVED). -/
theorem natCast_val_add_self {N : ℕ} [NeZero N] (x : ZMod N) :
    ((x.val + N : ℕ) : ZMod N) = x := by
  simp

/-- **The Kronecker character `χ_D` modulo `|D|`** (PROVED to be a multiplicative character) of
a fundamental discriminant `D`: `x ↦ (D/(x.val + |D|))` (the shift by `|D|` keeps the argument
positive). -/
noncomputable def kroneckerChar {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    DirichletCharacter ℂ D.natAbs :=
  haveI : NeZero D.natAbs := ⟨(natAbs_pos_of_isFundamentalDiscriminant hD).ne'⟩
  { toFun := fun x => ((kronecker D (x.val + D.natAbs) : ℤ) : ℂ)
    map_one' := by
      have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
      rw [kronecker_congr_zmod hD (n' := 1) (by omega) one_ne_zero (by simp), kronecker_one,
        Int.cast_one]
    map_mul' := fun x y => by
      have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
      rw [← Int.cast_mul, ← kronecker_mul D (by omega) (by omega)]
      congr 1
      refine kronecker_congr_zmod hD (by omega) (by positivity) ?_
      push_cast
      simp
    map_nonunit' := fun x hx => by
      have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
      rw [kronecker_eq_zero_of_not_coprime D (by omega), Int.cast_zero]
      intro hcop
      apply hx
      rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.isUnit_iff_coprime _ _).mpr (Nat.coprime_add_self_left.mp hcop) }

/-- Unfolding `kroneckerChar` (PROVED). -/
theorem kroneckerChar_apply {D : ℤ} (hD : IsFundamentalDiscriminant D) (x : ZMod D.natAbs) :
    kroneckerChar hD x = ((kronecker D (x.val + D.natAbs) : ℤ) : ℂ) :=
  rfl

/-- **`χ_D(n) = (D/n)`** (PROVED) for every natural number `n ≠ 0`. -/
theorem kroneckerChar_natCast {D : ℤ} (hD : IsFundamentalDiscriminant D) {n : ℕ} (hn : n ≠ 0) :
    kroneckerChar hD (n : ZMod D.natAbs) = (kronecker D n : ℂ) := by
  have : NeZero D.natAbs := ⟨(natAbs_pos_of_isFundamentalDiscriminant hD).ne'⟩
  have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
  rw [kroneckerChar_apply]
  congr 1
  exact kronecker_congr_zmod hD (by omega) hn (natCast_val_add_self _)

/-- **`χ_D(-1) = sgn D`** (PROVED). -/
theorem kroneckerChar_neg_one {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    kroneckerChar hD (-1) = (kroneckerNegOne D : ℂ) := by
  have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
  have hm : ((2 * D.natAbs - 1 : ℕ) : ZMod D.natAbs) = -1 := by
    have : 1 ≤ 2 * D.natAbs := by omega
    push_cast [this]
    simp
  rw [← hm, kroneckerChar_natCast hD (by omega), kronecker_two_mul_natAbs_sub_one hD,
    kroneckerNegOne]

/-- **`χ_D` is quadratic** (PROVED): its values lie in `{0, 1, -1}`. -/
theorem kroneckerChar_isQuadratic {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    (kroneckerChar hD).IsQuadratic := by
  intro x
  rw [kroneckerChar_apply]
  rcases kronecker_trichotomy D (x.val + D.natAbs) with h | h | h <;> simp [h]

/-! ### Primitivity -/

/-- **Witnesses against a smaller period** (PROVED): for a fundamental discriminant `D` and a
prime `p ∣ |D|` there is `n ≠ 0` with `n ≡ 1 (mod |D|/p)` and `(D/n) = -1`. -/
theorem exists_witness {D : ℤ} (hD : IsFundamentalDiscriminant D) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ D.natAbs) : ∃ n : ℕ, n ≠ 0 ∧ n ≡ 1 [MOD D.natAbs / p] ∧ kronecker D n = -1 := by
  obtain ⟨e, d, rfl, he, hd, hsq⟩ := exists_decomp hD
  set b := d.natAbs with hb
  have hbo : Odd b := Nat.odd_iff.mpr (by omega)
  have hb0 : 0 < b := hbo.pos
  have hbsq : Squarefree b := Int.squarefree_natAbs.mpr hsq
  have hc2 : Nat.Coprime 2 b := Nat.coprime_two_left.mpr hbo
  rw [Int.natAbs_mul, ← hb] at hpN ⊢
  by_cases hp2 : p = 2
  · subst hp2
    rcases he with rfl | rfl | rfl | rfl
    · exfalso
      have h1 : (Int.natAbs 1) = 1 := rfl
      rw [h1] at hpN
      omega
    · have h4 : (Int.natAbs (-4)) = 4 := rfl
      rw [h4]
      obtain ⟨k, hk3, hk1⟩ := Nat.chineseRemainder (Nat.Coprime.pow_left 2 hc2) 3 1
      refine ⟨k + b * 4, by omega, ?_, ?_⟩
      · have hm : (4 * b) / 2 = 2 * b := by omega
        rw [hm]
        refine (Nat.modEq_and_modEq_iff_modEq_mul hc2).mp ⟨?_, ?_⟩
        · have : k % 4 = 3 := hk3
          show (k + b * 4) % 2 = 1 % 2
          omega
        · exact (Nat.add_mul_mod_self_left k b 4).trans hk1
      · rw [kronecker_mul_one_mod_four _ hd (by omega), ← hb, kronecker_neg_four (by omega),
          jacobiSym_congr ((Nat.add_mul_mod_self_left k b 4).trans hk1), Nat.cast_one,
          jacobiSym.one_left]
        have : k % 4 = 3 := hk3
        have h1 : (k + b * 4) % 2 = 1 := by omega
        have h3 : (k + b * 4) % 4 = 3 := by omega
        simp only [h1, h3]
        rfl
    · have h4 : (Int.natAbs 8) = 8 := rfl
      rw [h4]
      obtain ⟨k, hk5, hk1⟩ := Nat.chineseRemainder (Nat.Coprime.pow_left 3 hc2) 5 1
      have hc4 : Nat.Coprime 4 b := Nat.Coprime.pow_left 2 hc2
      refine ⟨k + b * 8, by omega, ?_, ?_⟩
      · have hm : (8 * b) / 2 = 4 * b := by omega
        rw [hm]
        refine (Nat.modEq_and_modEq_iff_modEq_mul hc4).mp ⟨?_, ?_⟩
        · have : k % 8 = 5 := hk5
          show (k + b * 8) % 4 = 1 % 4
          omega
        · exact (Nat.add_mul_mod_self_left k b 8).trans hk1
      · rw [kronecker_mul_one_mod_four _ hd (by omega), ← hb, kronecker_eight (by omega),
          jacobiSym_congr ((Nat.add_mul_mod_self_left k b 8).trans hk1), Nat.cast_one,
          jacobiSym.one_left]
        have : k % 8 = 5 := hk5
        have h1 : (k + b * 8) % 2 = 1 := by omega
        have h3 : (k + b * 8) % 8 = 5 := by omega
        simp only [h1, h3]
        rfl
    · have h4 : (Int.natAbs (-8)) = 8 := rfl
      rw [h4]
      obtain ⟨k, hk5, hk1⟩ := Nat.chineseRemainder (Nat.Coprime.pow_left 3 hc2) 5 1
      have hc4 : Nat.Coprime 4 b := Nat.Coprime.pow_left 2 hc2
      refine ⟨k + b * 8, by omega, ?_, ?_⟩
      · have hm : (8 * b) / 2 = 4 * b := by omega
        rw [hm]
        refine (Nat.modEq_and_modEq_iff_modEq_mul hc4).mp ⟨?_, ?_⟩
        · have : k % 8 = 5 := hk5
          show (k + b * 8) % 4 = 1 % 4
          omega
        · exact (Nat.add_mul_mod_self_left k b 8).trans hk1
      · rw [kronecker_mul_one_mod_four _ hd (by omega), ← hb, kronecker_neg_eight (by omega),
          jacobiSym_congr ((Nat.add_mul_mod_self_left k b 8).trans hk1), Nat.cast_one,
          jacobiSym.one_left]
        have : k % 8 = 5 := hk5
        have h1 : (k + b * 8) % 2 = 1 := by omega
        have h3 : (k + b * 8) % 8 = 5 := by omega
        simp only [h1, h3]
        rfl
  · -- `p` is odd, so `p ∣ |d|`
    have hea : e.natAbs ∣ 8 := by rcases he with rfl | rfl | rfl | rfl <;> decide
    have hpa : ¬ p ∣ e.natAbs := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 from h.trans hea)))
    have hpb : p ∣ b := (hp.dvd_mul.mp hpN).resolve_left hpa
    obtain ⟨c, hc⟩ := hpb
    have hcop : Nat.Coprime p c := (Nat.squarefree_mul_iff.mp (hc ▸ hbsq)).1
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc; omega
    have hea0 : e.natAbs ≠ 0 := by rcases he with rfl | rfl | rfl | rfl <;> decide
    have hdiv : e.natAbs * b / p = e.natAbs * c := by
      rw [hc, show e.natAbs * (p * c) = p * (e.natAbs * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos]
    rw [hdiv]
    have hpac : Nat.Coprime p (e.natAbs * c) :=
      Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpa) hcop
    have := Fact.mk hp
    obtain ⟨r, hr⟩ := quadraticChar_exists_neg_one (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    obtain ⟨k, hkr, hk1⟩ := Nat.chineseRemainder hpac r.val 1
    set n := k + p * (e.natAbs * c) with hn
    have hn0 : n ≠ 0 := by
      have : 0 < p * (e.natAbs * c) := by
        have := hp.pos
        positivity
      omega
    have hnp : n ≡ r.val [MOD p] := (Nat.add_mul_mod_self_left k p _).trans hkr
    have hn1 : n ≡ 1 [MOD e.natAbs * c] := (Nat.add_mul_mod_self_right k p _).trans hk1
    refine ⟨n, hn0, hn1, ?_⟩
    rw [kronecker_mul_one_mod_four _ hd hn0, ← hb,
      kronecker_unit_congr he hn0 one_ne_zero (hn1.of_mul_right c), kronecker_one, one_mul, hc,
      jacobiSym.mul_right' _ hp.ne_zero hc0, jacobiSym_congr (hn1.of_mul_left _), Nat.cast_one,
      jacobiSym.one_left, mul_one, jacobiSym_congr hnp, ← jacobiSym.legendreSym.to_jacobiSym]
    simpa [legendreSym] using hr

/-- **A proper divisor divides a maximal proper divisor** (PROVED): if `c ∣ N`, `c ≠ N`, `0 < N`,
then `c ∣ N / p` for some prime `p ∣ N`. -/
theorem exists_prime_dvd_div_of_dvd {N c : ℕ} (hN : 0 < N) (hc : c ∣ N) (hne : c ≠ N) :
    ∃ p, p.Prime ∧ p ∣ N ∧ c ∣ N / p := by
  obtain ⟨t, rfl⟩ := hc
  have ht1 : t ≠ 1 := by rintro rfl; exact hne (mul_one c).symm
  obtain ⟨p, hp, s, rfl⟩ := Nat.exists_prime_and_dvd ht1
  refine ⟨p, hp, ⟨c * s, by ring⟩, ⟨s, ?_⟩⟩
  rw [show c * (p * s) = p * (c * s) by ring, Nat.mul_div_cancel_left _ hp.pos]

/-- **`χ_D` is primitive** (PROVED): its conductor is `|D|`. -/
theorem kroneckerChar_isPrimitive {D : ℤ} (hD : IsFundamentalDiscriminant D) :
    (kroneckerChar hD).IsPrimitive := by
  have hpos := natAbs_pos_of_isFundamentalDiscriminant hD
  have : NeZero D.natAbs := ⟨hpos.ne'⟩
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  obtain ⟨p, hp, hpN, hdiv⟩ :=
    exists_prime_dvd_div_of_dvd hpos (kroneckerChar hD).conductor_dvd_level hne
  obtain ⟨hd, χ', hχ'⟩ : (kroneckerChar hD).FactorsThrough (D.natAbs / p) :=
    ((kroneckerChar hD).mem_conductorSet_iff_conductor_dvd (Nat.div_dvd_of_dvd hpN)).mpr hdiv
  obtain ⟨n, hn0, hn1, hnk⟩ := exists_witness hD hp hpN
  have hval : kroneckerChar hD (n : ZMod D.natAbs) = -1 := by
    rw [kroneckerChar_natCast hD hn0, hnk]
    simp
  have hunit : IsUnit (n : ZMod D.natAbs) := by
    by_contra h
    rw [MulChar.map_nonunit _ h] at hval
    norm_num at hval
  have hone : kroneckerChar hD (n : ZMod D.natAbs) = 1 := by
    rw [← hunit.unit_spec, hχ', DirichletCharacter.changeLevel_eq_cast_of_dvd, hunit.unit_spec,
      ZMod.cast_natCast hd, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hn1, Nat.cast_one, map_one]
  rw [hval] at hone
  norm_num at hone

end ZInQ.Manuscript.RC.PrintsAnalytic.TwistedFE
