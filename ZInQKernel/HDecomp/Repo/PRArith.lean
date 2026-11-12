import ZInQKernel.Hypotheses.Height

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-repo/PRArith.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-repo, steps A5 and A7: the arithmetic of Lemma PR(i) (h-b1 §4) and of the fibre point

For `u ∈ ℚ ∖ 𝒞`, `j₀ = J(u) = −57600 F(u)²/G(u)⁶`. Prop. TS (h-b1 §1.2, a published theorem)
says: at a prime `p` where the cover `Y₃ → P¹_j` is tame with no vertical ramification
(Lemma NV, `p ≥ 5`), the inertia of the fibre field at `p` has order `e_b / gcd(e_b, m_b)`, where
`m_b` is the intersection multiplicity of `j₀` with the branch point `b ∈ {0, ∞, −16/27}`,
`(e₀, e_∞, e_{−16/27}) = (4, 6, 2)` (A2). Here we prove the elementary half of Lemma PR(i):

* `inertia_trivial_iff` : for every prime `p ≥ 17` and `u ∈ ℚ ∖ 𝒞`,
  `4 ∣ m₀ ∧ 6 ∣ m_∞ ∧ 2 ∣ m_{−16/27}` (i.e. all three predicted inertia orders are 1)
  iff no `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd; with `m₀ = v_p(j₀)⁺`,
  `m_∞ = (−v_p(j₀))⁺`, `m_{−16/27} = v_p(j₀ + 16/27)⁺`.
* `inertia_trivial_of_not_dvd` : the same in terms of `M_S(u) = ZInQ.contactSupport S u`.
* `Hq_ne_zero`, `J_ne_zero`, `J_ne_branch` : `j₀` is finite, nonzero and `≠ −16/27`
  (h-b1 M7; A7 "j = J(u) is rational, finite and nonzero").
* `G6_sub_F2`, `J_add`, `t_eq`, `t_sub_one` : N5 L510-516 and rv-h-cm §1.4.
-/

open ZInQ

namespace GlueRepo.PR

/-- The rational functions of N5 L377-386, L510-516. -/
def Fq (u : ℚ) : ℚ := u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)
def Gq (u : ℚ) : ℚ := 7 * u ^ 2 + 300 * u + 3600
def Hq (u : ℚ) : ℚ :=
  (u ^ 2 - 60 * u - 1800) * (13 * u ^ 2 + 480 * u + 3600) * (11 * u ^ 2 + 600 * u + 7200)
/-- `H` in homogeneous form. -/
def Hh (a b : ℤ) : ℤ :=
  (a ^ 2 - 60 * a * b - 1800 * b ^ 2) * (13 * a ^ 2 + 480 * a * b + 3600 * b ^ 2) *
    (11 * a ^ 2 + 600 * a * b + 7200 * b ^ 2)

/-- `J(u)`, verbatim copy of `ZInQ.JHeight.Jmap` (`ZInQKernel/Hypotheses/JHeight.lean`, which
scratch files cannot import in this worktree). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

theorem Jmap_eq (u : ℚ) : Jmap u = -57600 * Fq u ^ 2 / Gq u ^ 6 := rfl

/-- `G⁶ − 97200 F² = H²` (N5 L513-515). -/
theorem G6_sub_F2 (u : ℚ) : Gq u ^ 6 - 97200 * Fq u ^ 2 = Hq u ^ 2 := by
  unfold Gq Fq Hq; ring

theorem Gq_ne_zero (u : ℚ) : Gq u ≠ 0 := by
  unfold Gq; nlinarith [sq_nonneg (7 * u + 150)]

/-- `J + 16/27 = 16 H² / (27 G⁶)` (h-b1 M7). -/
theorem J_add (u : ℚ) : Jmap u + 16 / 27 = 16 * Hq u ^ 2 / (27 * Gq u ^ 6) := by
  have hG := Gq_ne_zero u
  rw [Jmap_eq]
  field_simp
  linear_combination (16 : ℚ) * G6_sub_F2 u

/-- Elkies' coordinate `t = 1 + 27 j / 16` (rv-h-cm §1.3). -/
def tq (u : ℚ) : ℚ := 1 + 27 * Jmap u / 16

theorem t_eq (u : ℚ) : tq u = Hq u ^ 2 / Gq u ^ 6 := by
  have hG := Gq_ne_zero u
  unfold tq; rw [Jmap_eq]; field_simp
  linear_combination (16 : ℚ) * G6_sub_F2 u

theorem t_sub_one (u : ℚ) : tq u - 1 = -3 * (180 * Fq u / Gq u ^ 3) ^ 2 := by
  have hG := Gq_ne_zero u
  unfold tq; rw [Jmap_eq]; field_simp; ring

/-! ### Nonvanishing -/

/-- A rational square has even `3`-adic valuation. -/
theorem not_sq_of_odd_val {x d : ℚ} (hx : x ^ 2 = d) (hd : d ≠ 0)
    (hodd : Odd (padicValRat 3 d)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← hx, padicValRat.pow] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) ⟨padicValRat 3 x, by push_cast; ring⟩

theorem quad_ne_zero {α β γ : ℚ} (hα : α ≠ 0) (hΔ : β ^ 2 - 4 * α * γ ≠ 0)
    (hodd : Odd (padicValRat 3 (β ^ 2 - 4 * α * γ))) (u : ℚ) : α * u ^ 2 + β * u + γ ≠ 0 := by
  intro h
  exact not_sq_of_odd_val (x := 2 * α * u + β) (by linear_combination 4 * α * h) hΔ hodd

theorem val3_43200 : padicValRat 3 (43200 : ℚ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (43200 : ℚ) = ((3 ^ 3 * 1600 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem val3_10800 : padicValRat 3 (10800 : ℚ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (10800 : ℚ) = ((3 ^ 3 * 400 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rfl

/-- `H` has no rational root: its quadratic factors have discriminants `10800, 43200, 43200`,
of odd `3`-adic valuation (h-b1 M7). -/
theorem Hq_ne_zero (u : ℚ) : Hq u ≠ 0 := by
  have h1 : (1 : ℚ) * u ^ 2 + (-60) * u + (-1800) ≠ 0 :=
    quad_ne_zero one_ne_zero (by norm_num) (by norm_num [val3_10800]) u
  have h2 : (13 : ℚ) * u ^ 2 + 480 * u + 3600 ≠ 0 :=
    quad_ne_zero (by norm_num) (by norm_num) (by norm_num [val3_43200]) u
  have h3 : (11 : ℚ) * u ^ 2 + 600 * u + 7200 ≠ 0 :=
    quad_ne_zero (by norm_num) (by norm_num) (by norm_num [val3_43200]) u
  unfold Hq
  refine mul_ne_zero (mul_ne_zero ?_ h2) h3
  intro h; apply h1; linear_combination h

theorem Fq_ne_zero {u : ℚ} (hu : u ∉ contactSet) : Fq u ≠ 0 := by
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
  unfold Fq
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 ?_) ?_) ?_) ?_) ?_
  all_goals intro h
  exacts [h1 (by linarith), h2 (by linarith), h3 (by linarith), h4 (by linarith), h5 (by linarith)]

/-- `j₀ = J(u)` is finite and nonzero for `u ∉ 𝒞` (A7). -/
theorem J_ne_zero {u : ℚ} (hu : u ∉ contactSet) : Jmap u ≠ 0 := by
  rw [Jmap_eq]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Fq_ne_zero hu)))
    (pow_ne_zero _ (Gq_ne_zero u))

/-- `j₀ ≠ −16/27`: `J(u)` is not a branch value (h-b1 M7). -/
theorem J_ne_branch (u : ℚ) : Jmap u ≠ -16 / 27 := by
  intro h
  have h1 := J_add u
  rw [h] at h1
  have hH := Hq_ne_zero u
  have hG := Gq_ne_zero u
  have h2 : 16 * Hq u ^ 2 / (27 * Gq u ^ 6) ≠ 0 := by positivity
  exact h2 (by rw [← h1]; norm_num)

/-! ### The valuation case analysis of Lemma PR(i) -/

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

/-- A `{2,3,5,7,11,13}`-smooth number bound. -/
def smoothBound : ℕ := 2 ^ 60 * 3 ^ 40 * 5 ^ 40 * 7 ^ 6 * 11 ^ 6 * 13 ^ 6

theorem not_dvd_smoothBound (h17 : 17 ≤ p) : ¬ p ∣ smoothBound := by
  have hpp := hp.out.prime
  intro h
  simp only [smoothBound, hpp.dvd_mul] at h
  rcases h with (((((h | h) | h) | h) | h) | h) <;>
    have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h) <;> omega

theorem smooth_ne_zero (h17 : 17 ≤ p) (N : ℕ) (hN : N ∣ smoothBound) : (N : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => not_dvd_smoothBound h17 (h.trans hN)

theorem vpos_iff {z : ℤ} (hz : z ≠ 0) : 0 < padicValInt p z ↔ (z : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← pow_one (p : ℤ), padicValInt_dvd_iff]
  simp [hz, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

theorem pair_not {x y b : ℤ} {d : ℕ} (hd : (d : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (h : y = x + d * b) : ¬ ((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
  rintro ⟨hx, hy⟩
  rw [h] at hy; push_cast at hy; rw [hx, zero_add] at hy
  exact (mul_ne_zero hd hb) hy

theorem bezout_not {x y b s t : ℤ} {N k : ℕ} (hN : (N : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (h : s * x + t * y = N * b ^ k) : ¬ ((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
  rintro ⟨hx, hy⟩
  have := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at this
  rw [hx, hy, mul_zero, mul_zero, add_zero] at this
  exact (mul_ne_zero hN (pow_ne_zero _ hb)) this.symm

/-- `F`, `G` in homogeneous form (copies of `ZInQ.JHeight.Fh`, `Gh`). -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- Homogeneous Bezout certificates (`scratch/glue-repo/bezout.py`). -/
theorem bez_FG (a b : ℤ) :
    (-1001 * a - 37650 * b) * Fh a b + (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2
      + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b
      = (104976000000 : ℕ) * b ^ 7 := by
  unfold Fh Gh; push_cast; ring

theorem bez_FH (a b : ℤ) :
    (16823807 * a ^ 5 + 168910350 * a ^ 4 * b - 76576533600 * a ^ 3 * b ^ 2
      - 3442684140000 * a ^ 2 * b ^ 3 - 52460404920000 * a * b ^ 4 - 259773966000000 * b ^ 5) * Fh a
          b
    + (-117649 * a ^ 5 - 15008651 * a ^ 4 * b - 649710600 * a ^ 3 * b ^ 2
      - 11566268700 * a ^ 2 * b ^ 3 - 72155790000 * a * b ^ 4 - 14580000 * b ^ 5) * Hh a b
      = (680244480000000000 : ℕ) * b ^ 11 := by
  unfold Fh Hh; push_cast; ring

theorem bez_GH (a b : ℤ) :
    (-858 * a ^ 5 - 5693 * a ^ 4 * b + 3924600 * a ^ 3 * b ^ 2 + 161087400 * a ^ 2 * b ^ 3
      + 2164860000 * a * b ^ 4 + 9985680000 * b ^ 5) * Gh a b + (42 * a + 757 * b) * Hh a b
      = (629856000000 : ℕ) * b ^ 7 := by
  unfold Gh Hh; push_cast; ring

theorem padicValRat_int_eq_zero (h17 : 17 ≤ p) {z : ℤ} (N : ℕ) (hz : z.natAbs = N)
    (hN : N ∣ smoothBound) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  · rfl
  · rw [Int.natCast_dvd, hz]
    exact fun h => not_dvd_smoothBound h17 (h.trans hN)

/-- The final case analysis of Lemma PR(i) over the naturals (`p ∤ b`). -/
theorem final_nat {v0 v1 v2 v3 v4 v5 vF vG vH vb : ℕ}
    (hF : (vF : ℤ) = v0 + v1 + v2 + v3 + v4 + v5) (hb : vb = 0)
    (q01 : ¬ (0 < v0 ∧ 0 < v1))
    (q02 : ¬ (0 < v0 ∧ 0 < v2))
    (q03 : ¬ (0 < v0 ∧ 0 < v3))
    (q04 : ¬ (0 < v0 ∧ 0 < v4))
    (q05 : ¬ (0 < v0 ∧ 0 < v5))
    (q12 : ¬ (0 < v1 ∧ 0 < v2))
    (q13 : ¬ (0 < v1 ∧ 0 < v3))
    (q14 : ¬ (0 < v1 ∧ 0 < v4))
    (q15 : ¬ (0 < v1 ∧ 0 < v5))
    (q23 : ¬ (0 < v2 ∧ 0 < v3))
    (q24 : ¬ (0 < v2 ∧ 0 < v4))
    (q25 : ¬ (0 < v2 ∧ 0 < v5))
    (q34 : ¬ (0 < v3 ∧ 0 < v4))
    (q35 : ¬ (0 < v3 ∧ 0 < v5))
    (q45 : ¬ (0 < v4 ∧ 0 < v5))
    (bFG : ¬ (0 < vF ∧ 0 < vG)) (bFH : ¬ (0 < vF ∧ 0 < vH)) (bGH : ¬ (0 < vG ∧ 0 < vH)) :
    (4 ∣ (2 * (vF : ℤ) - 6 * (vG : ℤ)).toNat ∧ 6 ∣ (-(2 * (vF : ℤ) - 6 * (vG : ℤ))).toNat ∧
      2 ∣ (2 * (vH : ℤ) - 6 * (vG : ℤ)).toNat) ↔
      ¬ ((0 < (v0 : ℤ) - vb ∧ ((v0 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v1 : ℤ) - vb ∧ ((v1 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v2 : ℤ) - vb ∧ ((v2 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v3 : ℤ) - vb ∧ ((v3 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v4 : ℤ) - vb ∧ ((v4 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v5 : ℤ) - vb ∧ ((v5 : ℤ) - vb) % 2 = 1)) := by
  subst hb
  rcases Nat.eq_zero_or_pos vF with hF0 | hF0
  · clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH
    have e0 : v0 = 0 := by omega
    have e1 : v1 = 0 := by omega
    have e2 : v2 = 0 := by omega
    have e3 : v3 = 0 := by omega
    have e4 : v4 = 0 := by omega
    have e5 : v5 = 0 := by omega
    omega
  · have hG0 : vG = 0 := by by_contra h; exact bFG ⟨hF0, Nat.pos_of_ne_zero h⟩
    have hH0 : vH = 0 := by by_contra h; exact bFH ⟨hF0, Nat.pos_of_ne_zero h⟩
    rcases Nat.eq_zero_or_pos v0 with h0 | h0
    ·
      rcases Nat.eq_zero_or_pos v1 with h1 | h1
      ·
        rcases Nat.eq_zero_or_pos v2 with h2 | h2
        ·
          rcases Nat.eq_zero_or_pos v3 with h3 | h3
          ·
            rcases Nat.eq_zero_or_pos v4 with h4 | h4
            ·
              rcases Nat.eq_zero_or_pos v5 with h5 | h5
              ·
                clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
                omega
              · have z0 : v0 = 0 := by by_contra h; exact q05 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z1 : v1 = 0 := by by_contra h; exact q15 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z2 : v2 = 0 := by by_contra h; exact q25 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z3 : v3 = 0 := by by_contra h; exact q35 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z4 : v4 = 0 := by by_contra h; exact q45 ⟨(Nat.pos_of_ne_zero h), h5⟩
                clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
                omega
            · have z0 : v0 = 0 := by by_contra h; exact q04 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z1 : v1 = 0 := by by_contra h; exact q14 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z2 : v2 = 0 := by by_contra h; exact q24 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z3 : v3 = 0 := by by_contra h; exact q34 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z5 : v5 = 0 := by by_contra h; exact q45 ⟨h4, (Nat.pos_of_ne_zero h)⟩
              clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
              omega
          · have z0 : v0 = 0 := by by_contra h; exact q03 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z1 : v1 = 0 := by by_contra h; exact q13 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z2 : v2 = 0 := by by_contra h; exact q23 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z4 : v4 = 0 := by by_contra h; exact q34 ⟨h3, (Nat.pos_of_ne_zero h)⟩
            have z5 : v5 = 0 := by by_contra h; exact q35 ⟨h3, (Nat.pos_of_ne_zero h)⟩
            clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
            omega
        · have z0 : v0 = 0 := by by_contra h; exact q02 ⟨(Nat.pos_of_ne_zero h), h2⟩
          have z1 : v1 = 0 := by by_contra h; exact q12 ⟨(Nat.pos_of_ne_zero h), h2⟩
          have z3 : v3 = 0 := by by_contra h; exact q23 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          have z4 : v4 = 0 := by by_contra h; exact q24 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          have z5 : v5 = 0 := by by_contra h; exact q25 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
          omega
      · have z0 : v0 = 0 := by by_contra h; exact q01 ⟨(Nat.pos_of_ne_zero h), h1⟩
        have z2 : v2 = 0 := by by_contra h; exact q12 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z3 : v3 = 0 := by by_contra h; exact q13 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z4 : v4 = 0 := by by_contra h; exact q14 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z5 : v5 = 0 := by by_contra h; exact q15 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
        omega
    · have z1 : v1 = 0 := by by_contra h; exact q01 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z2 : v2 = 0 := by by_contra h; exact q02 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z3 : v3 = 0 := by by_contra h; exact q03 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z4 : v4 = 0 := by by_contra h; exact q04 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z5 : v5 = 0 := by by_contra h; exact q05 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
      omega


/-- **Lemma PR(i), elementary half.** For a prime `p ≥ 17` and `u ∈ ℚ ∖ 𝒞`, the three
predicted inertia orders `e_b / gcd(e_b, m_b)` of Prop. TS are all `1` (equivalently
`e_b ∣ m_b`) iff no `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd. -/
theorem inertia_trivial_iff (h17 : 17 ≤ p) {u : ℚ} (hu : u ∉ contactSet) :
    (4 ∣ (padicValRat p (Jmap u)).toNat ∧ 6 ∣ (-padicValRat p (Jmap u)).toNat ∧
      2 ∣ (padicValRat p (Jmap u + 16 / 27)).toNat) ↔
    ¬ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)) := by
  set a : ℤ := u.num
  set b : ℤ := (u.den : ℤ)
  have hbq : (b : ℚ) ≠ 0 := by simp [b]
  have hb0 : b ≠ 0 := by simp [b]
  have hu_eq : u = (a : ℚ) / b := by simp [a, b, Rat.num_div_den]
  have hFq := Fq_ne_zero hu
  have hGq := Gq_ne_zero u
  have hHq := Hq_ne_zero u
  -- homogeneous forms
  have eF : Fq u = (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fq Fh; push_cast; field_simp
  have eG : Gq u = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gq Gh; push_cast; field_simp
  have eH : Hq u = (Hh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Hq Hh; push_cast; field_simp
  have hFh : (Fh a b : ℚ) ≠ 0 := by
    intro h; apply hFq; rw [eF, h, zero_div]
  have hGh : (Gh a b : ℚ) ≠ 0 := by
    intro h; apply hGq; rw [eG, h, zero_div]
  have hHh : (Hh a b : ℚ) ≠ 0 := by
    intro h; apply hHq; rw [eH, h, zero_div]
  have hFh' : Fh a b ≠ 0 := by exact_mod_cast hFh
  have hGh' : Gh a b ≠ 0 := by exact_mod_cast hGh
  have hHh' : Hh a b ≠ 0 := by exact_mod_cast hHh
  have eJ : Jmap u = ((-57600 : ℤ) : ℚ) * (Fh a b : ℚ) ^ 2 / (Gh a b : ℚ) ^ 6 := by
    rw [Jmap_eq, eF, eG]; push_cast; field_simp
  have eJ' : Jmap u + 16 / 27 = ((16 : ℤ) : ℚ) * (Hh a b : ℚ) ^ 2 / (((27 : ℤ) : ℚ) * (Gh a b : ℚ) ^
      6) := by
    rw [J_add, eH, eG]; push_cast; field_simp
  -- valuations of J and J + 16/27
  have v57600 : padicValRat p (((-57600 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 57600 (by norm_num) (by unfold smoothBound; norm_num)
  have v16 : padicValRat p (((16 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 16 (by norm_num) (by unfold smoothBound; norm_num)
  have v27 : padicValRat p (((27 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 27 (by norm_num) (by unfold smoothBound; norm_num)
  have hJv : padicValRat p (Jmap u) = 2 * padicValInt p (Fh a b) - 6 * padicValInt p (Gh a b) := by
    rw [eJ, padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hFh)) (pow_ne_zero _ hGh),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hFh), padicValRat.pow, padicValRat.pow,
      v57600, padicValRat.of_int, padicValRat.of_int]
    push_cast; ring
  have hJv' : padicValRat p (Jmap u + 16 / 27)
      = 2 * padicValInt p (Hh a b) - 6 * padicValInt p (Gh a b) := by
    rw [eJ', padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hHh))
        (mul_ne_zero (by norm_num) (pow_ne_zero _ hGh)),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hHh),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hGh), padicValRat.pow, padicValRat.pow,
      v16, v27, padicValRat.of_int, padicValRat.of_int]
    push_cast; ring
  -- the six contact factors
  have hX : ∀ c : ℤ, (c : ℚ) ∈ contactSet → ((a - c * b : ℤ) : ℚ) ≠ 0 ∧
      u - c = ((a - c * b : ℤ) : ℚ) / b := by
    intro c hc
    have e : u - c = ((a - c * b : ℤ) : ℚ) / b := by rw [hu_eq]; push_cast; field_simp
    refine ⟨fun h => ?_, e⟩
    rw [h, zero_div, sub_eq_zero] at e
    exact hu (e ▸ hc)
  have vX : ∀ c : ℤ, (c : ℚ) ∈ contactSet →
      padicValRat p (u - c) = padicValInt p (a - c * b) - padicValInt p b := by
    intro c hc
    rw [(hX c hc).2, padicValRat.div (hX c hc).1 hbq, padicValRat.of_int, padicValRat.of_int]
  have m0 : ((0 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m1 : ((-15 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m2 : ((-20 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m3 : ((-24 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m4 : ((-30 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m5 : ((-60 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have n0 := (hX 0 m0).1
  have n1 := (hX (-15) m1).1
  have n2 := (hX (-20) m2).1
  have n3 := (hX (-24) m3).1
  have n4 := (hX (-30) m4).1
  have n5 := (hX (-60) m5).1
  have hv0 := vX 0 m0
  have hv1 := vX (-15) m1
  have hv2 := vX (-20) m2
  have hv3 := vX (-24) m3
  have hv4 := vX (-30) m4
  have hv5 := vX (-60) m5
  push_cast at hv0 hv1 hv2 hv3 hv4 hv5
  -- v(F) is the sum
  have hFprod : Fh a b = (a - 0 * b) * (a - -15 * b) * (a - -20 * b) * (a - -24 * b)
      * (a - -30 * b) * (a - -60 * b) := by unfold Fh; ring
  have n0' : a - 0 * b ≠ 0 := by exact_mod_cast n0
  have n1' : a - -15 * b ≠ 0 := by exact_mod_cast n1
  have n2' : a - -20 * b ≠ 0 := by exact_mod_cast n2
  have n3' : a - -24 * b ≠ 0 := by exact_mod_cast n3
  have n4' : a - -30 * b ≠ 0 := by exact_mod_cast n4
  have n5' : a - -60 * b ≠ 0 := by exact_mod_cast n5
  have c0 : ((a - 0 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n0'
  have c1 : ((a - -15 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n1'
  have c2 : ((a - -20 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n2'
  have c3 : ((a - -24 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n3'
  have c4 : ((a - -30 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n4'
  have c5 : ((a - -60 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n5'
  have hvF : (padicValInt p (Fh a b) : ℤ) = padicValInt p (a - 0 * b) + padicValInt p (a - -15 * b)
      + padicValInt p (a - -20 * b) + padicValInt p (a - -24 * b) + padicValInt p (a - -30 * b)
      + padicValInt p (a - -60 * b) := by
    simp only [← padicValRat.of_int]
    have p1 := mul_ne_zero c0 c1
    have p2 := mul_ne_zero p1 c2
    have p3 := mul_ne_zero p2 c3
    have p4 := mul_ne_zero p3 c4
    rw [hFprod, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul,
      padicValRat.mul p4 c5, padicValRat.mul p3 c4, padicValRat.mul p2 c3, padicValRat.mul p1 c2,
      padicValRat.mul c0 c1]
  have hv0 := vX 0 m0
  have hv1 := vX (-15) m1
  have hv2 := vX (-20) m2
  have hv3 := vX (-24) m3
  have hv4 := vX (-30) m4
  have hv5 := vX (-60) m5
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_ofNat] at hv0 hv1 hv2 hv3 hv4 hv5
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left]
  rw [hv0, hv1, hv2, hv3, hv4, hv5, hJv, hJv']
  simp only [Int.odd_iff]
  by_cases hbp : (b : ZMod p) = 0
  · -- `p ∣ b`: `u` is not `p`-integral; `j₀ ≡ J(∞)` meets no branch point
    have ha : (a : ZMod p) ≠ 0 := by
      intro ha
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hbp
      have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp ha
      have h2 : p ∣ u.den := Int.natCast_dvd_natCast.mp hbp
      have h3 := Nat.dvd_gcd h1 h2
      rw [u.reduced] at h3
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h3)
    have h7 : (7 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 7 (by unfold smoothBound; norm_num)
    have h11 : (11 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 11 (by unfold smoothBound; norm_num)
    have h13 : (13 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 13 (by unfold smoothBound; norm_num)
    have z : ∀ c : ℤ, padicValInt p (a - c * b) = 0 := by
      intro c
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; rw [hbp]; simpa using ha
    have zF : padicValInt p (Fh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Fh; push_cast; rw [hbp]; simp [ha]
    have zG : padicValInt p (Gh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Gh; push_cast; rw [hbp]; simp [ha, h7]
    have zH : padicValInt p (Hh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Hh; push_cast; rw [hbp]; simp [ha, h11, h13]
    have vb : 0 < padicValInt p b := (vpos_iff hb0).mpr hbp
    simp only [z, zF, zG, zH]
    omega
  · -- `p ∤ b`
    have vb0 : padicValInt p b = 0 := by
      by_contra h
      exact hbp ((vpos_iff hb0).mp (Nat.pos_of_ne_zero h))
    have q01 := pair_not (p := p) (x := a - 0 * b) (y := a - -15 * b) (d := 15)
      (smooth_ne_zero h17 15 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n1'] at q01
    have q02 := pair_not (p := p) (x := a - 0 * b) (y := a - -20 * b) (d := 20)
      (smooth_ne_zero h17 20 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n2'] at q02
    have q03 := pair_not (p := p) (x := a - 0 * b) (y := a - -24 * b) (d := 24)
      (smooth_ne_zero h17 24 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n3'] at q03
    have q04 := pair_not (p := p) (x := a - 0 * b) (y := a - -30 * b) (d := 30)
      (smooth_ne_zero h17 30 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n4'] at q04
    have q05 := pair_not (p := p) (x := a - 0 * b) (y := a - -60 * b) (d := 60)
      (smooth_ne_zero h17 60 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n5'] at q05
    have q12 := pair_not (p := p) (x := a - -15 * b) (y := a - -20 * b) (d := 5)
      (smooth_ne_zero h17 5 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n2'] at q12
    have q13 := pair_not (p := p) (x := a - -15 * b) (y := a - -24 * b) (d := 9)
      (smooth_ne_zero h17 9 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n3'] at q13
    have q14 := pair_not (p := p) (x := a - -15 * b) (y := a - -30 * b) (d := 15)
      (smooth_ne_zero h17 15 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n4'] at q14
    have q15 := pair_not (p := p) (x := a - -15 * b) (y := a - -60 * b) (d := 45)
      (smooth_ne_zero h17 45 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n5'] at q15
    have q23 := pair_not (p := p) (x := a - -20 * b) (y := a - -24 * b) (d := 4)
      (smooth_ne_zero h17 4 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n3'] at q23
    have q24 := pair_not (p := p) (x := a - -20 * b) (y := a - -30 * b) (d := 10)
      (smooth_ne_zero h17 10 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n4'] at q24
    have q25 := pair_not (p := p) (x := a - -20 * b) (y := a - -60 * b) (d := 40)
      (smooth_ne_zero h17 40 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n5'] at q25
    have q34 := pair_not (p := p) (x := a - -24 * b) (y := a - -30 * b) (d := 6)
      (smooth_ne_zero h17 6 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n3', ← vpos_iff n4'] at q34
    have q35 := pair_not (p := p) (x := a - -24 * b) (y := a - -60 * b) (d := 36)
      (smooth_ne_zero h17 36 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n3', ← vpos_iff n5'] at q35
    have q45 := pair_not (p := p) (x := a - -30 * b) (y := a - -60 * b) (d := 30)
      (smooth_ne_zero h17 30 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n4', ← vpos_iff n5'] at q45
    have bFG := bezout_not (p := p) (smooth_ne_zero h17 104976000000
      (by unfold smoothBound; norm_num)) hbp (bez_FG a b)
    have bFH := bezout_not (p := p) (smooth_ne_zero h17 680244480000000000
      (by unfold smoothBound; norm_num)) hbp (bez_FH a b)
    have bGH := bezout_not (p := p) (smooth_ne_zero h17 629856000000
      (by unfold smoothBound; norm_num)) hbp (bez_GH a b)
    rw [← vpos_iff hFh', ← vpos_iff hGh'] at bFG
    rw [← vpos_iff hFh', ← vpos_iff hHh'] at bFH
    rw [← vpos_iff hGh', ← vpos_iff hHh'] at bGH
    exact final_nat hvF vb0 q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH

/-- Lemma PR(i), elementary half, in terms of `M_S(u) = ZInQ.contactSupport S u`: for a prime
`p ∉ S` (`S ⊇ {primes ≤ 324}`), the predicted inertia orders at `p` are all `1` iff `p ∤ M_S(u)`. -/
theorem inertia_trivial_iff_not_dvd (S : Finset ℕ) (hS : ∀ q, q.Prime → q ≤ 324 → q ∈ S)
    (hpS : p ∉ S) {u : ℚ} (hu : u ∉ contactSet) :
    (4 ∣ (padicValRat p (Jmap u)).toNat ∧ 6 ∣ (-padicValRat p (Jmap u)).toNat ∧
      2 ∣ (padicValRat p (Jmap u + 16 / 27)).toNat) ↔ ¬ p ∣ contactSupport S u := by
  have h17 : 17 ≤ p := by
    by_contra h
    exact hpS (hS p hp.out (by omega))
  rw [inertia_trivial_iff h17 hu, prime_dvd_contactSupport_iff hu hp.out]
  simp [hpS]

theorem div_gcd_eq_one_iff {e m : ℕ} (he : 0 < e) : e / Nat.gcd e m = 1 ↔ e ∣ m := by
  constructor
  · intro h
    have hg : Nat.gcd e m ∣ e := Nat.gcd_dvd_left e m
    have he' : e = Nat.gcd e m := by
      have := Nat.div_mul_cancel hg
      rw [h, one_mul] at this
      exact this.symm
    rw [he']
    exact Nat.gcd_dvd_right e m
  · intro h
    rw [Nat.gcd_eq_left h, Nat.div_self he]

/-- Lemma PR(i), elementary half, with Prop. TS's inertia orders `e_b / gcd(e_b, m_b)` literally. -/
theorem inertia_orders_eq_one_iff (S : Finset ℕ) (hS : ∀ q, q.Prime → q ≤ 324 → q ∈ S)
    (hpS : p ∉ S) {u : ℚ} (hu : u ∉ contactSet) :
    (4 / Nat.gcd 4 (padicValRat p (Jmap u)).toNat = 1 ∧
      6 / Nat.gcd 6 (-padicValRat p (Jmap u)).toNat = 1 ∧
      2 / Nat.gcd 2 (padicValRat p (Jmap u + 16 / 27)).toNat = 1) ↔ ¬ p ∣ contactSupport S u := by
  rw [div_gcd_eq_one_iff (by norm_num), div_gcd_eq_one_iff (by norm_num),
    div_gcd_eq_one_iff (by norm_num)]
  exact inertia_trivial_iff_not_dvd S hS hpS hu

end Valuation

/-! ### NoCM: the fibre of `X⁶ → X*` over `t(u)` (A10; rv-h-cm §2.4, §7.2 step 3)

In Elkies' model `ℚ(X⁶) = ℚ(t)(y₁, y₂)`, `y₁² = −t`, `y₂² = 3(t − 1)` (rv-h-cm §2.3; `w₂`, `w₆`,
`w₃` negate `y₂`, `y₁`, both). Over `t(u)` the four points are `(±i h₁, ±i h₂)` with
`h₁ = H/G³`, `h₂ = 540F/G³`, both nonzero: a free `W`-orbit, with coordinates in `ℚ(i)`, no
coordinate real (so the residue field is not `ℚ`), and complex conjugation acting as `w₃`. -/

open Complex in
/-- The fibre over `t(u)`: exactly the four points `(±i h₁, ±i h₂)`. -/
theorem fibre_iff (u : ℚ) (Y₁ Y₂ : ℂ) :
    (Y₁ ^ 2 = -((tq u : ℚ) : ℂ) ∧ Y₂ ^ 2 = 3 * (((tq u : ℚ) : ℂ) - 1)) ↔
    (Y₁ = I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ) ∨ Y₁ = -(I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ))) ∧
    (Y₂ = I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ) ∨ Y₂ = -(I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ))) :=
        by
  have hG := Gq_ne_zero u
  have e1 : -((tq u : ℚ) : ℂ) = (I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ)) ^ 2 := by
    rw [t_eq]; push_cast; rw [mul_pow, I_sq]; ring
  have e2 : 3 * (((tq u : ℚ) : ℂ) - 1) = (I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ)) ^ 2 := by
    have := t_sub_one u
    rw [show ((tq u : ℚ) : ℂ) - 1 = ((tq u - 1 : ℚ) : ℂ) by push_cast; ring, this]
    push_cast; rw [mul_pow, I_sq]; ring
  rw [e1, e2, sq_eq_sq_iff_eq_or_eq_neg, sq_eq_sq_iff_eq_or_eq_neg]

theorem h₁_ne_zero (u : ℚ) : Hq u / Gq u ^ 3 ≠ 0 :=
  div_ne_zero (Hq_ne_zero u) (pow_ne_zero _ (Gq_ne_zero u))

theorem h₂_ne_zero {u : ℚ} (hu : u ∉ contactSet) : 540 * Fq u / Gq u ^ 3 ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) (Fq_ne_zero hu)) (pow_ne_zero _ (Gq_ne_zero u))

open Complex in
/-- The four points are pairwise distinct, `W` acts freely (no point has a zero coordinate),
no point has a real (a fortiori rational) coordinate, and complex conjugation acts as `w₃`
(negates both coordinates). -/
theorem fibre_free {u : ℚ} (hu : u ∉ contactSet) (Y₁ Y₂ : ℂ)
    (h : Y₁ ^ 2 = -((tq u : ℚ) : ℂ) ∧ Y₂ ^ 2 = 3 * (((tq u : ℚ) : ℂ) - 1)) :
    Y₁ ≠ -Y₁ ∧ Y₂ ≠ -Y₂ ∧ Y₁.im ≠ 0 ∧ Y₂.im ≠ 0 ∧
      (starRingEnd ℂ Y₁ = -Y₁ ∧ starRingEnd ℂ Y₂ = -Y₂) := by
  have n1 := h₁_ne_zero u
  have n2 := h₂_ne_zero hu
  obtain ⟨h1, h2⟩ := (fibre_iff u Y₁ Y₂).mp h
  have k1 : Y₁.re = 0 ∧ Y₁.im ≠ 0 := by
    clear h h2
    generalize Hq u / Gq u ^ 3 = r at h1 n1
    rcases h1 with rfl | rfl <;> simp [n1]
  have k2 : Y₂.re = 0 ∧ Y₂.im ≠ 0 := by
    clear h h1 k1
    generalize 540 * Fq u / Gq u ^ 3 = r at h2 n2
    rcases h2 with rfl | rfl <;> simp [n2]
  refine ⟨fun e => k1.2 ?_, fun e => k2.2 ?_, k1.2, k2.2, ?_, ?_⟩
  · have := congrArg Complex.im e; simp at this; linarith
  · have := congrArg Complex.im e; simp at this; linarith
  · apply Complex.ext <;> simp [k1.1]
  · apply Complex.ext <;> simp [k2.1]

end GlueRepo.PR

