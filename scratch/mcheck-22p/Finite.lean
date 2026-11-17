import Mathlib

/-!
# mcheck-22p: finite facts used in the proof of `prop:fixed-prime-pattern` (tex L1299-1704)
-/

namespace MCheck22P.Finite

/-- `𝓑`. -/
def B : List ℤ := [0, -15, -20, -24, -30, -60, 1]

/-- A form `c₁u₁ + c₂u₂ + (α A + β) v`, recorded as `(c₁, c₂, α, β)`, so that `A` stays symbolic. -/
def forms : List (ℤ × ℤ × ℤ × ℤ) :=
  (0, 0, 0, 1) :: (B.map fun b => (1, 0, 0, -b)) ++ (B.map fun b => (0, 1, 0, -b)) ++
    (B.map fun b => (-1, -1, 1, -b))

theorem forms_length : forms.length = 22 := by decide

/-- tex L1305: each form has a coefficient `1` or `-1` (among `c₁, c₂`, or the `v`-coefficient
when it does not involve `A`). -/
theorem unit_coeff : ∀ f ∈ forms, f.1 = 1 ∨ f.1 = -1 ∨ f.2.1 = 1 ∨ f.2.1 = -1 ∨
    (f.2.2.1 = 0 ∧ (f.2.2.2 = 1 ∨ f.2.2.2 = -1)) := by decide

/-- The three `2×2` minors of two forms, as `m₀ + m₁ A`, recorded `(m₀, m₁)`. The minor on the
first two columns, then columns `(1,3)`, `(2,3)`. -/
def minors (f g : ℤ × ℤ × ℤ × ℤ) : List (ℤ × ℤ) :=
  [(f.1 * g.2.1 - f.2.1 * g.1, 0),
   (f.1 * g.2.2.2 - f.2.2.2 * g.1, f.1 * g.2.2.1 - f.2.2.1 * g.1),
   (f.2.1 * g.2.2.2 - f.2.2.2 * g.2.1, f.2.1 * g.2.2.1 - f.2.2.1 * g.2.1)]

/-- tex L1306-1313: for every pair of distinct forms, some minor is independent of `A`, nonzero,
and of absolute value at most `61`. Hence every pair is linearly independent over `ℚ` and over
`𝔽_q` for every prime `q > 61` (in particular `q > 324`), for every integer `A`. -/
theorem pairwise_minor : ∀ i j : Fin 22, i ≠ j →
    ∃ m ∈ minors (forms.get ⟨i, by rw [forms_length]; exact i.2⟩)
        (forms.get ⟨j, by rw [forms_length]; exact j.2⟩),
      m.2 = 0 ∧ m.1 ≠ 0 ∧ m.1.natAbs ≤ 61 := by decide

/-- The bound `61` is attained (`1 - (-60)`): the contact differences. -/
theorem contact_diffs : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → (b - b').natAbs ≤ 61 ∧ 0 < (b - b').natAbs := by
  decide

/-- tex L1557-1558: `N(75 - 53√2) = 7`. -/
theorem norm_d : (75 : ℤ) ^ 2 - 2 * 53 ^ 2 = 7 := by norm_num

/-- tex L1555-1557: `3` is not a square mod `7`, so `p ≡ 3 (mod 7)`, `p ≡ 1 (mod 4)` gives
`(7/p) = (p/7) = -1`; and `2` is a square mod every `p ≡ 1 (mod 8)` (here: supplementary law). -/
theorem three_nonsq_mod7 : ∀ x : ZMod 7, x ^ 2 ≠ 3 := by decide

theorem seven_nonsq_of_three_mod7 {p : ℕ} [Fact p.Prime] (h8 : p % 8 = 1) (h7 : p % 7 = 3) :
    ¬ IsSquare (7 : ZMod p) := by
  have h7f : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have key := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 7) (by omega)
    (by norm_num)
  have e : ((7 : ℕ) : ZMod p) = 7 := by norm_num
  rw [e] at key
  rw [key]
  rintro ⟨y, hy⟩
  have : ((p : ZMod 7)) = 3 := by
    have : p % 7 = (3 : ℕ) := h7
    rw [← ZMod.natCast_mod, this]; rfl
  rw [this] at hy
  exact three_nonsq_mod7 y (by rw [hy]; ring)

theorem two_sq_of_one_mod8 {p : ℕ} [Fact p.Prime] (h8 : p % 8 = 1) : IsSquare (2 : ZMod p) := by
  rw [ZMod.exists_sq_eq_two_iff (by omega)]; omega

/-- tex L1321-1323, L1349, L1386-1389: the elementary inequalities. -/
theorem ineqs : (22 : ℚ) / 2 ^ 5 < 1 ∧ (∀ h : ℕ, 324 < h → 42 * h < h ^ 2) ∧
    (∀ q : ℕ, 324 < q → 44 < q) := by
  refine ⟨by norm_num, fun h hh => by nlinarith, fun q hq => by omega⟩

/-- `W = 4 ∏_{p ≤ 324} p`. -/
def W : ℕ := 4 * ∏ p ∈ (Finset.range 325).filter Nat.Prime, p

theorem W_pos : 0 < W := by
  unfold W; refine Nat.mul_pos (by norm_num) (Finset.prod_pos fun p hp => ?_)
  exact (Finset.mem_filter.1 hp).2.pos

/-- tex L239, L1339-1342: Dirichlet's theorem (Mathlib) makes every unit class mod `W` contain
infinitely many primes `> 324`, so `𝓗` is well defined with 22 primes per class, and 22 pairwise
distinct `h_ν` can be chosen in any assignment of classes. -/
theorem class_infinite {r : ℕ} (hr : Nat.Coprime r W) :
    {p : ℕ | p.Prime ∧ 324 < p ∧ p ≡ r [MOD W]}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hpa, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max a 324) W_pos.ne' hr
  exact ⟨p, ⟨hp, lt_of_le_of_lt (le_max_right _ _) hpa, hmod⟩,
    lt_of_le_of_lt (le_max_left _ _) hpa⟩

/-- Every prime `> 324` is a unit mod `W`. -/
theorem prime_coprime_W {p : ℕ} (hp : p.Prime) (h : 324 < p) : Nat.Coprime p W := by
  unfold W
  refine Nat.Coprime.mul_right ?_ ?_
  · exact (Nat.coprime_primes hp Nat.prime_two |>.2 (by omega)).pow_right 2 |>.symm.symm |>
      fun h' => by simpa using h'
  · refine Nat.Coprime.prod_right fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    exact (Nat.coprime_primes hp hq2).2 (by simp at hq1; omega)

end MCheck22P.Finite
