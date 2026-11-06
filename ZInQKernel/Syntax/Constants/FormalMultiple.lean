import ZInQKernel.Model.Field.Codes

/-!
# The least formal multiple

Blueprint: `syntax/constants/least-formal-multiple.md`.

Every `u ∈ K₀` has a unique normalized representation `u = (a + b s)/c` with `a, b ∈ ℤ`,
`c ∈ ℕ`, `c > 0` and `gcd(a, b, c) = 1` (`normalizedRep`, with the existence and uniqueness
statements `normalizedRep_isNormalizedRep` and `IsNormalizedRep.eq_normalizedRep`). For a point
`Q` of `E(K₀)`, `ξ(Q) = 1/x(Q)` if `Q ≠ O` and `x(Q) ≠ 0` and `ξ(Q) = 0` otherwise (Lean's
`0⁻¹ = 0` gives the second convention at points with `x = 0`).

`LFM(N)` is the least `m ≥ 1` such that the normalized representation `(a, b, c)` of
`ξ([m]P₀)` satisfies `N⁴ ∣ a`, `N⁴ ∣ b` and `gcd(c, N) = 1`, and `0` if there is none
(`sInf ∅ = 0`). It is never evaluated.
-/

namespace ZInQ.Syntax

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The normalized representation -/

/-- `(a, b, c)` is a normalized representation of `u`: `c > 0`, `gcd(a, b, c) = 1` and
`u = (a + b s)/c`. -/
def IsNormalizedRep (u : K0) (a b : ℤ) (c : ℕ) : Prop :=
  0 < c ∧ Nat.gcd (Int.gcd a b) c = 1 ∧ u = ((a : K0) + (b : K0) * sqrt2) / (c : K0)

/-- The normalized representation: `c = lcm(den u₀, den u₁)` and `a = u₀ c`, `b = u₁ c`. -/
def normalizedRep (u : K0) : ℤ × ℤ × ℕ :=
  (u.re.num * ((Nat.lcm u.re.den u.im.den / u.re.den : ℕ) : ℤ),
    u.im.num * ((Nat.lcm u.re.den u.im.den / u.im.den : ℕ) : ℤ),
    Nat.lcm u.re.den u.im.den)

theorem div_eq_iff_components {u : K0} {a b : ℤ} {c : ℕ} (hc : 0 < c) :
    u = ((a : K0) + (b : K0) * sqrt2) / (c : K0) ↔ u.re = a / c ∧ u.im = b / c := by
  have hc' : (c : K0) ≠ 0 := by exact_mod_cast hc.ne'
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [eq_div_iff hc', K0.ext_iff', eq_div_iff hcq, eq_div_iff hcq]
  simp [sqrt2]

/-- If `q = a / c` with `c > 0`, the reduced denominator of `q` divides `c`. -/
theorem den_dvd_of_eq_div {q : ℚ} {a : ℤ} {c : ℕ} (h : q = a / c) : q.den ∣ c := by
  have := Rat.den_dvd a c
  rw [Rat.divInt_eq_div, Int.cast_natCast, ← h] at this
  exact_mod_cast this

theorem normalizedRep_pos (u : K0) : 0 < (normalizedRep u).2.2 :=
  Nat.lcm_pos u.re.den_pos u.im.den_pos

/-- Clearing a denominator: if `den q ∣ c` and `c > 0` then `q = (num q · (c / den q)) / c`. -/
theorem eq_num_mul_div_den_div {q : ℚ} {c : ℕ} (hc : 0 < c) (hd : q.den ∣ c) :
    q = (q.num * ((c / q.den : ℕ) : ℤ) : ℤ) / (c : ℚ) := by
  obtain ⟨t, rfl⟩ := hd
  have ht : (t : ℚ) ≠ 0 := by
    have : t ≠ 0 := by rintro rfl; simp at hc
    exact_mod_cast this
  rw [Nat.mul_div_cancel_left _ q.den_pos]
  push_cast
  rw [mul_div_mul_right _ _ ht, Rat.num_div_den]

theorem normalizedRep_re (u : K0) :
    u.re = (normalizedRep u).1 / ((normalizedRep u).2.2 : ℚ) :=
  eq_num_mul_div_den_div (normalizedRep_pos u) (Nat.dvd_lcm_left _ _)

theorem normalizedRep_im (u : K0) :
    u.im = (normalizedRep u).2.1 / ((normalizedRep u).2.2 : ℚ) :=
  eq_num_mul_div_den_div (normalizedRep_pos u) (Nat.dvd_lcm_right _ _)

/-- Any representation `u = (a + b s)/c` has `lcm(den u₀, den u₁) ∣ c`. -/
theorem normalizedRep_dvd {u : K0} {a b : ℤ} {c : ℕ} (hre : u.re = a / c) (him : u.im = b / c) :
    (normalizedRep u).2.2 ∣ c :=
  Nat.lcm_dvd (den_dvd_of_eq_div hre) (den_dvd_of_eq_div him)

/-- Two representations `a/(c t) = a'/c` have `a = a' t`. -/
theorem eq_mul_of_div_eq_div {a a' : ℤ} {c t : ℕ} (hct : 0 < c * t)
    (h : (a : ℚ) / ((c * t : ℕ) : ℚ) = a' / c) : a = a' * t := by
  have hc : (c : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hct).ne'
  have ht : (t : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hct).ne'
  push_cast at h
  rw [div_eq_div_iff (mul_ne_zero hc ht) hc] at h
  have : (a : ℚ) = a' * t := mul_right_cancel₀ hc (by rw [h]; ring)
  exact_mod_cast this

theorem dvd_gcd_three {t : ℕ} {a b : ℤ} {c : ℕ} (ha : (t : ℤ) ∣ a) (hb : (t : ℤ) ∣ b)
    (hc : t ∣ c) : t ∣ Nat.gcd (Int.gcd a b) c :=
  Nat.dvd_gcd (Int.dvd_gcd ha hb) hc

/-- Existence: `normalizedRep u` is a normalized representation of `u`. -/
theorem normalizedRep_isNormalizedRep (u : K0) :
    IsNormalizedRep u (normalizedRep u).1 (normalizedRep u).2.1 (normalizedRep u).2.2 := by
  refine ⟨normalizedRep_pos u, ?_, (div_eq_iff_components (normalizedRep_pos u)).2
    ⟨normalizedRep_re u, normalizedRep_im u⟩⟩
  have hc := normalizedRep_pos u
  have hre := normalizedRep_re u
  have him := normalizedRep_im u
  set a := (normalizedRep u).1
  set b := (normalizedRep u).2.1
  set c := (normalizedRep u).2.2
  set g := Nat.gcd (Int.gcd a b) c
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ hc
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  obtain ⟨c₁, hc₁⟩ : g ∣ c := Nat.gcd_dvd_right _ _
  obtain ⟨a₁, ha₁⟩ : (g : ℤ) ∣ a :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_left _ _)
  obtain ⟨b₁, hb₁⟩ : (g : ℤ) ∣ b :=
    (Int.natCast_dvd_natCast.2 (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_right _ _)
  have hre₁ : u.re = a₁ / c₁ := by
    rw [hre, ha₁, hc₁]; push_cast; rw [mul_div_mul_left _ _ hgq]
  have him₁ : u.im = b₁ / c₁ := by
    rw [him, hb₁, hc₁]; push_cast; rw [mul_div_mul_left _ _ hgq]
  have hc₁pos : 0 < c₁ := Nat.pos_of_mul_pos_left (hc₁ ▸ hc)
  have hle : g * c₁ ≤ 1 * c₁ := by
    rw [one_mul, ← hc₁]; exact Nat.le_of_dvd hc₁pos (normalizedRep_dvd hre₁ him₁)
  have := Nat.le_of_mul_le_mul_right hle hc₁pos
  omega

/-- Uniqueness: every normalized representation of `u` is `normalizedRep u`. -/
theorem IsNormalizedRep.eq_normalizedRep {u : K0} {a b : ℤ} {c : ℕ}
    (h : IsNormalizedRep u a b c) : (a, b, c) = normalizedRep u := by
  obtain ⟨hc, hg, hu⟩ := h
  obtain ⟨hre, him⟩ := (div_eq_iff_components hc).1 hu
  obtain ⟨t, rfl⟩ := normalizedRep_dvd hre him
  have ha := eq_mul_of_div_eq_div hc (hre.symm.trans (normalizedRep_re u))
  have hb := eq_mul_of_div_eq_div hc (him.symm.trans (normalizedRep_im u))
  have ht : t ∣ Nat.gcd (Int.gcd a b) ((normalizedRep u).2.2 * t) :=
    dvd_gcd_three (ha ▸ Dvd.intro_left _ rfl) (hb ▸ Dvd.intro_left _ rfl) (Dvd.intro_left _ rfl)
  rw [hg, Nat.dvd_one] at ht
  subst ht
  simp only [Nat.cast_one, mul_one] at ha hb
  rw [ha, hb, mul_one]

theorem isNormalizedRep_iff {u : K0} {a b : ℤ} {c : ℕ} :
    IsNormalizedRep u a b c ↔ (a, b, c) = normalizedRep u := by
  refine ⟨IsNormalizedRep.eq_normalizedRep, fun h => ?_⟩
  rw [show a = _ from congrArg Prod.fst h, show b = _ from congrArg (·.2.1) h,
    show c = _ from congrArg (·.2.2) h]
  exact normalizedRep_isNormalizedRep u

/-- The normalized representation of `0` is `(0, 0, 1)`. -/
theorem normalizedRep_zero : normalizedRep 0 = (0, 0, 1) := rfl

/-! ### The least formal multiple -/

/-- `ξ(Q) = 1/x(Q)` for an affine point `Q` (`0` if `x(Q) = 0`), and `ξ(O) = 0`. -/
noncomputable def xi : genCurve.toAffine.Point → K0
  | .zero => 0
  | .some x _ _ => x⁻¹

@[simp] theorem xi_zero : xi 0 = 0 := rfl

@[simp] theorem xi_some {x y : K0} (h : genCurve.toAffine.Nonsingular x y) :
    xi (.some x y h) = x⁻¹ := rfl

/-- The condition defining `LFM(N)` at the index `m`: the normalized representation
`(a, b, c)` of `ξ([m]P₀)` has `N⁴ ∣ a`, `N⁴ ∣ b` and `gcd(c, N) = 1`. -/
def FormalCondition (N m : ℕ) : Prop :=
  (N : ℤ) ^ 4 ∣ (normalizedRep (xi (m • genP0))).1 ∧
    (N : ℤ) ^ 4 ∣ (normalizedRep (xi (m • genP0))).2.1 ∧
    Nat.Coprime (normalizedRep (xi (m • genP0))).2.2 N

/-- `LFM(N)`: the least `m ≥ 1` satisfying the formal condition, `0` if there is none. -/
noncomputable def leastFormalMultiple (N : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ FormalCondition N m}

/-- If no index succeeds, `LFM(N) = 0`. -/
theorem leastFormalMultiple_eq_zero {N : ℕ} (h : ¬∃ m, 1 ≤ m ∧ FormalCondition N m) :
    leastFormalMultiple N = 0 := by
  rw [leastFormalMultiple, Nat.sInf_eq_zero]
  right
  exact Set.eq_empty_of_forall_notMem fun m hm => h ⟨m, hm⟩

/-- If some index succeeds, `LFM(N)` is the least one. -/
theorem leastFormalMultiple_spec {N : ℕ} (h : ∃ m, 1 ≤ m ∧ FormalCondition N m) :
    1 ≤ leastFormalMultiple N ∧ FormalCondition N (leastFormalMultiple N) ∧
      ∀ m, 1 ≤ m → FormalCondition N m → leastFormalMultiple N ≤ m :=
  ⟨(Nat.sInf_mem h).1, (Nat.sInf_mem h).2, fun _ h₁ h₂ => Nat.sInf_le ⟨h₁, h₂⟩⟩

/-- A successful index `m ≥ 1` below which no positive index succeeds is `LFM(N)`. -/
theorem leastFormalMultiple_eq_of {N m : ℕ} (hm : 1 ≤ m) (hc : FormalCondition N m)
    (hmin : ∀ m', 1 ≤ m' → m' < m → ¬FormalCondition N m') : leastFormalMultiple N = m := by
  obtain ⟨h₁, h₂, h₃⟩ := leastFormalMultiple_spec ⟨m, hm, hc⟩
  refine le_antisymm (h₃ m hm hc) (not_lt.1 fun hlt => hmin _ h₁ hlt h₂)

theorem leastFormalMultiple_pos_iff {N : ℕ} :
    0 < leastFormalMultiple N ↔ ∃ m, 1 ≤ m ∧ FormalCondition N m := by
  refine ⟨fun h => ?_, fun h => (leastFormalMultiple_spec h).1⟩
  by_contra hn
  rw [leastFormalMultiple_eq_zero hn] at h
  exact lt_irrefl _ h

/- The least formal multiple is never evaluated: from here on the elaborator may not unfold
it. -/
attribute [irreducible] leastFormalMultiple

end ZInQ.Syntax
