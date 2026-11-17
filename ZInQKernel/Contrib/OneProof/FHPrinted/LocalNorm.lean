import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Local components of quadratic idele class characters of `ℚ` (task fh-printed)

For a squarefree integer `d` the quadratic idele class character `χ_d` of `ℚ(√d)` has local
components `χ_{d,v} : ℚ_v^× → {±1}` with kernel the norm group `N(ℚ_v(√d)^×)` (local class field
theory); `χ_{d,v}(x)` is the Hilbert symbol `(d, x)_v`. This file works with the norm form
directly (`IsLocalNorm K d x`: `x = y² − d z²` in `K`) and proves, from Mathlib only (Hensel's
lemma, the finite-field Chevalley–Warning lemma for two quadrics, quadratic reciprocity):

* the local conditions of Friedberg–Hoffstein read as squares:
  `isSquare_div_of_localNorm_iff` (odd `p ∤ D₀`), `isSquare_div_two_of_localNorm_iff` (`p = 2`,
  `D₀ ≡ 1 mod 4`, which also gives `D ≡ 1 mod 4`), `pos_mul_of_real_iff` (`v = ∞`); conversely
  equal square classes give equal norm groups (`isLocalNorm_iff_of_isSquare_div`);
* the Dirichlet coefficients of `χ_d` built from its local components (`charAtPrime`,
  `idelicChar`: `χ_d(p) = χ_{d,p}(p)` at unramified `p`, `0` at ramified `p`) are the Jacobi
  symbol `(n / |d|)` for `d ≡ 1 (mod 4)` (`idelicChar_eq_jacobiSym`), and `χ_d(2) = 0` for
  `d ≡ 2, 3 (mod 4)` (`charAtPrime_two_of_ramified`).

The non-norm statements are proved by descent on the norm form (`not_isLocalNorm_of_descent`):
`p` is not a norm from the unramified extension (`d` a nonsquare unit), a nonsquare unit is not a
norm from a ramified extension (`p ∥ d`), and at `2`: `2` for `d ≡ 5 (8)`, `−1` for `d ≡ 3 (4)`,
`5` for `d ≡ 2 (4)`. Every unit is a norm from an unramified extension (`isLocalNorm_unit`,
`isLocalNorm_two_unit`).
-/

namespace ZInQ.FHPrinted

open PadicInt Polynomial

/-- `x` is a norm from `K(√d)`: `x = y² − d z²` with `y, z ∈ K`. -/
def IsLocalNorm (K : Type*) [Field K] (d : ℤ) (x : K) : Prop :=
  ∃ y z : K, x = y ^ 2 - d * z ^ 2

section General

variable {K : Type*} [Field K] {d : ℤ}

theorem IsLocalNorm.mul {x x' : K} (h : IsLocalNorm K d x) (h' : IsLocalNorm K d x') :
    IsLocalNorm K d (x * x') := by
  obtain ⟨y, z, rfl⟩ := h
  obtain ⟨y', z', rfl⟩ := h'
  exact ⟨y * y' + d * z * z', y * z' + y' * z, by ring⟩

theorem IsLocalNorm.sq_mul {x : K} (c : K) (h : IsLocalNorm K d x) :
    IsLocalNorm K d (c ^ 2 * x) := by
  obtain ⟨y, z, rfl⟩ := h
  exact ⟨c * y, c * z, by ring⟩

theorem isLocalNorm_sq (c : K) : IsLocalNorm K d (c ^ 2) := ⟨c, 0, by ring⟩

theorem isLocalNorm_neg_self : IsLocalNorm K d (-(d : K)) := ⟨0, 1, by ring⟩

theorem isLocalNorm_of_mul_eq_sq {u r W : K} (hr0 : r ≠ 0) (h : u * r = W ^ 2)
    (hr : IsLocalNorm K d r) : IsLocalNorm K d u := by
  have e : u = (W / r) ^ 2 * r := by field_simp; linear_combination h
  rw [e]; exact hr.sq_mul _

theorem isLocalNorm_of_eq_sq (h2 : (2 : K) ≠ 0) {w : K} (hw0 : w ≠ 0) (hw : (d : K) = w ^ 2)
    (x : K) : IsLocalNorm K d x :=
  ⟨(x + 1) / 2, (x - 1) / (2 * w), by rw [hw]; field_simp; ring⟩

/-- Equal square classes give equal norm groups: if `d = D c²` with `c ≠ 0`, then `K(√d)` and
`K(√D)` have the same norms. -/
theorem isLocalNorm_iff_of_eq_mul_sq {D : ℤ} {c : K} (hc : c ≠ 0) (h : (d : K) = D * c ^ 2)
    (x : K) : IsLocalNorm K d x ↔ IsLocalNorm K D x := by
  constructor
  · rintro ⟨y, z, rfl⟩; exact ⟨y, c * z, by rw [h]; ring⟩
  · rintro ⟨y, z, rfl⟩; exact ⟨y, z / c, by rw [h]; field_simp⟩

theorem isLocalNorm_iff_of_isSquare_div {D : ℤ} (hd : (d : K) ≠ 0) (hD : (D : K) ≠ 0)
    (h : IsSquare ((d : K) / D)) (x : K) : IsLocalNorm K d x ↔ IsLocalNorm K D x := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero, div_eq_zero_iff] at hc
    rcases hc with h0 | h0
    · exact hd h0
    · exact hD h0
  refine isLocalNorm_iff_of_eq_mul_sq hc0 ?_ x
  rw [div_eq_iff hD] at hc
  rw [hc]; ring

end General

section Hensel

variable {p : ℕ} [hp : Fact p.Prime]

theorem mem_maximalIdeal_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) :
    x ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
  rw [← ker_toZMod]; exact h

theorem norm_lt_one_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) : ‖x‖ < 1 :=
  mem_nonunits.mp (mem_maximalIdeal_of_toZMod h)

theorem dvd_of_toZMod {x : ℤ_[p]} (h : toZMod x = 0) : (p : ℤ_[p]) ∣ x :=
  (norm_lt_one_iff_dvd x).mp (norm_lt_one_of_toZMod h)

theorem isUnit_of_toZMod {x : ℤ_[p]} (h : toZMod x ≠ 0) : IsUnit x := by
  by_contra hx
  exact h (by rw [← RingHom.mem_ker, ker_toZMod]; exact hx)

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

/-- **Hensel**: a `p`-adic integer (`p` odd) that is a nonzero square modulo `p` is a square. -/
theorem isSquare_of_toZMod (hp2 : p ≠ 2) {u : ℤ_[p]} {c : ZMod p} (hc : c ≠ 0)
    (hu : toZMod u = c ^ 2) : IsSquare u := by
  set a : ℤ_[p] := ((c.val : ℕ) : ℤ_[p]) with ha_def
  have ha : toZMod a = c := by simp [a]
  let F : Polynomial ℤ_[p] := X ^ 2 - C u
  have hF : F.aeval a = a ^ 2 - u := by simp [F]
  have hF' : F.derivative.aeval a = 2 * a := by simp [F]; norm_num
  have h1 : ‖F.aeval a‖ < 1 := by
    rw [hF]; apply norm_lt_one_of_toZMod; simp [ha, hu]
  have h2 : ‖F.derivative.aeval a‖ = 1 := by
    rw [hF', ← PadicInt.isUnit_iff]; apply isUnit_of_toZMod
    rw [map_mul, ha, map_ofNat]
    exact mul_ne_zero (two_ne_zero_zmod hp2) hc
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := a) (by rw [h2]; simpa using h1)
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  linear_combination -this

/-- **Hensel at `2`**: a `2`-adic integer `≡ 1 (mod 8)` is a square. -/
theorem isSquare_of_toZModPow_three {u : ℤ_[2]} (hu : toZModPow 3 u = 1) : IsSquare u := by
  let F : Polynomial ℤ_[2] := X ^ 2 - C u
  have h1 : ‖F.aeval (1 : ℤ_[2])‖ ≤ ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℤ)) := by
    rw [norm_le_pow_iff_mem_span_pow, ← ker_toZModPow, RingHom.mem_ker]
    simp [F, hu]
  have hd : F.derivative.aeval (1 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by simp [F]; norm_num
  have h2 : ‖F.derivative.aeval (1 : ℤ_[2])‖ = ((2 : ℕ) : ℝ)⁻¹ := by
    rw [hd]; exact PadicInt.norm_p
  obtain ⟨z, hz, -⟩ := hensels_lemma (F := F) (a := 1) (by
    rw [h2]
    refine lt_of_le_of_lt h1 ?_
    norm_num)
  refine ⟨z, ?_⟩
  have : z ^ 2 - u = 0 := by simpa [F] using hz
  linear_combination -this

/-- An integer prime to `p` (odd) that is a square modulo `p` is a nonzero square in `ℚ_p`. -/
theorem exists_sq_of_int (hp2 : p ≠ 2) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a)
    (hsq : IsSquare (a : ZMod p)) : ∃ w : ℚ_[p], w ≠ 0 ∧ (a : ℚ_[p]) = w ^ 2 := by
  obtain ⟨c, hc⟩ := hsq
  have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact ha0 hc
  obtain ⟨z, hz⟩ := isSquare_of_toZMod hp2 hc0 (u := (a : ℤ_[p])) (by rw [map_intCast, hc]; ring)
  have hz' : (a : ℚ_[p]) = (z : ℚ_[p]) ^ 2 := by
    rw [← PadicInt.coe_intCast, hz]; push_cast; ring
  refine ⟨z, fun h0 => ?_, hz'⟩
  rw [h0] at hz'
  have : (a : ℚ_[p]) = 0 := by simpa using hz'
  exact ha (by rw [Int.cast_eq_zero.mp this]; exact dvd_zero _)

/-- An integer `≡ 1 (mod 8)` is a nonzero square in `ℚ_2`. -/
theorem exists_sq_of_int_two {a : ℤ} (ha : a % 8 = 1) :
    ∃ w : ℚ_[2], w ≠ 0 ∧ (a : ℚ_[2]) = w ^ 2 := by
  have h8 : (a : ZMod (2 ^ 3)) = 1 := by
    have e : a = 8 * (a / 8) + 1 := by omega
    rw [e]; push_cast
    have : (8 : ZMod (2 ^ 3)) = 0 := by decide
    rw [this]; ring
  obtain ⟨z, hz⟩ := isSquare_of_toZModPow_three (u := (a : ℤ_[2])) (by rw [map_intCast, h8])
  have hz' : (a : ℚ_[2]) = (z : ℚ_[2]) ^ 2 := by
    rw [← PadicInt.coe_intCast, hz]; push_cast; ring
  refine ⟨z, fun h0 => ?_, hz'⟩
  rw [h0] at hz'
  have : (a : ℚ_[2]) = 0 := by simpa using hz'
  have := Int.cast_eq_zero.mp this
  omega

end Hensel


section Descent

variable {p : ℕ} [hp : Fact p.Prime]

theorem p_ne_zero_padicInt : (p : ℤ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero

/-- **Descent for the norm form.** If `x ∈ ℤ_p` is not `Y² − d Z²` with `Y, Z ∈ ℤ_p`, and every
representation of `p^{2(k+1)} x` has `p ∣ Y`, `p ∣ Z`, then `x` is not a norm from `ℚ_p(√d)`. -/
theorem not_isLocalNorm_of_descent {d : ℤ} {x : ℤ_[p]}
    (h0 : ∀ Y Z : ℤ_[p], x ≠ Y ^ 2 - (d : ℤ_[p]) * Z ^ 2)
    (hstep : ∀ (k : ℕ) (Y Z : ℤ_[p]), (p : ℤ_[p]) ^ (2 * (k + 1)) * x = Y ^ 2 - (d : ℤ_[p]) * Z ^ 2 →
      (p : ℤ_[p]) ∣ Y ∧ (p : ℤ_[p]) ∣ Z) :
    ¬ IsLocalNorm ℚ_[p] d (x : ℚ_[p]) := by
  have key : ∀ k : ℕ, ∀ Y Z : ℤ_[p], (p : ℤ_[p]) ^ (2 * k) * x ≠ Y ^ 2 - (d : ℤ_[p]) * Z ^ 2 := by
    intro k
    induction k with
    | zero => intro Y Z; simpa using h0 Y Z
    | succ k ih =>
      intro Y Z hYZ
      obtain ⟨⟨Y', rfl⟩, ⟨Z', rfl⟩⟩ := hstep k Y Z hYZ
      apply ih Y' Z'
      have hp0 : (p : ℤ_[p]) ^ 2 ≠ 0 := pow_ne_zero 2 p_ne_zero_padicInt
      apply mul_left_cancel₀ hp0
      have e : (p : ℤ_[p]) ^ 2 * ((p : ℤ_[p]) ^ (2 * k) * x) =
          (p : ℤ_[p]) ^ (2 * (k + 1)) * x := by ring
      rw [e, hYZ]; ring
  rintro ⟨y, z, hyz⟩
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max ‖y‖ ‖z‖)
    (by exact_mod_cast hp.out.one_lt : (1 : ℝ) < p)
  have hle : ∀ w : ℚ_[p], ‖w‖ ≤ max ‖y‖ ‖z‖ → ‖(p : ℚ_[p]) ^ k * w‖ ≤ 1 := by
    intro w hw
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (by exact_mod_cast hp.out.pos) k
    rw [inv_mul_le_iff₀ hpk, mul_one]; linarith
  apply key k ⟨(p : ℚ_[p]) ^ k * y, hle y (le_max_left _ _)⟩
    ⟨(p : ℚ_[p]) ^ k * z, hle z (le_max_right _ _)⟩
  apply PadicInt.ext
  simp only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, PadicInt.coe_sub,
    PadicInt.coe_intCast]
  change (p : ℚ_[p]) ^ (2 * k) * (x : ℚ_[p]) =
    ((p : ℚ_[p]) ^ k * y) ^ 2 - (d : ℚ_[p]) * ((p : ℚ_[p]) ^ k * z) ^ 2
  rw [hyz]; ring

/-- Modulo `p`: if `d` is not a square mod `p`, `Y² ≡ d Z²` forces `Y ≡ Z ≡ 0`. -/
theorem toZMod_eq_zero_of_nonsquare {d : ℤ} (hd : ¬ IsSquare (d : ZMod p)) {Y Z : ℤ_[p]}
    (h : toZMod (Y ^ 2 - (d : ℤ_[p]) * Z ^ 2) = 0) : toZMod Y = 0 ∧ toZMod Z = 0 := by
  simp only [map_sub, map_mul, map_pow, map_intCast] at h
  by_cases hZ : toZMod Z = 0
  · rw [hZ] at h
    refine ⟨?_, hZ⟩
    have : toZMod Y ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · exfalso; apply hd
    refine ⟨toZMod Y / toZMod Z, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hZ hZ)]
    linear_combination -h

theorem toZMod_p : toZMod (p : ℤ_[p]) = 0 := by simp

/-- **`p` is not a norm from the unramified quadratic extension**: if `d` is not a square
modulo `p`, then `p ∉ N(ℚ_p(√d)^×)`. -/
theorem not_isLocalNorm_p {d : ℤ} (hd : ¬ IsSquare (d : ZMod p)) :
    ¬ IsLocalNorm ℚ_[p] d (p : ℚ_[p]) := by
  rw [← PadicInt.coe_natCast]
  apply not_isLocalNorm_of_descent
  · intro Y Z h
    obtain ⟨hY, hZ⟩ := toZMod_eq_zero_of_nonsquare hd (Y := Y) (Z := Z) (by rw [← h]; simp)
    obtain ⟨Y', rfl⟩ := dvd_of_toZMod hY
    obtain ⟨Z', rfl⟩ := dvd_of_toZMod hZ
    have h1 : (p : ℤ_[p]) * 1 = p * (p * (Y' ^ 2 - (d : ℤ_[p]) * Z' ^ 2)) := by
      linear_combination h
    have h2 := congrArg toZMod (mul_left_cancel₀ p_ne_zero_padicInt h1)
    simp at h2
  · intro k Y Z h
    obtain ⟨hY, hZ⟩ := toZMod_eq_zero_of_nonsquare hd (Y := Y) (Z := Z) (by
      rw [← h, map_mul, toZMod_p, mul_zero])
    exact ⟨dvd_of_toZMod hY, dvd_of_toZMod hZ⟩

/-- **A nonsquare unit is not a norm from a ramified quadratic extension**: if `p ∥ d` and `u`
is not a square modulo `p`, then `u ∉ N(ℚ_p(√d)^×)`. -/
theorem not_isLocalNorm_of_ramified {d u : ℤ} (hpd : (p : ℤ) ∣ d) (hpd2 : ¬ (p : ℤ) ^ 2 ∣ d)
    (hu : ¬ IsSquare (u : ZMod p)) : ¬ IsLocalNorm ℚ_[p] d (u : ℚ_[p]) := by
  obtain ⟨d', rfl⟩ := hpd
  have hd' : ¬ (p : ℤ) ∣ d' := fun h => hpd2 (by obtain ⟨e, rfl⟩ := h; exact ⟨e, by ring⟩)
  have hd'0 : (d' : ZMod p) ≠ 0 := fun h => hd' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  rw [← PadicInt.coe_intCast]
  apply not_isLocalNorm_of_descent
  · intro Y Z h
    apply hu
    refine ⟨toZMod Y, ?_⟩
    have := congrArg toZMod h
    simp only [map_sub, map_mul, map_pow, map_intCast, Int.cast_mul, Int.cast_natCast,
      map_natCast, ZMod.natCast_self, zero_mul, sub_zero] at this
    rw [this]; ring
  · intro k Y Z h
    have h1 := congrArg toZMod h
    simp only [map_sub, map_mul, map_pow, map_intCast, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, sub_zero, map_natCast] at h1
    have hY : toZMod Y = 0 := by
      have : toZMod Y ^ 2 = 0 := by rw [← h1]; simp
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    obtain ⟨Y', rfl⟩ := dvd_of_toZMod hY
    refine ⟨⟨Y', rfl⟩, dvd_of_toZMod ?_⟩
    have h2 : (p : ℤ_[p]) * ((d' : ℤ_[p]) * Z ^ 2) =
        p * (p * Y' ^ 2 - (p : ℤ_[p]) ^ (2 * k + 1) * u) := by
      push_cast at h
      linear_combination h
    have h3 := congrArg toZMod (mul_left_cancel₀ p_ne_zero_padicInt h2)
    simp only [map_sub, map_mul, map_pow, map_intCast, map_natCast, ZMod.natCast_self,
      zero_mul, zero_pow (Nat.succ_ne_zero _), sub_zero] at h3
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hd'0
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4

end Descent

section Two

theorem intCast_zmod8 {d : ℤ} {r : ℕ} (h : d % 8 = r) : (d : ZMod (2 ^ 3)) = r := by
  have e : d = 8 * (d / 8) + r := by omega
  rw [e]; push_cast
  have : (8 : ZMod (2 ^ 3)) = 0 := by decide
  rw [this]; ring

theorem two_dvd_of_four_mul {Y : ℤ_[2]} (h : 4 * toZModPow 3 Y = 0) : ((2 : ℕ) : ℤ_[2]) ∣ Y := by
  have h1 : (4 * Y) ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
    rw [← ker_toZModPow, RingHom.mem_ker, map_mul, map_ofNat]; exact h
  obtain ⟨W, hW⟩ := Ideal.mem_span_singleton.mp h1
  refine ⟨W, ?_⟩
  have h4 : (4 : ℤ_[2]) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  rw [hW]; push_cast; ring

/-- Descent at `2`, modulo `8`. -/
theorem not_isLocalNorm_two {d : ℤ} {x : ℤ_[2]} {r : ZMod (2 ^ 3)} (hd : (d : ZMod (2 ^ 3)) = r)
    (h0 : ∀ a b : ZMod (2 ^ 3), toZModPow 3 x ≠ a ^ 2 - r * b ^ 2)
    (hstep : ∀ c a b : ZMod (2 ^ 3), 4 * c * toZModPow 3 x = a ^ 2 - r * b ^ 2 →
      4 * a = 0 ∧ 4 * b = 0) :
    ¬ IsLocalNorm ℚ_[2] d (x : ℚ_[2]) := by
  apply not_isLocalNorm_of_descent
  · intro Y Z h
    apply h0 (toZModPow 3 Y) (toZModPow 3 Z)
    have := congrArg (toZModPow 3) h
    simpa [hd] using this
  · intro k Y Z h
    have e : ((2 : ℕ) : ℤ_[2]) ^ (2 * (k + 1)) = 4 * ((2 : ℕ) : ℤ_[2]) ^ (2 * k) := by
      push_cast; ring
    rw [e] at h
    have := congrArg (toZModPow 3) h
    simp only [map_mul, map_sub, map_pow, map_intCast, map_ofNat, hd] at this
    obtain ⟨ha, hb⟩ := hstep _ _ _ this
    exact ⟨two_dvd_of_four_mul ha, two_dvd_of_four_mul hb⟩

/-- `2` is not a norm from `ℚ_2(√d)` for `d ≡ 5 (mod 8)` (the unramified quadratic extension). -/
theorem not_isLocalNorm_two_of_five {d : ℤ} (hd : d % 8 = 5) :
    ¬ IsLocalNorm ℚ_[2] d (2 : ℚ_[2]) := by
  have e : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by norm_cast
  rw [← e]
  refine not_isLocalNorm_two (r := 5) (by rw [intCast_zmod8 hd]; rfl) ?_ ?_
  · simp only [map_ofNat]; decide
  · simp only [map_ofNat]; decide

/-- `−1` is not a norm from `ℚ_2(√d)` for `d ≡ 3 (mod 4)`. -/
theorem not_isLocalNorm_neg_one_of_three {d : ℤ} (hd : d % 4 = 3) :
    ¬ IsLocalNorm ℚ_[2] d (-1 : ℚ_[2]) := by
  have e : ((-1 : ℤ_[2]) : ℚ_[2]) = -1 := by norm_cast
  rw [← e]
  rcases (by omega : d % 8 = 3 ∨ d % 8 = 7) with h | h
  · refine not_isLocalNorm_two (r := 3) (by rw [intCast_zmod8 h]; rfl) ?_ ?_
    · simp only [map_neg, map_one]; decide
    · simp only [map_neg, map_one]; decide
  · refine not_isLocalNorm_two (r := 7) (by rw [intCast_zmod8 h]; rfl) ?_ ?_
    · simp only [map_neg, map_one]; decide
    · simp only [map_neg, map_one]; decide

/-- `5` is not a norm from `ℚ_2(√d)` for `d ≡ 2 (mod 4)`. -/
theorem not_isLocalNorm_five_of_two {d : ℤ} (hd : d % 4 = 2) :
    ¬ IsLocalNorm ℚ_[2] d (5 : ℚ_[2]) := by
  have e : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast
  rw [← e]
  rcases (by omega : d % 8 = 2 ∨ d % 8 = 6) with h | h
  · refine not_isLocalNorm_two (r := 2) (by rw [intCast_zmod8 h]; rfl) ?_ ?_
    · simp only [map_ofNat]; decide
    · simp only [map_ofNat]; decide
  · refine not_isLocalNorm_two (r := 6) (by rw [intCast_zmod8 h]; rfl) ?_ ?_
    · simp only [map_ofNat]; decide
    · simp only [map_ofNat]; decide

/-- For `d ≡ 1 (mod 8)`, `d` is a square in `ℚ_2` and every element is a norm. -/
theorem isLocalNorm_two_of_one {d : ℤ} (hd : d % 8 = 1) (x : ℚ_[2]) : IsLocalNorm ℚ_[2] d x := by
  obtain ⟨w, hw0, hw⟩ := exists_sq_of_int_two hd
  exact isLocalNorm_of_eq_sq (by norm_num) hw0 hw x

theorem isLocalNorm_two_five {d : ℤ} (hd : d % 4 = 1) : IsLocalNorm ℚ_[2] d 5 := by
  obtain ⟨w, -, hw⟩ := exists_sq_of_int_two (a := 5 + 4 * d) (by omega)
  refine ⟨w, 2, ?_⟩
  push_cast at hw
  linear_combination hw

theorem isLocalNorm_two_neg_one {d : ℤ} (hd : d % 4 = 1) : IsLocalNorm ℚ_[2] d (-1) := by
  rcases (by omega : d % 8 = 1 ∨ d % 8 = 5) with h | h
  · exact isLocalNorm_two_of_one h _
  obtain ⟨w, hw0, hw⟩ := exists_sq_of_int_two (a := d - 4) (by omega)
  refine ⟨2 / w, 1 / w, ?_⟩
  push_cast at hw
  field_simp
  linear_combination hw

/-- Every unit of `ℤ_2` is a norm from `ℚ_2(√d)` for `d ≡ 1 (mod 4)` (unramified). -/
theorem isLocalNorm_two_unit {d : ℤ} (hd : d % 4 = 1) {u : ℤ_[2]} (hu : IsUnit u) :
    IsLocalNorm ℚ_[2] d (u : ℚ_[2]) := by
  have hu8 : toZModPow 3 u * toZModPow 3 ((hu.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have hodd : ∀ a b : ZMod (2 ^ 3), a * b = 1 → a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by decide
  have hm1 := isLocalNorm_two_neg_one hd
  have h5 := isLocalNorm_two_five hd
  have key : ∀ r : ℤ, IsLocalNorm ℚ_[2] d (r : ℚ_[2]) → toZModPow 3 (u * (r : ℤ_[2])) = 1 →
      IsLocalNorm ℚ_[2] d (u : ℚ_[2]) := by
    intro r hr h1
    have hr0 : (r : ℚ_[2]) ≠ 0 := by
      intro h0
      have : r = 0 := by exact_mod_cast h0
      subst this
      simp at h1
      exact absurd h1 (by decide)
    obtain ⟨W, hW⟩ := isSquare_of_toZModPow_three h1
    refine isLocalNorm_of_mul_eq_sq hr0 (W := (W : ℚ_[2])) ?_ hr
    have := congrArg (fun t : ℤ_[2] => (t : ℚ_[2])) hW
    simp only [PadicInt.coe_mul, PadicInt.coe_intCast] at this
    rw [this]; ring
  rcases hodd _ _ hu8 with h | h | h | h
  · exact key 1 (by simpa using isLocalNorm_sq (d := d) (1 : ℚ_[2])) (by simp [h])
  · refine key (-5) (by push_cast; simpa using hm1.mul h5) ?_
    rw [map_mul, h, map_intCast]; decide
  · refine key 5 (by exact_mod_cast h5) ?_
    rw [map_mul, h, map_intCast]; decide
  · refine key (-1) (by push_cast; exact hm1) ?_
    rw [map_mul, h, map_intCast]; decide

end Two

section Infinity

theorem real_isLocalNorm_of_pos {d : ℤ} (hd : 0 < d) (x : ℝ) : IsLocalNorm ℝ d x := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact isLocalNorm_of_eq_sq two_ne_zero (w := Real.sqrt d) (Real.sqrt_ne_zero'.mpr hd')
    (Real.sq_sqrt hd'.le).symm x

theorem real_not_isLocalNorm_neg_one {d : ℤ} (hd : d < 0) : ¬ IsLocalNorm ℝ d (-1) := by
  rintro ⟨y, z, h⟩
  have : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg y, sq_nonneg z, mul_nonneg (neg_nonneg.mpr this.le) (sq_nonneg z)]

/-- **The local condition at `∞`**: `χ_{d,∞}(−1) = χ_{D,∞}(−1)` forces `d D > 0`. -/
theorem pos_mul_of_real_iff {d D : ℤ} (hd : d ≠ 0) (hD : D ≠ 0)
    (h : IsLocalNorm ℝ d (-1) ↔ IsLocalNorm ℝ D (-1)) : 0 < d * D := by
  rcases lt_or_gt_of_ne hd with hd' | hd' <;> rcases lt_or_gt_of_ne hD with hD' | hD'
  · nlinarith
  · exact absurd (h.mpr (real_isLocalNorm_of_pos hD' _)) (real_not_isLocalNorm_neg_one hd')
  · exact absurd (h.mp (real_isLocalNorm_of_pos hd' _)) (real_not_isLocalNorm_neg_one hD')
  · nlinarith

theorem real_isSquare_div_of_pos_mul {d D : ℤ} (h : 0 < d * D) : IsSquare ((d : ℝ) / D) := by
  have hD : (D : ℝ) ≠ 0 := by
    intro h0; have : D = 0 := by exact_mod_cast h0
    subst this; simp at h
  have hpos : (0 : ℝ) < (d : ℝ) / D := by
    have h' : (0 : ℝ) < (d : ℝ) * D := by exact_mod_cast h
    have : (d : ℝ) / D = ((d : ℝ) * D) / ((D : ℝ) * D) := by field_simp
    rw [this]; exact div_pos h' (mul_self_pos.mpr hD)
  exact ⟨Real.sqrt ((d : ℝ) / D), (Real.mul_self_sqrt hpos.le).symm⟩

end Infinity

section OddUnits

variable {p : ℕ} [hp : Fact p.Prime]

theorem intCast_ne_zero_of_not_dvd {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : (d : ZMod p) ≠ 0 :=
  fun h => hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

theorem padic_intCast_ne_zero_of_not_dvd {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : (d : ℚ_[p]) ≠ 0 := by
  intro h; apply hd; rw [Int.cast_eq_zero.mp h]; exact dvd_zero _

/-- **Every unit is a norm from an unramified quadratic extension** (`p` odd, `p ∤ d`): solve
`a² − d b² ≡ u (mod p)` (Chevalley–Warning for two quadrics, Mathlib) and lift by Hensel. -/
theorem isLocalNorm_unit (hp2 : p ≠ 2) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) {u : ℤ_[p]}
    (hu : toZMod u ≠ 0) : IsLocalNorm ℚ_[p] d (u : ℚ_[p]) := by
  have hd0 := intCast_ne_zero_of_not_dvd hd
  have hdQ := padic_intCast_ne_zero_of_not_dvd hd
  have hcard : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hdeg : (C (-(d : ZMod p)) * X ^ 2 + C (-toZMod u)).degree = 2 := by
    rw [degree_add_C (by rw [degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0)]; norm_num),
      degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0)]
    rfl
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := ZMod p)
    (f := X ^ 2) (g := C (-(d : ZMod p)) * X ^ 2 + C (-toZMod u)) (by simp) hdeg hcard
  simp only [eval_pow, eval_X, eval_add, eval_mul, eval_C] at hab
  set B : ℤ_[p] := ((b.val : ℕ) : ℤ_[p])
  have hB : toZMod B = b := by simp [B]
  by_cases ha : a = 0
  · rw [ha] at hab
    have hb : b ≠ 0 := by
      rintro rfl; apply hu; linear_combination -hab
    obtain ⟨W, hW⟩ := isSquare_of_toZMod hp2 (c := (d : ZMod p) * b) (mul_ne_zero hd0 hb)
      (u := -(u * d)) (by
        simp only [map_neg, map_mul, map_intCast]
        linear_combination (d : ZMod p) * hab)
    refine ⟨0, (W : ℚ_[p]) / d, ?_⟩
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hW
    simp only [PadicInt.coe_mul, PadicInt.coe_neg, PadicInt.coe_intCast] at this
    field_simp
    linear_combination -this
  · obtain ⟨W, hW⟩ := isSquare_of_toZMod hp2 (c := a) ha (u := u + d * B ^ 2)
      (by simp only [map_add, map_mul, map_pow, map_intCast, hB]; linear_combination -hab)
    refine ⟨W, B, ?_⟩
    have := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hW
    simp only [PadicInt.coe_mul, PadicInt.coe_add, PadicInt.coe_pow, PadicInt.coe_intCast] at this
    linear_combination this

theorem isLocalNorm_intCast_unit (hp2 : p ≠ 2) {d u : ℤ} (hd : ¬ (p : ℤ) ∣ d)
    (hu : ¬ (p : ℤ) ∣ u) : IsLocalNorm ℚ_[p] d (u : ℚ_[p]) := by
  have := isLocalNorm_unit hp2 hd (u := (u : ℤ_[p]))
    (by rw [map_intCast]; exact intCast_ne_zero_of_not_dvd hu)
  simpa using this

theorem not_sq_dvd_of_squarefree {D : ℤ} (hD : Squarefree D) : ¬ (p : ℤ) ^ 2 ∣ D := by
  intro h
  have hu := hD (p : ℤ) (by simpa [sq] using h)
  have h1 := Int.isUnit_iff_natAbs_eq.mp hu
  simp only [Int.natAbs_natCast] at h1
  exact hp.out.one_lt.ne' h1

end OddUnits

section LocalConditions

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The local condition at an odd prime.** If `χ_{D,p} = χ_{D₀,p}` (same norm groups in
`ℚ_p^×`), `p ∤ D₀` and `D` squarefree, then `D / D₀` is a square in `ℚ_p`. -/
theorem isSquare_div_of_localNorm_iff (hp2 : p ≠ 2) {D D₀ : ℤ} (hD : Squarefree D)
    (hD₀ : ¬ (p : ℤ) ∣ D₀)
    (h : ∀ x : ℚ_[p], x ≠ 0 → (IsLocalNorm ℚ_[p] D x ↔ IsLocalNorm ℚ_[p] D₀ x)) :
    IsSquare ((D : ℚ_[p]) / (D₀ : ℚ_[p])) := by
  have hD₀Q := padic_intCast_ne_zero_of_not_dvd hD₀
  by_cases hpD : (p : ℤ) ∣ D
  · exfalso
    obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by ring⟩
    set u : ℤ := ((a.val : ℕ) : ℤ)
    have hu : (u : ZMod p) = a := by simp [u]
    have hpu : ¬ (p : ℤ) ∣ u := fun h' => ha0 (by rw [← hu]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h')
    have hn := not_isLocalNorm_of_ramified hpD (not_sq_dvd_of_squarefree hD) (u := u) (by rw [hu]; exact ha)
    exact hn ((h _ (padic_intCast_ne_zero_of_not_dvd hpu)).mpr (isLocalNorm_intCast_unit hp2 hD₀ hpu))
  have hDQ := padic_intCast_ne_zero_of_not_dvd hpD
  have hpDD : ¬ (p : ℤ) ∣ D * D₀ := by
    intro h'
    rcases (Int.Prime.dvd_mul' hp.out h') with h1 | h1
    · exact hpD h1
    · exact hD₀ h1
  by_cases hsq : IsSquare ((D * D₀ : ℤ) : ZMod p)
  · obtain ⟨w, -, hw⟩ := exists_sq_of_int hp2 hpDD hsq
    refine ⟨w / D₀, ?_⟩
    push_cast at hw
    field_simp
    linear_combination hw
  · exfalso
    have hl := (legendreSym.eq_neg_one_iff (p := p)).mpr hsq
    rw [legendreSym.mul] at hl
    have h1 := legendreSym.eq_one_or_neg_one (p := p) (intCast_ne_zero_of_not_dvd hpD)
    have h2 := legendreSym.eq_one_or_neg_one (p := p) (intCast_ne_zero_of_not_dvd hD₀)
    have hpQ : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2] at hl; norm_num at hl
    · -- `D` square, `D₀` not
      obtain ⟨w, hw0, hw⟩ := exists_sq_of_int hp2 hpD
        ((legendreSym.eq_one_iff p (intCast_ne_zero_of_not_dvd hpD)).mp h1)
      exact not_isLocalNorm_p ((legendreSym.eq_neg_one_iff p).mp h2)
        ((h _ hpQ).mp (isLocalNorm_of_eq_sq (by norm_num) hw0 hw _))
    · obtain ⟨w, hw0, hw⟩ := exists_sq_of_int hp2 hD₀
        ((legendreSym.eq_one_iff p (intCast_ne_zero_of_not_dvd hD₀)).mp h2)
      exact not_isLocalNorm_p ((legendreSym.eq_neg_one_iff p).mp h1)
        ((h _ hpQ).mpr (isLocalNorm_of_eq_sq (by norm_num) hw0 hw _))
    · rw [h1, h2] at hl; norm_num at hl

/-- **The local condition at `2`.** If `χ_{D,2} = χ_{D₀,2}` with `D₀ ≡ 1 (mod 4)` and `D`
squarefree, then `D ≡ 1 (mod 4)` (`χ_D` is unramified at `2`) and `D / D₀` is a square in `ℚ_2`. -/
theorem isSquare_div_two_of_localNorm_iff {D D₀ : ℤ} (hD : Squarefree D) (hD₀ : D₀ % 4 = 1)
    (h : ∀ x : ℚ_[2], x ≠ 0 → (IsLocalNorm ℚ_[2] D x ↔ IsLocalNorm ℚ_[2] D₀ x)) :
    D % 4 = 1 ∧ IsSquare ((D : ℚ_[2]) / (D₀ : ℚ_[2])) := by
  have h4 : D % 4 ≠ 0 := by
    intro h0
    have := not_sq_dvd_of_squarefree (p := 2) hD
    exact this (by push_cast; omega)
  have hD₀Q : (D₀ : ℚ_[2]) ≠ 0 := by
    intro h0; have := Int.cast_eq_zero.mp h0; omega
  have hD4 : D % 4 = 1 := by
    rcases (by omega : D % 4 = 1 ∨ D % 4 = 2 ∨ D % 4 = 3) with h1 | h1 | h1
    · exact h1
    · exact absurd ((h 5 (by norm_num)).mpr (isLocalNorm_two_five hD₀))
        (not_isLocalNorm_five_of_two h1)
    · exact absurd ((h (-1) (by norm_num)).mpr (isLocalNorm_two_neg_one hD₀))
        (not_isLocalNorm_neg_one_of_three h1)
  refine ⟨hD4, ?_⟩
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  rcases (by omega : D % 8 = 1 ∨ D % 8 = 5) with h1 | h1 <;>
    rcases (by omega : D₀ % 8 = 1 ∨ D₀ % 8 = 5) with h0 | h0
  · obtain ⟨w, -, hw⟩ := exists_sq_of_int_two (a := D * D₀) (by rw [Int.mul_emod, h1, h0]; rfl)
    refine ⟨w / D₀, ?_⟩
    push_cast at hw; field_simp; linear_combination hw
  · exact absurd ((h 2 h2).mp (isLocalNorm_two_of_one h1 _)) (not_isLocalNorm_two_of_five h0)
  · exact absurd ((h 2 h2).mpr (isLocalNorm_two_of_one h0 _)) (not_isLocalNorm_two_of_five h1)
  · obtain ⟨w, -, hw⟩ := exists_sq_of_int_two (a := D * D₀) (by rw [Int.mul_emod, h1, h0]; rfl)
    refine ⟨w / D₀, ?_⟩
    push_cast at hw; field_simp; linear_combination hw

end LocalConditions

section Character

/-- **The quadratic character `χ_d` at a prime `p`** (the Dirichlet coefficient of the idele class
character of `ℚ(√d)` at `p`): `χ_{d,p}(p)` if the local component `χ_{d,p}` is unramified, i.e.
trivial on `ℤ_p^×` (every unit is a norm from `ℚ_p(√d)`), and `0` otherwise. Here
`χ_{d,p}(x) = 1` iff `x` is a norm from `ℚ_p(√d)` (local class field theory). -/
noncomputable def charAtPrime (d : ℤ) (p : ℕ) : ℤ := by
  classical
  exact if hp : p.Prime then
    haveI := Fact.mk hp
    if (∀ u : ℤ_[p], IsUnit u → IsLocalNorm ℚ_[p] d (u : ℚ_[p])) then
      (if IsLocalNorm ℚ_[p] d (p : ℚ_[p]) then 1 else -1)
    else 0
  else 0

/-- **The Dirichlet coefficients of `L(s, χ_d) = ∏_{p unramified} (1 − χ_{d,p}(p) p^{−s})^{−1}`**:
`χ_d(n) = ∏_{p^k ∥ n} χ_d(p)^k` (completely multiplicative, `0` at multiples of ramified
primes). -/
noncomputable def idelicChar (d : ℤ) (n : ℕ) : ℤ :=
  n.factorization.prod fun p k => charAtPrime d p ^ k

/-- Quadratic reciprocity in the form used here: for `d ≡ 1 (mod 4)` and an odd prime `p`,
`(p / |d|) = (d / p)`. -/
theorem jacobiSym_prime_eq_legendreSym {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d : ℤ}
    (hd : d % 4 = 1) : jacobiSym (p : ℤ) d.natAbs = legendreSym p d := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  rw [jacobiSym.legendreSym.to_jacobiSym]
  rcases le_or_gt 0 d with h0 | h0
  · have hdeq : d = ((d.natAbs : ℕ) : ℤ) := by omega
    have h1 : d.natAbs % 4 = 1 := by omega
    conv_rhs => rw [hdeq]
    exact (jacobiSym.quadratic_reciprocity_one_mod_four h1 hpodd).symm
  · have h3 : d.natAbs % 4 = 3 := by omega
    have hoddD : Odd d.natAbs := Nat.odd_iff.mpr (by omega)
    have hdeq : d = -((d.natAbs : ℕ) : ℤ) := by omega
    conv_rhs => rw [hdeq]
    rw [jacobiSym.neg _ hpodd]
    have hp4 : p % 4 = 1 ∨ p % 4 = 3 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hpodd)
    rcases hp4 with h1 | h3p
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hoddD, ZMod.χ₄_nat_one_mod_four h1,
        one_mul]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h3p h3, ZMod.χ₄_nat_three_mod_four h3p,
        neg_one_mul]

/-- **`χ_d(p) = (p / |d|)`** for `d ≡ 1 (mod 4)` squarefree: the idelic character at a prime is
the Jacobi symbol, i.e. the Kronecker symbol `(d / p)`. -/
theorem charAtPrime_eq_jacobiSym {d : ℤ} (hd4 : d % 4 = 1) (hd : Squarefree d) {p : ℕ}
    (hp : p.Prime) : charAtPrime d p = jacobiSym (p : ℤ) d.natAbs := by
  have := Fact.mk hp
  unfold charAtPrime
  rw [dite_eq_left hp]
  by_cases hp2 : p = 2
  · subst hp2
    rw [ite_eq_left (fun u hu => isLocalNorm_two_unit hd4 hu)]
    have hodd : Odd d.natAbs := Nat.odd_iff.mpr (by omega)
    have e2 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
    rw [e2, show ((2 : ℕ) : ℤ) = 2 from rfl, jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight,
      ite_eq_right (by omega : d.natAbs % 2 ≠ 0)]
    rcases (by omega : d % 8 = 1 ∨ d % 8 = 5) with h | h
    · rw [ite_eq_left (isLocalNorm_two_of_one h _), ite_eq_left (by omega)]
    · rw [ite_eq_right (not_isLocalNorm_two_of_five h), ite_eq_right (by omega)]
  · by_cases hpd : (p : ℤ) ∣ d
    · -- ramified
      rw [ite_eq_right]
      · symm
        rw [jacobiSym.eq_zero_iff]
        refine ⟨by have := hd.ne_zero; omega, ?_⟩
        rw [Int.gcd_natCast_natCast]
        intro h1
        have : p ∣ Nat.gcd p d.natAbs := Nat.dvd_gcd dvd_rfl (Int.natCast_dvd.mp hpd)
        rw [h1] at this
        exact hp.one_lt.ne' (Nat.dvd_one.mp this)
      · intro hall
        obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
          (by rw [ZMod.ringChar_zmod_n]; exact hp2)
        have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by ring⟩
        set u : ℤ := ((a.val : ℕ) : ℤ)
        have hu : (u : ZMod p) = a := by simp [u]
        have hn := not_isLocalNorm_of_ramified hpd (not_sq_dvd_of_squarefree hd) (u := u)
          (by rw [hu]; exact ha)
        apply hn
        have := hall (u : ℤ_[p]) (isUnit_of_toZMod (by rw [map_intCast, hu]; exact ha0))
        simpa using this
    · -- unramified
      rw [ite_eq_left (fun u hu => isLocalNorm_unit hp2 hpd ((hu.map toZMod).ne_zero)),
        jacobiSym_prime_eq_legendreSym hp2 hd4]
      have h0 := intCast_ne_zero_of_not_dvd hpd
      by_cases hsq : IsSquare (d : ZMod p)
      · obtain ⟨w, hw0, hw⟩ := exists_sq_of_int hp2 hpd hsq
        rw [ite_eq_left (isLocalNorm_of_eq_sq (by norm_num) hw0 hw _),
          (legendreSym.eq_one_iff p h0).mpr hsq]
      · rw [ite_eq_right (not_isLocalNorm_p hsq), (legendreSym.eq_neg_one_iff p).mpr hsq]

theorem zmod2_five_ne_zero : ¬ ((5 : ZMod 2) = 0) := by decide

/-- Consistency check at `2` for even discriminants: `χ_d(2) = 0` when `d ≡ 2, 3 (mod 4)`
(`χ_{d,2}` is ramified). -/
theorem charAtPrime_two_of_ramified {d : ℤ} (hd : d % 4 = 2 ∨ d % 4 = 3) : charAtPrime d 2 = 0 := by
  have := Fact.mk Nat.prime_two
  unfold charAtPrime
  rw [dite_eq_left Nat.prime_two, ite_eq_right]
  intro hall
  rcases hd with h | h
  · apply not_isLocalNorm_five_of_two h
    have h5 : toZMod (5 : ℤ_[2]) ≠ 0 := by
      rw [map_ofNat]
      exact zmod2_five_ne_zero
    have := hall 5 (isUnit_of_toZMod h5)
    have e : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast
    rwa [e] at this
  · apply not_isLocalNorm_neg_one_of_three h
    have := hall (-1) isUnit_one.neg
    simpa using this

/-- **The idelic character of `ℚ(√d)` is the Jacobi symbol** `n ↦ (n / |d|)` for `d ≡ 1 (mod 4)`
squarefree (and `n ≠ 0`). -/
theorem idelicChar_eq_jacobiSym {d : ℤ} (hd4 : d % 4 = 1) (hd : Squarefree d) :
    ∀ n : ℕ, n ≠ 0 → idelicChar d n = jacobiSym (n : ℤ) d.natAbs := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [idelicChar]
  | prime p hp =>
    intro _
    rw [idelicChar, hp.factorization, Finsupp.prod_single_index (by simp), pow_one,
      charAtPrime_eq_jacobiSym hd4 hd hp]
  | mul a b iha ihb =>
    intro hab
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    rw [idelicChar, Nat.factorization_mul ha hb,
      Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), ← idelicChar,
      ← idelicChar, iha ha, ihb hb]
    push_cast
    rw [jacobiSym.mul_left]

end Character

end ZInQ.FHPrinted
