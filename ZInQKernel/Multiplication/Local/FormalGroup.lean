import ZInQKernel.Multiplication.Local.Chord

/-!
# The formal neighbourhood of `y² = x³ + A x` and its filtration

Blueprint: `multiplication/local/formal-group.md`.

Let `K` be a field, `v : AddValuation K (WithTop ℤ)` a valuation with values in `ℤ ∪ {∞}`, and
`A ∈ K` with `v(A) ≥ 0`; `W = shortCurve A` is `y² = x³ + A x`. Put
`W₁(K) = {O} ∪ {(x, y) ∈ W(K) : v(x) < 0}` (`W1`), and `z = -x/y`, `w = 1/x`, `ω = -1/y`, all
`0` at `O` (`zCoord`, `wCoord`, `omegaCoord`). Then

1. an affine point of `W₁(K)` has `v(x) = -2N`, `v(y) = -3N` with `N ≥ 1`, so `y ≠ 0`,
   `v(z) = N`, `v(w) = 2N`, `v(ω) = 3N` (`formal_val_x_y`);
2. for every integer `k`, `W_k(K) = {P ∈ W₁(K) : v(z(P)) ≥ k}` is a subgroup (`formalFilt`;
   for `k ≤ 1` it is `W₁(K)` itself, `formalNbhd`);
3. `z` is injective on `W₁(K)` (`zCoord_injOn`);
4. `[n]P ∈ W₁(K)` and `v(z([n]P)) ≥ v(z(P))` for `P ∈ W₁(K)`, `n ∈ ℤ` (`zsmul_mem_W1`).

The proof is the elementary chord computation of `Chord.lean`; no completeness is used.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K]

/-- The local parameter `z = -x/y` of a point of `y² = x³ + A x` (`z(O) = 0`). -/
def zCoord {A : K} : (shortCurve A).toAffine.Point → K
  | 0 => 0
  | .some x y _ => -x / y

/-- The inverse abscissa `w = 1/x` (`w(O) = 0`). -/
def wCoord {A : K} : (shortCurve A).toAffine.Point → K
  | 0 => 0
  | .some x _ _ => 1 / x

/-- Silverman's auxiliary coordinate `ω = -1/y` (`ω(O) = 0`). -/
def omegaCoord {A : K} : (shortCurve A).toAffine.Point → K
  | 0 => 0
  | .some _ y _ => -1 / y

@[simp] theorem zCoord_zero {A : K} : zCoord (0 : (shortCurve A).toAffine.Point) = 0 := rfl
@[simp] theorem zCoord_some {A x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    zCoord (.some x y h) = -x / y := rfl
@[simp] theorem wCoord_some {A x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    wCoord (.some x y h) = 1 / x := rfl
@[simp] theorem omegaCoord_some {A x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    omegaCoord (.some x y h) = -1 / y := rfl

theorem point_zero_eq {A : K} : (Point.zero : (shortCurve A).toAffine.Point) = 0 := rfl

theorem zCoord_neg {A : K} (P : (shortCurve A).toAffine.Point) : zCoord (-P) = -zCoord P := by
  rcases P with _ | ⟨x, y, h⟩
  · show (0 : K) = -0; rw [neg_zero]
  · rw [Point.neg_some, zCoord_some, zCoord_some, shortCurve_negY]; ring

variable (v : AddValuation K (WithTop ℤ))

/-- Membership in `W₁(K)`: `P = O`, or `P = (x, y)` with `v(x) < 0`. -/
def InW1 {A : K} : (shortCurve A).toAffine.Point → Prop
  | 0 => True
  | .some x _ _ => v x < 0

/-- The formal neighbourhood `W₁(K) = {O} ∪ {(x, y) : v(x) < 0}` as a set. -/
def W1 (A : K) : Set (shortCurve A).toAffine.Point := {P | InW1 v P}

@[simp] theorem zero_mem_W1 {A : K} : (0 : (shortCurve A).toAffine.Point) ∈ W1 v A := trivial

@[simp] theorem some_mem_W1_iff {A x y : K} (h : (shortCurve A).toAffine.Nonsingular x y) :
    Point.some x y h ∈ W1 v A ↔ v x < 0 := Iff.rfl

variable {v} {A : K}

/-- **Part 1.** An affine point of `W₁(K)` has `v(x) = -2N` and `v(y) = -3N` with `N ≥ 1`;
hence `y ≠ 0`, `v(z) = N`, `v(w) = 2N = 2 v(z)` and `v(ω) = 3N`. -/
theorem formal_val_x_y (hA : 0 ≤ v A) {x y : K} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : v x < 0) :
    ∃ N : ℤ, 1 ≤ N ∧ v x = (-2 * N : ℤ) ∧ v y = (-3 * N : ℤ) ∧ y ≠ 0 ∧
      v (zCoord (.some x y h)) = N ∧ v (wCoord (.some x y h)) = (2 * N : ℤ) ∧
      v (omegaCoord (.some x y h)) = (3 * N : ℤ) := by
  have hA' : Vge v 0 A := hA
  have e := (shortCurve_equation_iff A x y).mp h.1
  have hx0 : x ≠ 0 := by rintro rfl; rw [v.map_zero] at hx; exact (not_top_lt hx)
  obtain ⟨a, ha⟩ := val_eq_coe hx0
  have ha0 : a < 0 := by rw [ha] at hx; exact_mod_cast hx
  have hx3 : v (x ^ 3) = (3 * a : ℤ) := by simpa using val_pow_coe ha 3
  have hAx : Vge v (3 * a + 1) (A * x) := (hA'.mul (Vge.of_eq ha)).mono (by omega)
  have hsum := val_add_eq hx3 hAx
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [← e, zero_pow two_ne_zero, v.map_zero] at hsum
    exact WithTop.top_ne_coe hsum
  obtain ⟨b, hb⟩ := val_eq_coe hy0
  have hy2 : v (y ^ 2) = (2 * b : ℤ) := by simpa using val_pow_coe hb 2
  rw [← e, hy2] at hsum
  have hab : 2 * b = 3 * a := by exact_mod_cast hsum
  refine ⟨a - b, by omega, by rw [ha]; congr 1; omega, by rw [hb]; congr 1; omega, hy0, ?_, ?_, ?_⟩
  · rw [zCoord_some, neg_div, v.map_neg, val_div_coe ha hb]
  · rw [wCoord_some, one_div, val_inv_coe ha]; congr 1; omega
  · rw [omegaCoord_some, neg_div, v.map_neg, one_div, val_inv_coe hb]; congr 1; omega

/-- The level data `v(x/y) = N`, `v(1/y) = 3N` of an affine point of `W₁(K)`. -/
theorem level_of_mem_W1 (hA : 0 ≤ v A) {x y : K} (h : (shortCurve A).toAffine.Nonsingular x y)
    (hx : v x < 0) :
    ∃ N : ℤ, 1 ≤ N ∧ y ≠ 0 ∧ v (x / y) = N ∧ v (1 / y) = (3 * N : ℤ) ∧
      v (zCoord (.some x y h)) = N := by
  obtain ⟨N, hN, -, -, hy0, hz, -, hω⟩ := formal_val_x_y hA h hx
  refine ⟨N, hN, hy0, ?_, ?_, hz⟩
  · rwa [zCoord_some, neg_div, v.map_neg] at hz
  · rwa [omegaCoord_some, neg_div, v.map_neg] at hω

variable [DecidableEq K]

/-- Closure of `{P ∈ W₁(K) : v(z(P)) ≥ k}` under addition. -/
theorem add_mem_filt (hA : 0 ≤ v A) (k : ℤ) {P Q : (shortCurve A).toAffine.Point}
    (hP : InW1 v P ∧ (k : WithTop ℤ) ≤ v (zCoord P))
    (hQ : InW1 v Q ∧ (k : WithTop ℤ) ≤ v (zCoord Q)) :
    InW1 v (P + Q) ∧ (k : WithTop ℤ) ≤ v (zCoord (P + Q)) := by
  have hA' : Vge v 0 A := hA
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [point_zero_eq, zero_add]; exact hQ
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [point_zero_eq, add_zero]; exact hP
  obtain ⟨N₁, hN₁, hy₁, ht₁, hw₁, hz₁⟩ := level_of_mem_W1 hA h₁ hP.1
  obtain ⟨N₂, hN₂, hy₂, ht₂, hw₂, hz₂⟩ := level_of_mem_W1 hA h₂ hQ.1
  have hk₁ : k ≤ N₁ := by have := hP.2; rw [hz₁] at this; exact_mod_cast this
  have hk₂ : k ≤ N₂ := by have := hQ.2; rw [hz₂] at this; exact_mod_cast this
  set m := max k 1 with hm
  have hm1 : 1 ≤ m := le_max_right _ _
  by_cases hs : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0
  · rw [hs]; exact ⟨trivial, by simp [v.map_zero]⟩
  obtain ⟨x₃, y₃, h₃, heq, hy₃, ht₃, hw₃, -⟩ := chord_add hA' hm1 h₁ h₂ hy₁ hy₂
    ((vge_iff_of_eq ht₁).mpr (by omega)) ((vge_iff_of_eq ht₂).mpr (by omega))
    ((vge_iff_of_eq hw₁).mpr (by omega)) ((vge_iff_of_eq hw₂).mpr (by omega)) hs
  rw [heq]
  have e₃ := tw_equation hy₃ ((shortCurve_equation_iff A x₃ y₃).mp h₃.1)
  have hw0 : 1 / y₃ ≠ 0 := one_div_ne_zero hy₃
  obtain ⟨c, hc⟩ := val_eq_coe hw0
  have hc3 : 3 * m ≤ c := (vge_iff_of_eq hc).mp hw₃
  have hrest : Vge v (c + 1) (-(A * (x₃ / y₃) * (1 / y₃) ^ 2)) :=
    (((hA'.mul ht₃).mul (Vge.pow (Vge.of_eq hc) 2)).mono (by push_cast; omega)).neg
  have hcube := val_add_eq hc hrest
  rw [show 1 / y₃ + -(A * (x₃ / y₃) * (1 / y₃) ^ 2) = (x₃ / y₃) ^ 3 by
    linear_combination e₃] at hcube
  have ht0 : x₃ / y₃ ≠ 0 := by
    intro h0; rw [h0, zero_pow three_ne_zero, v.map_zero] at hcube; exact WithTop.top_ne_coe hcube
  obtain ⟨d, hd⟩ := val_eq_coe ht0
  have hdm : m ≤ d := (vge_iff_of_eq hd).mp ht₃
  have hcd : c = 3 * d := by
    have := val_pow_coe hd 3; rw [hcube] at this; exact_mod_cast this
  have hx₃ : x₃ = (x₃ / y₃) / (1 / y₃) := by field_simp
  refine ⟨?_, ?_⟩
  · show v x₃ < 0
    rw [hx₃, val_div_coe hd hc]
    exact_mod_cast (show d - c < 0 by omega)
  · rw [zCoord_some, neg_div, v.map_neg, hd]
    exact_mod_cast (show k ≤ d by omega)

/-- Closure of `{P ∈ W₁(K) : v(z(P)) ≥ k}` under negation. -/
theorem neg_mem_filt (k : ℤ) {P : (shortCurve A).toAffine.Point}
    (hP : InW1 v P ∧ (k : WithTop ℤ) ≤ v (zCoord P)) :
    InW1 v (-P) ∧ (k : WithTop ℤ) ≤ v (zCoord (-P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, neg_zero]; exact hP
  rw [Point.neg_some]
  refine ⟨hP.1, ?_⟩
  have := hP.2
  rw [zCoord_some] at this ⊢
  rw [shortCurve_negY, neg_div_neg_eq, ← v.map_neg, ← neg_div]
  exact this

/-- **Part 2.** The subgroup `W_k(K) = {P ∈ W₁(K) : v(z(P)) ≥ k}` (for `k ≤ 1` this is
`W₁(K)`). -/
def formalFilt (A : K) (hA : 0 ≤ v A) (k : ℤ) : AddSubgroup (shortCurve A).toAffine.Point where
  carrier := {P | InW1 v P ∧ (k : WithTop ℤ) ≤ v (zCoord P)}
  zero_mem' := ⟨trivial, by simp [v.map_zero]⟩
  add_mem' hP hQ := add_mem_filt hA k hP hQ
  neg_mem' hP := neg_mem_filt k hP

theorem mem_formalFilt_iff (hA : 0 ≤ v A) (k : ℤ) (P : (shortCurve A).toAffine.Point) :
    P ∈ formalFilt A hA k ↔ P ∈ W1 v A ∧ (k : WithTop ℤ) ≤ v (zCoord P) := Iff.rfl

omit [DecidableEq K] in
/-- Every point of `W₁(K)` has `v(z) ≥ 1`. -/
theorem one_le_val_zCoord (hA : 0 ≤ v A) {P : (shortCurve A).toAffine.Point} (hP : P ∈ W1 v A) :
    (1 : WithTop ℤ) ≤ v (zCoord P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, zCoord_zero, v.map_zero]; exact le_top
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA h hP
  rw [hz]; exact_mod_cast hN

/-- The formal neighbourhood `W₁(K)` as a subgroup. -/
abbrev formalNbhd (A : K) (hA : 0 ≤ v A) : AddSubgroup (shortCurve A).toAffine.Point :=
  formalFilt A hA 1

/-- **Part 2, `k = 1`.** `W₁(K)` is a subgroup: its carrier is `W1`. -/
theorem mem_formalNbhd_iff (hA : 0 ≤ v A) (P : (shortCurve A).toAffine.Point) :
    P ∈ formalNbhd A hA ↔ P ∈ W1 v A :=
  ⟨fun h => h.1, fun h => ⟨h, one_le_val_zCoord hA h⟩⟩

theorem coe_formalNbhd (hA : 0 ≤ v A) : (formalNbhd A hA : Set (shortCurve A).toAffine.Point) = W1 v A :=
  Set.ext (mem_formalNbhd_iff hA)

/-- For `k ≤ 1`, `W_k(K) = W₁(K)`. -/
theorem formalFilt_eq_of_le_one (hA : 0 ≤ v A) {k : ℤ} (hk : k ≤ 1) :
    formalFilt A hA k = formalNbhd A hA := by
  ext P
  refine ⟨fun h => (mem_formalNbhd_iff hA P).mpr h.1, fun h => ⟨h.1, le_trans ?_ h.2⟩⟩
  exact_mod_cast hk

/-- The filtration is decreasing. -/
theorem formalFilt_antitone (hA : 0 ≤ v A) {k l : ℤ} (hkl : k ≤ l) :
    formalFilt A hA l ≤ formalFilt A hA k :=
  fun _ h => ⟨h.1, le_trans (by exact_mod_cast hkl) h.2⟩

/-- **Part 3.** `z` is injective on `W₁(K)`. -/
theorem zCoord_injOn (hA : 0 ≤ v A) : Set.InjOn zCoord (W1 v A) := by
  have hA' : Vge v 0 A := hA
  have aux : ∀ {x y : K} (h : (shortCurve A).toAffine.Nonsingular x y), v x < 0 →
      zCoord (.some x y h) ≠ 0 := by
    intro x y h hx h0
    obtain ⟨N, -, -, -, -, hz, -⟩ := formal_val_x_y hA h hx
    rw [h0, v.map_zero] at hz; exact WithTop.top_ne_coe hz
  rintro (_ | ⟨x₁, y₁, h₁⟩) hP (_ | ⟨x₂, y₂, h₂⟩) hQ hz
  · rfl
  · exact absurd hz.symm (aux h₂ hQ)
  · exact absurd hz (aux h₁ hP)
  obtain ⟨N₁, hN₁, hy₁, ht₁, hw₁, -⟩ := level_of_mem_W1 hA h₁ hP
  obtain ⟨N₂, hN₂, hy₂, ht₂, hw₂, -⟩ := level_of_mem_W1 hA h₂ hQ
  have ht : x₁ / y₁ = x₂ / y₂ := by
    simp only [zCoord_some, neg_div, neg_inj] at hz; exact hz
  have hx : x₁ = x₂ := by
    by_contra hx
    exact t_ne_of_x_ne' hA' le_rfl hy₁ hy₂ ((shortCurve_equation_iff A x₁ y₁).mp h₁.1)
      ((shortCurve_equation_iff A x₂ y₂).mp h₂.1) ((vge_iff_of_eq ht₁).mpr (by omega))
      ((vge_iff_of_eq hw₁).mpr (by omega)) ((vge_iff_of_eq hw₂).mpr (by omega)) hx ht
  subst hx
  have hx0 : x₁ ≠ 0 := by
    intro h0
    have hP' : v x₁ < 0 := hP
    rw [h0, v.map_zero] at hP'; exact not_top_lt hP'
  have hy : y₁ = y₂ := by
    rw [div_eq_div_iff hy₁ hy₂] at ht
    exact (mul_left_cancel₀ hx0 (by linear_combination ht)).symm
  subst hy
  rfl

/-- **Part 4.** For `P ∈ W₁(K)` and `n ∈ ℤ`, `[n]P ∈ W₁(K)` and `v(z([n]P)) ≥ v(z(P))`. -/
theorem zsmul_mem_W1 (hA : 0 ≤ v A) {P : (shortCurve A).toAffine.Point} (hP : P ∈ W1 v A)
    (n : ℤ) : n • P ∈ W1 v A ∧ v (zCoord P) ≤ v (zCoord (n • P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, zsmul_zero]; exact ⟨trivial, le_rfl⟩
  obtain ⟨N, -, -, -, -, hz, -⟩ := formal_val_x_y hA h hP
  have hmem : Point.some x y h ∈ formalFilt A hA N := ⟨hP, by rw [hz]⟩
  have := (formalFilt A hA N).zsmul_mem hmem n
  exact ⟨this.1, by rw [hz]; exact this.2⟩

/-- Part 4 for the subgroups `W_k(K)`: they are stable under `[n]`. -/
theorem zsmul_mem_formalFilt (hA : 0 ≤ v A) {k : ℤ} {P : (shortCurve A).toAffine.Point}
    (hP : P ∈ formalFilt A hA k) (n : ℤ) : n • P ∈ formalFilt A hA k :=
  (formalFilt A hA k).zsmul_mem hP n

end ZInQ.Mult
