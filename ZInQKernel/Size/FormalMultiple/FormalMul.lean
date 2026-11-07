import ZInQKernel.Multiplication.Local.FormalGroup

/-!
# Multiplication in a formal neighbourhood (the part used here)

Blueprint: `assembly/local-tests/formal-multiplication.md`, items 1 and 3 (the
statement is formalized in full by the assembly chapter; this file proves the special cases
that the formal-multiple argument needs, from the chord estimate of
`ZInQKernel/Multiplication/Local/Chord.lean`).

Let `v : AddValuation K (WithTop ℤ)`, `A ∈ K` with `v(A) ≥ 0`, `W : y² = x³ + A x`, and `W_k`
the subgroup of points with `v(z) ≥ k` (`ZInQ.Mult.formalFilt`).

1. `zCoord_add_sub_ge`: for `k ≥ 1` and `P, Q ∈ W_k`, `v(z(P + Q) - z(P) - z(Q)) ≥ 5k`.
2. `zCoord_nsmul_sub_ge`: for `Q ∈ W_k`, `v(z([n]Q) - n z(Q)) ≥ 5k`.
3. `nsmul_mem_formalFilt_of_val`: if `v(q) = e` with `0 ≤ e ≤ 4`, then
   `[qᵃ n] W_k ⊆ W_{k + a e}` (for `k ≤ 1` read `W_k = W₁`).
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult

variable {K : Type*} [Field K] [DecidableEq K] {v : AddValuation K (WithTop ℤ)} {A : K}

section Chord

variable (hA : Vge v 0 A)
include hA

/-- The third point of the line through two points of the formal neighbourhood: the
estimate `v(t₃ - t₁ - t₂) ≥ 5m` (`formal_third_point` records `m + 1`). -/
theorem formal_third_point_five {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ ℓ lam ν : K}
    (h₁ : (shortCurve A).toAffine.Equation x₁ y₁) (h₂ : (shortCurve A).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂))
    (hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hlam : Vge v (2 * m) lam) (hν : Vge v (3 * m) ν) (hν0 : ν ≠ 0) (hℓν : ℓ = -lam / ν)
    (hc₁ : y₁ = ℓ * x₁ + 1 / ν) (hc₂ : y₂ = ℓ * x₂ + 1 / ν)
    (e₃ : (-(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν)) ^ 2 =
      (ℓ ^ 2 - x₁ - x₂) ^ 3 + A * (ℓ ^ 2 - x₁ - x₂)) :
    Vge v (5 * m)
      ((ℓ ^ 2 - x₁ - x₂) / -(ℓ * (ℓ ^ 2 - x₁ - x₂) + 1 / ν) - x₁ / y₁ - x₂ / y₂) := by
  obtain ⟨hy₃0, -, -, -⟩ := formal_third_point hA hm h₁ h₂ hxy hℓ hy₁ hy₂ ht₁ ht₂ hlam hν hν0
    hℓν hc₁ hc₂ e₃
  have hV := vieta_shortCurve h₁ h₂ hxy hℓ
  have hc : y₁ - ℓ * x₁ = 1 / ν := by rw [hc₁]; ring
  rw [hc] at hV
  obtain ⟨V2, V3⟩ := hV
  generalize hx₃ : ℓ ^ 2 - x₁ - x₂ = x₃ at V2 V3 e₃ hy₃0 ⊢
  generalize hy₃ : -(ℓ * x₃ + 1 / ν) = y₃ at e₃ hy₃0 ⊢
  have hAl : Vge v 1 (A * lam ^ 2) := (hA.mul (hlam.pow 2)).mono (by push_cast; omega)
  have hD0 : 1 + A * lam ^ 2 ≠ 0 := Mult.one_add_ne_zero hAl
  have hDv : v (1 + A * lam ^ 2) = 0 := Mult.val_one_add hAl
  have hD' : A * ℓ ^ 2 + (1 / ν) ^ 2 ≠ 0 := by
    rw [hℓν]
    intro h0
    apply hD0
    have : A * (-lam / ν) ^ 2 + (1 / ν) ^ 2 = (1 + A * lam ^ 2) / ν ^ 2 := by
      field_simp; ring
    rw [this] at h0
    exact (div_eq_zero_iff.mp h0).resolve_right (pow_ne_zero 2 hν0)
  have hid := sum_t_identity (A := A) (x₁ := x₁) (x₂ := x₂) (x₃ := x₃) (y₃ := y₃)
    (by rw [← hx₃]; ring) V2 V3 hc₁ hc₂ (by rw [← hy₃, neg_neg]) hy₁ hy₂ hy₃0 hD'
  have hdiff : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = 2 * A * lam * ν / (1 + A * lam ^ 2) := by
    have : x₃ / y₃ - x₁ / y₁ - x₂ / y₂ = -(2 * A * ℓ / (A * ℓ ^ 2 + (1 / ν) ^ 2)) := by
      rw [← hid]; ring
    have key : A * (-lam / ν) ^ 2 + (1 / ν) ^ 2 = (1 + A * lam ^ 2) / ν ^ 2 := by
      field_simp; ring
    rw [this, hℓν, key, div_div_eq_mul_div, neg_div', div_left_inj' hD0]
    field_simp
  rw [hdiff]
  have hN : Vge v (5 * m) (2 * A * lam * ν) :=
    ((((Mult.vge_ofNat 2).mul hA).mul hlam).mul hν).mono (by omega)
  exact hN.div_unit hDv

/-- **The addition estimate with `5m`.** If `v(x/y) ≥ m ≥ 1` and `v(1/y) ≥ 3m` for two points
whose sum is not `O`, then the sum is affine with the same bounds and
`v(t(P₁ + P₂) - t(P₁) - t(P₂)) ≥ 5m`. -/
theorem chord_add_five {m : ℤ} (hm : 1 ≤ m) {x₁ y₁ x₂ y₂ : K}
    (h₁ : (shortCurve A).toAffine.Nonsingular x₁ y₁)
    (h₂ : (shortCurve A).toAffine.Nonsingular x₂ y₂) (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0)
    (ht₁ : Vge v m (x₁ / y₁)) (ht₂ : Vge v m (x₂ / y₂))
    (hw₁ : Vge v (3 * m) (1 / y₁)) (hw₂ : Vge v (3 * m) (1 / y₂))
    (hne : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ≠ 0) :
    ∃ x₃ y₃ h₃, Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x₃ y₃ h₃ ∧
      Vge v (5 * m) (x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by
  have e₁ := (shortCurve_equation_iff A x₁ y₁).mp h₁.1
  have e₂ := (shortCurve_equation_iff A x₂ y₂).mp h₂.1
  have hxy : ¬(x₁ = x₂ ∧ y₁ = (shortCurve A).toAffine.negY x₂ y₂) :=
    fun h => hne (Point.add_of_Y_eq h.1 h.2)
  rw [Point.add_some hxy]
  obtain ⟨lam, ν, hlam, hν, hν0, hℓν, hc₁, hc₂⟩ : ∃ lam ν : K, Vge v (2 * m) lam ∧
      Vge v (3 * m) ν ∧ ν ≠ 0 ∧ (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = -lam / ν ∧
      y₁ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₁ + 1 / ν ∧
      y₂ = (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ * x₂ + 1 / ν := by
    by_cases hx : x₁ = x₂
    · have hyy : y₁ = y₂ := by
        rcases Y_eq_of_X_eq h₁.1 h₂.1 hx with h | h
        · exact h
        · exact absurd ⟨hx, h⟩ hxy
      subst hx hyy
      have hy' : y₁ ≠ (shortCurve A).toAffine.negY x₁ y₁ := fun h => hxy ⟨rfl, h⟩
      have h2 : (2 : K) ≠ 0 := by
        intro h2
        apply hy'
        rw [shortCurve_negY]
        linear_combination y₁ * h2
      have hslope : (shortCurve A).toAffine.slope x₁ x₁ y₁ y₁ =
          (3 * x₁ ^ 2 + A) / (y₁ - -y₁) := by
        rw [Affine.slope_of_Y_ne rfl hy']; simp
      obtain ⟨lam, ν, h1, h2, h3, h4, h5⟩ := formal_tangent_line hA hm h2 hy₁ e₁ ht₁ hw₁
      exact ⟨lam, ν, h1, h2, h3, by rw [hslope, h4], by rw [hslope]; exact h5,
        by rw [hslope]; exact h5⟩
    · have hslope : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        Affine.slope_of_X_ne hx
      obtain ⟨lam, ν, h1, h2, h3, h4, h5, h6⟩ :=
        formal_chord_line hA hm hy₁ hy₂ e₁ e₂ ht₁ ht₂ hw₁ hw₂ hx
      exact ⟨lam, ν, h1, h2, h3, by rw [hslope, h4], by rw [hslope]; exact h5,
        by rw [hslope]; exact h6⟩
  have h₃ := nonsingular_add h₁ h₂ hxy
  refine ⟨_, _, h₃, rfl, ?_⟩
  have eX : (shortCurve A).toAffine.addX x₁ x₂ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂ := by
    rw [Affine.addX, shortCurve_a₁, shortCurve_a₂]; ring
  have eY : (shortCurve A).toAffine.addY x₁ x₂ y₁ ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂) =
      -((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ *
        ((shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ ^ 2 - x₁ - x₂) + 1 / ν) := by
    rw [Affine.addY, Affine.negAddY, eX, shortCurve_negY]
    linear_combination -hc₁
  have e₃ := (shortCurve_equation_iff A _ _).mp h₃.1
  rw [eX, eY] at e₃ ⊢
  generalize hℓ : (shortCurve A).toAffine.slope x₁ x₂ y₁ y₂ = ℓ at hℓν hc₁ hc₂ e₃ ⊢
  exact formal_third_point_five hA hm h₁.1 h₂.1 hxy hℓ hy₁ hy₂ ht₁ ht₂ hlam hν hν0 hℓν hc₁ hc₂ e₃

end Chord

omit [DecidableEq K] in
theorem zCoord_neg' (P : (shortCurve A).toAffine.Point) : zCoord (-P) = -zCoord P := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [point_zero_eq]
  · rw [Point.neg_some, zCoord_some, zCoord_some, shortCurve_negY]; ring

/-- **Item 1.** For `k ≥ 1` and `P, Q ∈ W_k`, `v(z(P + Q) - z(P) - z(Q)) ≥ 5k`. -/
theorem zCoord_add_sub_ge (hA : 0 ≤ v A) {k : ℤ} (hk : 1 ≤ k)
    {P Q : (shortCurve A).toAffine.Point} (hP : P ∈ formalFilt A hA k)
    (hQ : Q ∈ formalFilt A hA k) :
    Vge v (5 * k) (zCoord (P + Q) - zCoord P - zCoord Q) := by
  have hA' : Vge v 0 A := hA
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [point_zero_eq, zero_add, zCoord_zero, sub_zero, sub_self]; exact Vge.zero _
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [point_zero_eq, add_zero, zCoord_zero, sub_zero, sub_self]; exact Vge.zero _
  by_cases hs : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0
  · have hQ' : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ := eq_neg_of_add_eq_zero_right hs
    rw [hs, hQ', zCoord_neg', zCoord_zero]
    ring_nf; exact Vge.zero _
  obtain ⟨N₁, -, hy₁, ht₁, hw₁, hz₁⟩ := level_of_mem_W1 hA h₁ hP.1
  obtain ⟨N₂, -, hy₂, ht₂, hw₂, hz₂⟩ := level_of_mem_W1 hA h₂ hQ.1
  have hk₁ : k ≤ N₁ := by have := hP.2; rw [hz₁] at this; exact_mod_cast this
  have hk₂ : k ≤ N₂ := by have := hQ.2; rw [hz₂] at this; exact_mod_cast this
  obtain ⟨x₃, y₃, h₃, heq, hE⟩ := chord_add_five hA' hk h₁ h₂ hy₁ hy₂
    ((vge_iff_of_eq ht₁).mpr hk₁) ((vge_iff_of_eq ht₂).mpr hk₂)
    ((vge_iff_of_eq hw₁).mpr (by omega)) ((vge_iff_of_eq hw₂).mpr (by omega)) hs
  rw [heq, zCoord_some, zCoord_some, zCoord_some]
  have : -x₃ / y₃ - -x₁ / y₁ - -x₂ / y₂ = -(x₃ / y₃ - x₁ / y₁ - x₂ / y₂) := by ring
  rw [this]; exact hE.neg

/-- **Item 2.** For `k ≥ 1`, `Q ∈ W_k` and `n ∈ ℕ`, `v(z([n]Q) - n z(Q)) ≥ 5k`. -/
theorem zCoord_nsmul_sub_ge (hA : 0 ≤ v A) {k : ℤ} (hk : 1 ≤ k)
    {Q : (shortCurve A).toAffine.Point} (hQ : Q ∈ formalFilt A hA k) (n : ℕ) :
    Vge v (5 * k) (zCoord (n • Q) - n * zCoord Q) := by
  induction n with
  | zero =>
    rw [zero_nsmul, zCoord_zero, Nat.cast_zero, zero_mul, sub_zero]
    exact Vge.zero _
  | succ n ih =>
    have hn : n • Q ∈ formalFilt A hA k := (formalFilt A hA k).nsmul_mem hQ n
    have := (zCoord_add_sub_ge hA hk hn hQ).add ih
    rw [succ_nsmul]
    convert this using 1
    push_cast; ring

/-- **Item 3, one step.** If `v(q) = e` with `0 ≤ e ≤ 4`, then `[q] W_k ⊆ W_{k + e}`. -/
theorem nsmul_mem_formalFilt_add (hA : 0 ≤ v A) {k : ℤ} {q : ℕ} {e : ℤ}
    (hq : v (q : K) = e) (he0 : 0 ≤ e) (he4 : e ≤ 4) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) : q • Q ∈ formalFilt A hA (k + e) := by
  rcases Q with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, nsmul_zero]; exact (formalFilt A hA (k + e)).zero_mem
  obtain ⟨N, hN, -, -, -, hz, -⟩ := formal_val_x_y hA h hQ.1
  have hkN : k ≤ N := by have := hQ.2; rw [hz] at this; exact_mod_cast this
  have hQN : Point.some x y h ∈ formalFilt A hA N := ⟨hQ.1, by rw [hz]⟩
  have herr := zCoord_nsmul_sub_ge hA hN hQN q
  have hqz : v ((q : K) * zCoord (Point.some x y h)) = (e + N : ℤ) := val_mul_coe hq hz
  have hW := (zsmul_mem_W1 hA (P := Point.some x y h) hQ.1 q).1
  rw [natCast_zsmul] at hW
  refine ⟨hW, ?_⟩
  have hsum : zCoord (q • Point.some x y h) =
      (zCoord (q • Point.some x y h) - q * zCoord (Point.some x y h)) +
        q * zCoord (Point.some x y h) := by ring
  rw [hsum]
  exact ((herr.mono (by omega)).add ((vge_iff_of_eq hqz).mpr (by omega)))

/-- **Item 3.** If `v(q) = e` with `0 ≤ e ≤ 4`, then `[qᵃ n] W_k ⊆ W_{k + a e}`. -/
theorem nsmul_mem_formalFilt_of_val (hA : 0 ≤ v A) {k : ℤ} {q : ℕ} {e : ℤ}
    (hq : v (q : K) = e) (he0 : 0 ≤ e) (he4 : e ≤ 4) {Q : (shortCurve A).toAffine.Point}
    (hQ : Q ∈ formalFilt A hA k) (a n : ℕ) : (q ^ a * n) • Q ∈ formalFilt A hA (k + a * e) := by
  have hpow : ∀ a : ℕ, q ^ a • Q ∈ formalFilt A hA (k + a * e) := by
    intro a
    induction a with
    | zero => simpa using hQ
    | succ a ih =>
      rw [pow_succ, mul_nsmul]
      have := nsmul_mem_formalFilt_add hA hq he0 he4 ih
      convert this using 2; push_cast; ring
  rw [mul_nsmul]
  exact (formalFilt A hA (k + a * e)).nsmul_mem (hpow a) n

end ZInQ.Size
