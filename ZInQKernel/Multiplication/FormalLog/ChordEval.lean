import ZInQKernel.Multiplication.FormalLog.Eval
import ZInQKernel.Multiplication.FormalLog.ChordAlgebra

/-!
# `z(P + Q) = F(z(P), z(Q))`

Blueprint: `multiplication/local/formal-group-law.md`, part 2 (the evaluation).

Let `K` be a complete `ℤᵐ⁰`-valued field of characteristic `0`, `v(A) ≥ 0`, and
`P, Q ∈ W₁(K)` with `tᵢ = z(P), z(Q)`. Evaluating the relations of `Relations.lean` at
`(t₁, t₂)` (evaluation is a ring homomorphism on integral series, `Eval.lean`):
`Ω₁ = ω(t₁) = ω(P)`, `Ω₂ = ω(Q)` (`omegaSeries_hasSum`), `Λ = λ(t₁, t₂)` satisfies
`Λ(t₂ - t₁) = Ω₂ - Ω₁`, and for `t₁ = t₂` also `Λ(1 - 2A t₁ Ω₁) = 3t₁² + AΩ₁²` (from
`∂₁λ (T₂ - T₁) = λ - ω'(T₁)`). So `ω = Λz + (Ω₁ - Λt₁)` is the chord (or tangent) through `P`
and `Q`, and the chord formula `zCoord_add_of_line` gives `F(t₁, t₂) = z(P + Q)`
(`hasSum_formalAdd`); the cases `P = O`, `Q = O`, `P + Q = O` are direct.
-/

namespace ZInQ.Mult

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Affine WithZero

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K]

/-- `ω(z(P)) = ω(P)` on `W₁(K)` (including `P = O`). -/
theorem hasSum_omegaCoord {A : K} (hA : 0 ≤ vK K A) [DecidableEq K]
    {P : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) :
    HasSum (fun k => PowerSeries.coeff k (omegaSeries A) * zCoord P ^ k) (omegaCoord P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, zCoord_zero]
    have : omegaCoord (0 : (shortCurve A).toAffine.Point) = 0 := rfl
    rw [this]
    convert hasSum_single (f := fun k : ℕ => PowerSeries.coeff k (omegaSeries A) * (0 : K) ^ k) 0
      (fun k hk => by simp [hk]) using 1
    simp [coeff_omegaSeries, omegaCoeff_zero]
  · rw [zCoord_some, omegaCoord_some]
    exact omegaSeries_hasSum hA h hP

omit [Valued K ℤᵐ⁰] [CompleteSpace K] in
theorem omegaCoord_neg [DecidableEq K] {A : K} (P : (shortCurve A).toAffine.Point) :
    omegaCoord (-P) = -omegaCoord P := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [point_zero_eq, neg_zero]; exact neg_zero.symm
  · rw [Point.neg_some, omegaCoord_some, omegaCoord_some, shortCurve_negY]; ring

omit [Valued K ℤᵐ⁰] [CompleteSpace K] in
theorem omegaCoord_zero' {A : K} : omegaCoord (0 : (shortCurve A).toAffine.Point) = 0 := rfl

omit [CompleteSpace K] in
/-- **The chord formula on `W₁(K)`**: if `ω = Λ z + (ω(P) - Λ z(P))` passes through `P` and `Q`
(and is the tangent if `P = Q`), then `z(P + Q) = z(P) + z(Q) + 2AΛN/(1 + AΛ²)` with
`N = ω(P) - Λ z(P)`. -/
theorem zCoord_add_eq_of_line [CharZero K] [DecidableEq K] {A : K} (hA : 0 ≤ vK K A)
    {P Q : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) (hQ : Q ∈ W1 (vK K) A)
    {Λ : K} (hchord : Λ * (zCoord Q - zCoord P) = omegaCoord Q - omegaCoord P)
    (htan : P = Q →
      Λ * (1 - 2 * A * zCoord P * omegaCoord P) = 3 * zCoord P ^ 2 + A * omegaCoord P ^ 2)
    (hD : 1 + A * Λ ^ 2 ≠ 0) :
    zCoord (P + Q) = zCoord P + zCoord Q +
      2 * A * Λ * (omegaCoord P - Λ * zCoord P) / (1 + A * Λ ^ 2) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rw [point_zero_eq, zero_add, zCoord_zero, omegaCoord_zero']; ring
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rw [point_zero_eq, add_zero, zCoord_zero, omegaCoord_zero'] at *
    rw [show omegaCoord (Point.some x₁ y₁ h₁) - Λ * zCoord (Point.some x₁ y₁ h₁) = 0 by
      linear_combination hchord]
    ring
  obtain ⟨N₁, -, -, -, hy₁, -, -, -⟩ := formal_val_x_y hA h₁ hP
  obtain ⟨N₂, -, -, -, hy₂, -, -, -⟩ := formal_val_x_y hA h₂ hQ
  by_cases hs : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = 0
  · have hQ' : Point.some x₂ y₂ h₂ = -Point.some x₁ y₁ h₁ := (neg_eq_of_add_eq_zero_right hs).symm
    rw [hs, zCoord_zero]
    rw [hQ', zCoord_neg, omegaCoord_neg] at hchord
    rw [hQ', zCoord_neg]
    have hN : omegaCoord (Point.some x₁ y₁ h₁) - Λ * zCoord (Point.some x₁ y₁ h₁) = 0 := by
      have : 2 * (omegaCoord (Point.some x₁ y₁ h₁) - Λ * zCoord (Point.some x₁ y₁ h₁)) = 0 := by
        linear_combination hchord
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [hN]; ring
  have hsum : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ ∈ W1 (vK K) A := by
    have := (formalNbhd A hA).add_mem ((mem_formalNbhd_iff hA _).mpr hP)
      ((mem_formalNbhd_iff hA _).mpr hQ)
    exact (mem_formalNbhd_iff hA _).mp this
  have hy₃ : ∀ x y (h : (shortCurve A).toAffine.Nonsingular x y),
      Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some x y h → y ≠ 0 := by
    intro x y h he
    rw [he] at hsum
    obtain ⟨N, -, -, -, hy, -⟩ := formal_val_x_y hA h hsum
    exact hy
  rw [zCoord_some, zCoord_some, omegaCoord_some, omegaCoord_some] at hchord
  have := zCoord_add_of_line h2 h₁ h₂ hy₁ hy₂ hs hy₃ hD hchord (fun hx hy => by
    subst hx hy
    have := htan rfl
    rw [zCoord_some, omegaCoord_some] at this
    exact this)
  rw [this, zCoord_some, zCoord_some, omegaCoord_some]

/-- **`z(P + Q) = F(z(P), z(Q))`** for `P, Q ∈ W₁(K)`, the double series converging. -/
theorem hasSum_formalAdd [CharZero K] [DecidableEq K] {A : K} (hA : 0 ≤ vK K A)
    {P Q : (shortCurve A).toAffine.Point} (hP : P ∈ W1 (vK K) A) (hQ : Q ∈ W1 (vK K) A) :
    HasSum (fun n => coeff n (formalAdd A) * monoVal (zCoord P) (zCoord Q) n)
      (zCoord (P + Q)) := by
  have h₁ : 1 ≤ vK K (zCoord P) := one_le_val_zCoord hA hP
  have h₂ : 1 ≤ vK K (zCoord Q) := one_le_val_zCoord hA hQ
  have iL := MvIntegral.chordSlope hA
  have iω₁ := MvIntegral.omegaFst hA
  have iω₂ := MvIntegral.omegaSnd hA
  have iI := MvIntegral.chordInv hA
  have iC := MvIntegral.C hA
  have hΩ₁ : ev2 (zCoord P) (zCoord Q) (omegaFst A) = omegaCoord P := by
    rw [omegaFst_eq_subst]
    exact (hasSum_ev2_subst_X_zero (hasSum_omegaCoord hA hP)).tsum_eq
  have hΩ₂ : ev2 (zCoord P) (zCoord Q) (omegaSnd A) = omegaCoord Q :=
    (hasSum_ev2_subst_X_one (hasSum_omegaCoord hA hQ)).tsum_eq
  set Λ := ev2 (zCoord P) (zCoord Q) (chordSlope A) with hΛ
  have hchord : Λ * (zCoord Q - zCoord P) = omegaCoord Q - omegaCoord P := by
    have := congrArg (ev2 (zCoord P) (zCoord Q)) (chordSlope_mul_sub A)
    rw [ev2_mul h₁ h₂ iL ((MvIntegral.X 1).sub (MvIntegral.X 0)),
      ev2_sub h₁ h₂ (MvIntegral.X 1) (MvIntegral.X 0), ev2_sub h₁ h₂ iω₂ iω₁, ev2_X_zero,
      ev2_X_one, hΩ₁, hΩ₂] at this
    exact this
  have hInv : ev2 (zCoord P) (zCoord Q) (chordInv A) * (1 + A * Λ ^ 2) = 1 := by
    have := congrArg (ev2 (zCoord P) (zCoord Q)) (chordInv_mul A)
    rw [ev2_mul h₁ h₂ iI (MvIntegral.one.add (iC.mul (iL.pow 2))),
      ev2_add h₁ h₂ MvIntegral.one (iC.mul (iL.pow 2)), ev2_mul h₁ h₂ iC (iL.pow 2),
      ev2_pow h₁ h₂ iL, ev2_one, ev2_C] at this
    exact this
  have hD : 1 + A * Λ ^ 2 ≠ 0 := right_ne_zero_of_mul_eq_one hInv
  have htan : P = Q →
      Λ * (1 - 2 * A * zCoord P * omegaCoord P) = 3 * zCoord P ^ 2 + A * omegaCoord P ^ 2 := by
    intro hPQ
    subst hPQ
    have iM := iL.pderiv 0
    have iδ := MvIntegral.subst_X_derivative_omega hA 0
    have r4 := congrArg (ev2 (zCoord P) (zCoord P)) (pderiv_zero_chordSlope_mul A)
    rw [ev2_mul h₁ h₂ iM ((MvIntegral.X 1).sub (MvIntegral.X 0)),
      ev2_sub h₁ h₂ (MvIntegral.X 1) (MvIntegral.X 0), ev2_X_zero, ev2_X_one,
      ev2_sub h₁ h₂ iL iδ, sub_self, mul_zero, eq_comm, sub_eq_zero] at r4
    have r5 := congrArg (ev2 (zCoord P) (zCoord P)) (subst_derivative_omega_mul_fst A)
    have iT := (MvIntegral.C (show 0 ≤ vK K (2 * A) from
      ((vge_ofNat (v := vK K) 2).mul hA).mono (by simp)))
    rw [show (2 : MvPowerSeries (Fin 2) K) * MvPowerSeries.C A = MvPowerSeries.C (2 * A) by
        rw [map_mul, map_ofNat],
      show (3 : MvPowerSeries (Fin 2) K) = MvPowerSeries.C 3 by rw [map_ofNat],
      ev2_mul h₁ h₂ iδ (MvIntegral.one.sub ((iT.mul (MvIntegral.X 0)).mul iω₁)),
      ev2_sub h₁ h₂ MvIntegral.one ((iT.mul (MvIntegral.X 0)).mul iω₁),
      ev2_mul h₁ h₂ (iT.mul (MvIntegral.X 0)) iω₁, ev2_mul h₁ h₂ iT (MvIntegral.X 0),
      ev2_add h₁ h₂ ((MvIntegral.C (vge_ofNat (v := vK K) 3)).mul ((MvIntegral.X 0).pow 2))
        (iC.mul (iω₁.pow 2)),
      ev2_mul h₁ h₂ (MvIntegral.C (vge_ofNat (v := vK K) 3)) ((MvIntegral.X 0).pow 2),
      ev2_mul h₁ h₂ iC (iω₁.pow 2), ev2_pow h₁ h₂ (MvIntegral.X 0), ev2_pow h₁ h₂ iω₁,
      ev2_one, ev2_C, ev2_C, ev2_C, ev2_X_zero, hΩ₁, ← r4] at r5
    rw [hΛ]; exact r5
  have hF : ev2 (zCoord P) (zCoord Q) (formalAdd A) = zCoord P + zCoord Q +
      2 * A * Λ * (omegaCoord P - Λ * zCoord P) / (1 + A * Λ ^ 2) := by
    have i2 : MvIntegral (MvPowerSeries.C (2 * A) : MvPowerSeries (Fin 2) K) :=
      MvIntegral.C (((vge_ofNat (v := vK K) 2).mul hA).mono (by simp))
    have iν : MvIntegral (omegaFst A - chordSlope A * MvPowerSeries.X 0) :=
      iω₁.sub (iL.mul (MvIntegral.X 0))
    rw [formalAdd_eq, show (2 : MvPowerSeries (Fin 2) K) * MvPowerSeries.C A =
        MvPowerSeries.C (2 * A) by rw [map_mul, map_ofNat],
      ev2_add h₁ h₂ ((MvIntegral.X 0).add (MvIntegral.X 1))
      (((i2.mul iL).mul iν).mul iI), ev2_add h₁ h₂ (MvIntegral.X 0) (MvIntegral.X 1), ev2_X_zero,
      ev2_X_one, ev2_mul h₁ h₂ ((i2.mul iL).mul iν) iI, ev2_mul h₁ h₂ (i2.mul iL) iν,
      ev2_sub h₁ h₂ iω₁ (iL.mul (MvIntegral.X 0)), ev2_mul h₁ h₂ iL (MvIntegral.X 0),
      ev2_X_zero, hΩ₁, ev2_mul h₁ h₂ i2 iL, ev2_C, ← hΛ, eq_one_div_of_mul_eq_one_left hInv]
    ring
  rw [zCoord_add_eq_of_line hA hP hQ hchord htan hD, ← hF]
  exact hasSum_ev2 h₁ h₂ (MvIntegral.formalAdd hA)

end ZInQ.Mult
