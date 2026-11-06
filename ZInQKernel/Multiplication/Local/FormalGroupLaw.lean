import ZInQKernel.Multiplication.Local.FormalGroup
import ZInQKernel.Multiplication.Local.Analytic

/-!
# The formal group law of `y² = x³ + A x`

Blueprint: `multiplication/local/formal-group-law.md`.

1. `omegaSeries A` is the unique power series `ω(T)` with `ω = T³ + A T ω²`
   (`omegaSeries_eq`, `omegaSeries_unique`); it is `T³ (1 + ⋯)` and has coefficients in
   `ℤ[A]` (here: in any ring containing `A`, in particular in the valuation ring `𝒪`; over a
   valued field, `omegaSeries_integral`). For an affine point of `W₁(K)` of a complete field,
   `-1/y = ω(-x/y)` (`omegaSeries_hasSum`).
2. `formalAdd A = T₁ + T₂ + 2Aλν/(1 + Aλ²)` with `λ(T₁, T₂) = Σ ω_{i+j+1} T₁ⁱ T₂ʲ` (the
   difference quotient of `ω`) and `ν = ω(T₁) - λ T₁` is the chord construction with power
   series in place of elements. `formalGroupLaw_exists`: it is a commutative formal group law over
   `𝒪` with inverse `-T`, and `z(P + Q) = F(z(P), z(Q))` on `W₁(K)`.
-/

namespace ZInQ.Mult

open Finset PowerSeries WeierstrassCurve WeierstrassCurve.Affine Filter Topology WithZero

section Ring

variable {R : Type*} [CommRing R]

/-- The coefficients of `ω`: `ω_n = [n = 3] + A Σ_{i + j = n - 1} ω_i ω_j` for `n ≥ 1`,
`ω_0 = 0`. -/
def omegaCoeff (A : R) (n : ℕ) : R :=
  (if n = 3 then 1 else 0) +
    if h : n = 0 then 0 else
      A * ∑ x ∈ (antidiagonal (n - 1)).attach, omegaCoeff A x.1.1 * omegaCoeff A x.1.2
termination_by n
decreasing_by
  all_goals
    have := Finset.HasAntidiagonal.mem_antidiagonal.mp x.2
    omega

theorem omegaCoeff_eq (A : R) (n : ℕ) :
    omegaCoeff A n = (if n = 3 then 1 else 0) +
      if n = 0 then 0 else A * ∑ x ∈ antidiagonal (n - 1), omegaCoeff A x.1 * omegaCoeff A x.2 := by
  rw [omegaCoeff]
  congr 1
  split_ifs
  · rfl
  · congr 1
    exact Finset.sum_attach (antidiagonal (n - 1)) (fun x => omegaCoeff A x.1 * omegaCoeff A x.2)

theorem omegaCoeff_zero (A : R) : omegaCoeff A 0 = 0 := by
  rw [omegaCoeff_eq]; simp

theorem omegaCoeff_one (A : R) : omegaCoeff A 1 = 0 := by
  rw [omegaCoeff_eq]; simp [omegaCoeff_zero]

theorem omegaCoeff_two (A : R) : omegaCoeff A 2 = 0 := by
  rw [omegaCoeff_eq]
  simp [Finset.Nat.antidiagonal_succ, omegaCoeff_zero, omegaCoeff_one]

theorem omegaCoeff_three (A : R) : omegaCoeff A 3 = 1 := by
  rw [omegaCoeff_eq]
  simp [Finset.Nat.antidiagonal_succ, omegaCoeff_zero, omegaCoeff_one, omegaCoeff_two]

/-- The power series `ω(T) = T³ + A T⁴ ω'…` with `ω = T³ + A T ω²`. -/
def omegaSeries (A : R) : PowerSeries R := PowerSeries.mk (omegaCoeff A)

theorem coeff_omegaSeries (A : R) (n : ℕ) : coeff n (omegaSeries A) = omegaCoeff A n :=
  coeff_mk _ _

/-- The coefficient of `Tⁿ` in `T³ + A T f²`. -/
theorem coeff_omega_rhs (A : R) (f : PowerSeries R) (n : ℕ) :
    coeff n (X ^ 3 + C A * X * f ^ 2) = (if n = 3 then 1 else 0) +
      if n = 0 then 0 else A * ∑ x ∈ antidiagonal (n - 1), coeff x.1 f * coeff x.2 f := by
  rw [map_add, coeff_X_pow, mul_assoc, coeff_C_mul]
  congr 1
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, sq, coeff_mul]; simp

/-- **Part 1.** `ω = T³ + A T ω²`. -/
theorem omegaSeries_eq (A : R) : omegaSeries A = X ^ 3 + C A * X * omegaSeries A ^ 2 := by
  ext n
  rw [coeff_omega_rhs, coeff_omegaSeries, omegaCoeff_eq]
  simp only [coeff_omegaSeries]

/-- **Part 1.** `ω` is the unique solution of `ω = T³ + A T ω²`. -/
theorem omegaSeries_unique (A : R) {f : PowerSeries R} (hf : f = X ^ 3 + C A * X * f ^ 2) :
    f = omegaSeries A := by
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hf, coeff_omega_rhs, coeff_omegaSeries, omegaCoeff_eq]
    congr 1
    split_ifs with h
    · rfl
    · congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      rw [ih x.1 (by omega), ih x.2 (by omega), coeff_omegaSeries, coeff_omegaSeries]

/-- **Part 1.** `ω = T³ (1 + ⋯)`: the coefficients of `1, T, T²` vanish and that of `T³` is `1`. -/
theorem omegaSeries_lowCoeffs (A : R) :
    coeff 0 (omegaSeries A) = 0 ∧ coeff 1 (omegaSeries A) = 0 ∧ coeff 2 (omegaSeries A) = 0 ∧
      coeff 3 (omegaSeries A) = 1 := by
  simp only [coeff_omegaSeries, omegaCoeff_zero, omegaCoeff_one, omegaCoeff_two, omegaCoeff_three,
    and_self]

theorem omegaCoeff_map {S : Type*} [CommRing S] (f : R →+* S) (A : R) (n : ℕ) :
    f (omegaCoeff A n) = omegaCoeff (f A) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [omegaCoeff_eq, omegaCoeff_eq (f A), map_add, apply_ite f, apply_ite f, map_one, map_zero]
    congr 1
    split_ifs
    · rfl
    · rw [map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      rw [map_mul, ih x.1 (by omega), ih x.2 (by omega)]

/-! ### The formal addition law -/

/-- The difference quotient `λ(T₁, T₂) = (ω(T₂) - ω(T₁))/(T₂ - T₁) = Σ ω_{i+j+1} T₁ⁱ T₂ʲ`. -/
def chordSlope (A : R) : MvPowerSeries (Fin 2) R := fun n => omegaCoeff A (n 0 + n 1 + 1)

/-- `ω(T₁)` as a power series in two variables. -/
def omegaFst (A : R) : MvPowerSeries (Fin 2) R := fun n => if n 1 = 0 then omegaCoeff A (n 0) else 0

/-- **The formal group law** `F(T₁, T₂) = T₁ + T₂ + 2Aλν/(1 + Aλ²)`, `ν = ω(T₁) - λ T₁`. -/
noncomputable def formalAdd (A : R) : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.X 0 + MvPowerSeries.X 1 +
    MvPowerSeries.C (2 * A) * chordSlope A * (omegaFst A - chordSlope A * MvPowerSeries.X 0) *
      MvPowerSeries.invOfUnit (1 + MvPowerSeries.C A * chordSlope A ^ 2) 1

end Ring

/-! ### Over a valued field -/

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- **Part 1.** If `v(A) ≥ 0`, the coefficients of `ω` lie in the valuation ring. -/
theorem omegaSeries_integral {A : K} (hA : 0 ≤ vK K A) (n : ℕ) :
    0 ≤ vK K (coeff n (omegaSeries A)) := by
  rw [coeff_omegaSeries]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [omegaCoeff_eq]
    have h0 : Vge (vK K) 0 (if n = 3 then (1 : K) else 0) := by
      split_ifs
      · show ((0 : ℤ) : WithTop ℤ) ≤ vK K 1; rw [(vK K).map_one]; rfl
      · exact Vge.zero 0
    refine Vge.add h0 ?_
    split_ifs with hn
    · exact Vge.zero 0
    · have := (show Vge (vK K) 0 A from hA).mul (Vge.sum_of_le (m := 0) (s := antidiagonal (n - 1))
        fun x hx => by
          have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
          have h1 : Vge (vK K) 0 (omegaCoeff A x.1) := ih x.1 (by omega)
          have h2 : Vge (vK K) 0 (omegaCoeff A x.2) := ih x.2 (by omega)
          exact (h1.mul h2).mono (by simp))
      simpa using this

/-- **Part 1.** For an affine point `(x, y)` of `W₁(K)` over a complete field,
`-1/y = ω(-x/y)`, the series converging since `v(-x/y) ≥ 1`. -/
theorem omegaSeries_hasSum [CompleteSpace K] [DecidableEq K] {A : K} (hA : 0 ≤ vK K A) {x y : K}
    (h : (shortCurve A).toAffine.Nonsingular x y) (hx : vK K x < 0) :
    HasSum (fun n => coeff n (omegaSeries A) * (-x / y) ^ n) (-1 / y) := by
  sorry

variable [DecidableEq K]

/-- **Part 2: the formal group law.** For `A` in the valuation ring `𝒪` of a complete
`ℤᵐ⁰`-valued field `K` of characteristic `0`, the chord series `formalAdd A ∈ 𝒪⟦T₁, T₂⟧` is a
commutative formal group law `F(T₁, T₂) = T₁ + T₂ + ⋯` with formal inverse `i(T) = -T`
(`F(T, -T) = 0`), and `z(P + Q) = F(z(P), z(Q))` for `P, Q ∈ W₁(K)`, the double series
converging. -/
theorem formalGroupLaw_exists [CompleteSpace K] [CharZero K] (A : Valued.integer K) :
    ∃ F : FormalGroup (Valued.integer K), F.toPowerSeries = formalAdd A ∧ F.IsComm ∧
      MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (Valued.integer K)), -PowerSeries.X]
        F.toPowerSeries = 0 ∧
      ∀ P ∈ W1 (vK K) (A : K), ∀ Q ∈ W1 (vK K) (A : K),
        HasSum (fun n : Fin 2 →₀ ℕ =>
          ((MvPowerSeries.coeff n F.toPowerSeries : Valued.integer K) : K) *
            zCoord P ^ n 0 * zCoord Q ^ n 1) (zCoord (P + Q)) := by
  sorry

end ZInQ.Mult
