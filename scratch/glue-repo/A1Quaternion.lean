import Mathlib

/-!
# glue-repo, step A1: the quaternion datum and the Riemann form (N5 L405-418)

`B = (2,-3)` is Mathlib's `ℍ[ℚ, 2, 0, -3]` (`i² = 2`, `j² = -3`, `k = ij`).
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` is a genuine `Subring B`, and `μ = 2j + ij`.
Proved here (no `sorry`): `μ² = -6`; `𝒪` is a subring (an order) with reduced discriminant 6
(`det Trd(eₐ e_b) = -36`); the Gram matrix of `E(x,y) = Trd(μ⁻¹ x ȳ)` in N5's basis is N5's
matrix, with determinant 1; `E` is alternating and `E(ax, y) = E(x, a† y)` with
`a† = μ⁻¹ ā μ`; `†` is an anti-involution; `†` is positive: `Trd(a a†) > 0` for `a ≠ 0`.
-/

open Quaternion

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

namespace GlueRepo.A1

/-- The quaternion algebra `B = (2,-3)` over `ℚ`. -/
abbrev B := ℍ[ℚ, 2, 0, -3]

/-- Reduced trace (`c₂ = 0`, so `Trd x = x + x̄ = 2 re x`). -/
def trd (x : B) : ℚ := 2 * x.re

theorem trd_eq (x : B) : ((trd x : ℚ) : B) = x + star x := by
  ext <;> simp [trd] <;> ring

/-- `μ = 2j + ij`. -/
def μ : B := ⟨0, 0, 2, 1⟩
/-- `μ⁻¹ = -μ/6`. -/
def μinv : B := ⟨0, 0, -1/3, -1/6⟩

theorem μ_mul_μ : μ * μ = -6 := by ext <;> simp [μ] <;> norm_num
theorem μ_mul_μinv : μ * μinv = 1 := by ext <;> simp [μ, μinv] <;> norm_num
theorem μinv_mul_μ : μinv * μ = 1 := by ext <;> simp [μ, μinv] <;> norm_num

/-- N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)`. -/
def e : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- The `ℤ`-combination `n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+ij)/2`. -/
def comb (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + n 2 / 2, n 1 + n 3 / 2, n 2 / 2, n 3 / 2⟩

theorem comb_eq (n : Fin 4 → ℤ) : comb n = ∑ k, (n k : ℚ) • e k := by
  ext <;> simp [comb, e, Fin.sum_univ_four] <;> ring

/-- The structure constants of `𝒪` (integer polynomials; `scratch/glue-repo/compute.py` §4). -/
def combMul (n m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem comb_mul (n m : Fin 4 → ℤ) : comb n * comb m = comb (combMul n m) := by
  ext <;> simp [comb, combMul] <;> push_cast <;> ring

/-- The order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` as a subring of `B`. -/
def O : Subring B where
  carrier := Set.range comb
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨combMul n m, (comb_mul n m).symm⟩
  one_mem' := ⟨![1, 0, 0, 0], by ext <;> simp [comb]⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, by ext <;> simp [comb] <;> ring⟩
  zero_mem' := ⟨0, by ext <;> simp [comb]⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, by ext <;> simp [comb] <;> ring⟩

theorem e_mem (k : Fin 4) : e k ∈ O := by
  fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [comb, e]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [comb, e]⟩
  · exact ⟨![0, 0, 1, 0], by ext <;> simp [comb, e]⟩
  · exact ⟨![0, 0, 0, 1], by ext <;> simp [comb, e]⟩

/-- `𝒪` is closed under conjugation. -/
theorem star_mem {x : B} (hx : x ∈ O) : star x ∈ O := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨![n 0 + n 2, -n 1, -n 2, -n 3], by ext <;> simp [comb] <;> ring⟩

/-- The trace form `Trd(eₐ e_b)` of `𝒪` has determinant `-36 = -(disc)²`: reduced discriminant 6. -/
theorem trace_form :
    (Matrix.of fun a b => trd (e a * e b)) = !![2, 0, 1, 0; 0, 4, 0, 2; 1, 0, -1, 0; 0, 2, 0, 4] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [e, trd] <;> norm_num

theorem det_trace_form :
    (Matrix.of fun a b => trd (e a * e b)).det = -36 := by
  rw [trace_form, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  norm_num

/-- N5's form `E(x, y) = Trd(μ⁻¹ x ȳ)`. -/
def E (x y : B) : ℚ := trd (μinv * x * star y)

/-- The Gram matrix of `E` in N5's basis is the matrix printed at N5 L414-416. -/
theorem gram_E :
    (Matrix.of fun a b => E (e a) (e b)) = !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [E, e, μinv, trd] <;> norm_num

/-- ... with determinant one: `E` is a principal (unimodular) form on `𝒪`. -/
theorem det_gram_E : (Matrix.of fun a b => E (e a) (e b)).det = 1 := by
  rw [gram_E, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix, Fin.succAbove]
  norm_num

/-- `E` is integral on `𝒪 × 𝒪`. -/
theorem E_comb (n m : Fin 4 → ℤ) :
    E (comb n) (comb m) = ((-n 0 * m 2 + n 0 * m 3 + n 1 * m 2 - 2 * n 1 * m 3
      + n 2 * m 0 - n 2 * m 1 - n 3 * m 0 + 2 * n 3 * m 1 : ℤ) : ℚ) := by
  simp [E, comb, μinv, trd]; push_cast; ring

/-- `E` is alternating. -/
theorem E_self (x : B) : E x x = 0 := by
  simp [E, μinv, trd]; ring

theorem E_antisymm (x y : B) : E y x = - E x y := by
  simp [E, μinv, trd]; ring

/-- The Rosati involution `a ↦ μ⁻¹ ā μ`. -/
def ros (a : B) : B := μinv * star a * μ

/-- `E(ax, y) = E(x, a† y)`: `†` is the Rosati involution of `E`. -/
theorem E_ros (a x y : B) : E (a * x) y = E x (ros a * y) := by
  simp [E, ros, μ, μinv, trd]; ring

theorem ros_ros (a : B) : ros (ros a) = a := by
  ext <;> simp [ros, μ, μinv] <;> ring

theorem ros_mul (a b : B) : ros (a * b) = ros b * ros a := by
  ext <;> simp [ros, μ, μinv] <;> ring

theorem ros_add (a b : B) : ros (a + b) = ros a + ros b := by
  ext <;> simp [ros, μ, μinv] <;> ring

/-- `Trd(a a†)` for `a = x₀ + x₁ i + x₂ j + x₃ ij` (`compute.py` §1). -/
theorem trd_mul_ros (a : B) :
    trd (a * ros a) = 2 * a.re ^ 2 + 4 * a.imI ^ 2 + 18 * a.imJ ^ 2 - 48 * a.imJ * a.imK
      + 36 * a.imK ^ 2 := by
  simp [ros, μ, μinv, trd]; ring

/-- The Rosati involution is positive. -/
theorem trd_mul_ros_pos (a : B) (ha : a ≠ 0) : 0 < trd (a * ros a) := by
  rw [trd_mul_ros]
  have key : 2 * a.re ^ 2 + 4 * a.imI ^ 2 + 18 * a.imJ ^ 2 - 48 * a.imJ * a.imK + 36 * a.imK ^ 2
      = 2 * a.re ^ 2 + 4 * a.imI ^ 2 + 2 * (3 * a.imJ - 4 * a.imK) ^ 2 + 4 * a.imK ^ 2 := by ring
  rw [key]
  by_contra h
  push Not at h
  have h0 : a.re = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h1 : a.imI = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h3 : a.imK = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h2 : a.imJ = 0 := by
    have : (3 * a.imJ - 4 * a.imK) = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
    rw [h3] at this; linarith
  exact ha (by ext <;> simp [h0, h1, h2, h3])

/-- `𝒪` is stable under the Rosati involution (`μ ∈ 𝒪` normalizes `𝒪`). -/
theorem ros_mem {x : B} (hx : x ∈ O) : ros x ∈ O := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨![n 0 + 2 * n 2 - 2 * n 3, n 1 + n 2 - n 3, -3 * n 2 + 4 * n 3, -2 * n 2 + 3 * n 3],
    by ext <;> simp [comb, ros, μ, μinv] <;> push_cast <;> ring⟩

end GlueRepo.A1

#print axioms GlueRepo.A1.trd_mul_ros_pos
#print axioms GlueRepo.A1.det_gram_E
#print axioms GlueRepo.A1.E_ros
#print axioms GlueRepo.A1.det_trace_form
