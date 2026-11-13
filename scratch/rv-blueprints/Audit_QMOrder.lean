import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-!
# bp-qmmoduli, layer 1: the QM datum of discriminant 6 as a ring with a positive involution

Pure algebra, Mathlib only. This is the first concrete layer of the blueprint
`docs/research/bp-qmmoduli.md` (§3, nodes N1-N4).

* `BPQM.B = (2,−3)/ℚ` (Mathlib's `QuaternionAlgebra ℚ 2 0 (−3)`), `BPQM.O : Subring B` the maximal
  order `𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of N5 (L410-420), with its structure constants.
* The Rosati involution `x† = μ⁻¹ x̄ μ`, `μ = 2j + k`: an anti-automorphism of order 2 of `B`,
  preserving `𝒪`, positive (`trd(x x†) > 0` for `x ≠ 0`).
* N5's Riemann form `E₀(x, y) = trd(μ⁻¹ x ȳ)`: alternating, Rosati-compatible
  (`E₀(ax, y) = E₀(x, a†y)`), integral and unimodular on `𝒪`.
* **Uniqueness of the compatible polarization (lattice form).** Every alternating `ℚ`-bilinear
  form `E` on `B` with `E(ax, y) = E(x, a†y)` is `r·E₀` for a unique `r ∈ ℚ`; if moreover its Gram
  matrix on N5's basis of `𝒪` has determinant 1 (a principal polarization on `H₁ = 𝒪`), then
  `r = ±1`. This is the lattice-level content of h-trust A4 item 2.
* The Atkin–Lehner elements `w₂ = 1+i+j`, `w₃ = j`, `w₆ = μ` (reduced norms 2, 3, 6) normalize
  `𝒪`, and satisfy the relations of `W ≅ (ℤ/2)²` modulo `ℚ^×𝒪^×` that are used.
* `no_sq_eq_neg_two`: no `x ∈ B` has `x² = −2` (`ℚ(√−2)` does not embed; h-b1 M9's absent type
  `(0,2)` of elliptic elements), by 3-adic descent.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace BPQM

/-- `B = (2,−3)`: `i² = 2`, `j² = −3`, `k = ij`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-! ## §1 The maximal order `𝒪` -/

/-- The element `n₀·1 + n₁·i + n₂·(1+j)/2 + n₃·(i+k)/2` of `𝒪` with integer coordinates `n`. -/
def ofInt (n : Fin 4 → ℤ) : B :=
  ⟨n 0 + (n 2 : ℚ) / 2, n 1 + (n 3 : ℚ) / 2, (n 2 : ℚ) / 2, (n 3 : ℚ) / 2⟩

/-- N5's basis `(1, i, (1+j)/2, (i+k)/2)` (same as `PkgI1.oBasis`). -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

theorem ofInt_eq_sum (n : Fin 4 → ℤ) : ofInt n = ∑ k, (n k : ℚ) • oBasis k := by
  ext <;> simp [ofInt, oBasis, Fin.sum_univ_four] <;> ring

/-- Membership in `𝒪` (equivalent to `PkgI1.InO` by `ofInt_eq_sum`). -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ofInt n

/-- Structure constants of `𝒪` (`order_table.py`). -/
def mulCoord (n m : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

theorem ofInt_mul (n m : Fin 4 → ℤ) : ofInt n * ofInt m = ofInt (mulCoord n m) := by
  ext <;> simp [ofInt, mulCoord] <;> ring

theorem ofInt_add (n m : Fin 4 → ℤ) : ofInt n + ofInt m = ofInt (n + m) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_neg (n : Fin 4 → ℤ) : -ofInt n = ofInt (-n) := by
  ext <;> simp [ofInt] <;> ring

theorem ofInt_zero : ofInt 0 = 0 := by ext <;> simp [ofInt]

theorem ofInt_one : ofInt ![1, 0, 0, 0] = 1 := by ext <;> simp [ofInt]

/-- **The maximal order `𝒪` as a subring of `B`.** (Maximality is a fact about discriminants,
`disc 𝒪 = 6² `, recorded in h-trust A1; it is not needed for the statements of this file.) -/
def O : Subring B where
  carrier := {x | InO x}
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨mulCoord n m, ofInt_mul n m⟩
  one_mem' := ⟨![1, 0, 0, 0], ofInt_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, ofInt_add n m⟩
  zero_mem' := ⟨0, ofInt_zero.symm⟩
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, ofInt_neg n⟩

theorem mem_O {x : B} : x ∈ O ↔ InO x := Iff.rfl

theorem ofInt_mem (n : Fin 4 → ℤ) : ofInt n ∈ O := ⟨n, rfl⟩

/-! ## §2 The Rosati involution `x† = μ⁻¹ x̄ μ` -/

/-- `μ = 2j + k`, `μ² = −6`. -/
def mu : B := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = −μ/6`. -/
def muInv : B := ⟨0, 0, -1/3, -1/6⟩

theorem mu_mul_muInv : mu * muInv = 1 := by ext <;> simp [mu, muInv] <;> norm_num
theorem muInv_mul_mu : muInv * mu = 1 := by ext <;> simp [mu, muInv] <;> norm_num
theorem mu_mul_mu : mu * mu = -6 := by
  ext <;> simp [mu, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem mu_mem : mu ∈ O := ⟨![-2, -1, 4, 2], by ext <;> simp [mu, ofInt] <;> norm_num⟩

/-- Reduced trace. -/
def trd (x : B) : ℚ := 2 * x.re

/-- Reduced norm (`x x̄ = nrd x`). -/
def nrd (x : B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem trd_add (x y : B) : trd (x + y) = trd x + trd y := by simp [trd]; ring
theorem trd_smul (r : ℚ) (x : B) : trd (r • x) = r * trd x := by simp [trd]; ring
theorem trd_mul_comm (x y : B) : trd (x * y) = trd (y * x) := by simp [trd]; ring
theorem trd_star (x : B) : trd (star x) = trd x := by simp [trd]

theorem mul_star_eq_nrd (x : B) : x * star x = (⟨nrd x, 0, 0, 0⟩ : B) := by
  ext <;> simp [nrd] <;> ring

/-- The Rosati involution of N5's polarization. -/
def dag (x : B) : B := muInv * star x * mu

/-- The two conjugations agree because `μ² = −6` is central. -/
theorem dag_eq' (x : B) : dag x = mu * star x * muInv := by
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

theorem dag_dag (x : B) : dag (dag x) = x := by
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

theorem dag_mul (x y : B) : dag (x * y) = dag y * dag x := by
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

theorem dag_add (x y : B) : dag (x + y) = dag x + dag y := by
  simp only [dag, star_add, mul_add, add_mul]

theorem dag_smul (r : ℚ) (x : B) : dag (r • x) = r • dag x := by
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

theorem dag_one : dag 1 = 1 := by simp [dag, muInv_mul_mu]

/-- `†` on integer coordinates (`order_table.py`). -/
def dagCoord (n : Fin 4 → ℤ) : Fin 4 → ℤ :=
  ![n 0 + 2 * n 2 - 2 * n 3, n 1 + n 2 - n 3, -3 * n 2 + 4 * n 3, -2 * n 2 + 3 * n 3]

theorem dag_ofInt (n : Fin 4 → ℤ) : dag (ofInt n) = ofInt (dagCoord n) := by
  simp only [dag, muInv, mu, ofInt, dagCoord]; ext <;> simp <;> ring

/-- `†` preserves `𝒪`. -/
theorem dag_mem {x : B} (hx : x ∈ O) : dag x ∈ O := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨dagCoord n, dag_ofInt n⟩

/-- **Positivity of the Rosati involution**: `trd(x x†) = 2x₀² + 4x₁² + 18x₂² − 48x₂x₃ + 36x₃²`,
positive definite. -/
theorem trd_mul_dag (x : B) :
    trd (x * dag x) =
      2 * x.re ^ 2 + 4 * x.imI ^ 2 + 18 * x.imJ ^ 2 - 48 * x.imJ * x.imK + 36 * x.imK ^ 2 := by
  simp only [trd, dag, muInv, mu]; simp; ring

theorem trd_mul_dag_pos {x : B} (hx : x ≠ 0) : 0 < trd (x * dag x) := by
  rw [trd_mul_dag]
  have key : 2 * x.re ^ 2 + 4 * x.imI ^ 2 + 18 * x.imJ ^ 2 - 48 * x.imJ * x.imK + 36 * x.imK ^ 2
      = 2 * x.re ^ 2 + 4 * x.imI ^ 2 + 18 * (x.imJ - 4/3 * x.imK) ^ 2 + 4 * x.imK ^ 2 := by ring
  rw [key]
  by_contra hle
  push_neg at hle
  have a0 := sq_nonneg x.re
  have a1 := sq_nonneg x.imI
  have a2 := sq_nonneg (x.imJ - 4/3 * x.imK)
  have a3 := sq_nonneg x.imK
  have h0 : x.re = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
  have h1 : x.imI = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
  have h3 : x.imK = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
  have h2' : x.imJ - 4/3 * x.imK = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linarith)
  have h2 : x.imJ = 0 := by rw [h3] at h2'; simpa using h2'
  exact hx (by ext <;> simp [h0, h1, h2, h3])

/-! ## §3 N5's Riemann form and its Rosati compatibility -/

/-- `E₀(x, y) = trd(μ⁻¹ x ȳ)` (N5 L413-415). -/
def E0 (x y : B) : ℚ := trd (muInv * x * star y)

/-- `E₀` as a `ℚ`-bilinear form. -/
def E0bil : LinearMap.BilinForm ℚ B :=
  LinearMap.mk₂ ℚ E0
    (fun x x' y => by simp only [E0, mul_add, add_mul, trd_add])
    (fun r x y => by simp only [E0, mul_smul_comm, smul_mul_assoc, trd_smul, smul_eq_mul])
    (fun x y y' => by simp only [E0, star_add, mul_add, trd_add])
    (fun r x y => by
      simp only [E0, star_smul, mul_smul_comm, trd_smul, smul_eq_mul, star_trivial])

theorem E0bil_apply (x y : B) : E0bil x y = E0 x y := rfl

theorem E0_alt (x : B) : E0 x x = 0 := by
  simp only [E0, mul_assoc, mul_star_eq_nrd, muInv, trd]; simp

theorem E0_rosati (a x y : B) : E0 (a * x) y = E0 x (dag a * y) := by
  simp only [E0, dag, muInv, mu, trd]; simp; ring

/-- `E₀` on N5's basis is N5's Gram matrix (`PkgI1.gram_eq`). -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0]

theorem E0_gram (r s : Fin 4) : E0 (oBasis r) (oBasis s) = gram r s := by
  fin_cases r <;> fin_cases s <;> simp [E0, trd, muInv, oBasis, gram] <;> norm_num

theorem gram_det : gram.det = 1 := by
  simp [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-- `E₀` is `ℤ`-valued on `𝒪 × 𝒪`. -/
theorem E0_int (n m : Fin 4 → ℤ) : ∃ z : ℤ, E0 (ofInt n) (ofInt m) = z := by
  refine ⟨-(n 0 * m 2) + n 0 * m 3 + n 1 * m 2 - 2 * n 1 * m 3 + n 2 * m 0 - n 2 * m 1
    - n 3 * m 0 + 2 * n 3 * m 1, ?_⟩
  simp only [E0, trd, muInv, ofInt]; simp; ring

/-! ## §4 Uniqueness of the compatible polarization (lattice form)

Every alternating `ℚ`-bilinear form on `B = H₁(A, ℚ)` for which `𝒪` acts with adjoint `†` is a
rational multiple of `E₀`. Proof: `E(x, y) = E(x·1, y) = E(1, x†y) =: f(x†y)` with `f` linear;
alternation gives `f(x†x) = 0`; for `x = 1, 1+i, 1+j` this gives `f(1) = f(i) = f(j) + f(k) = 0`
(`x†x` computed in `order_table.py`), so `f(z) = (z₂ − z₃) f(j) = r·trd(μ⁻¹z̄)`. -/

/-- The coordinate decomposition `z = z₀ + z₁ i + z₂ j + z₃ k`. -/
theorem decomp (z : B) :
    z = z.re • (1 : B) + z.imI • (⟨0, 1, 0, 0⟩ : B) + z.imJ • (⟨0, 0, 1, 0⟩ : B) +
      z.imK • (⟨0, 0, 0, 1⟩ : B) := by
  ext <;> simp

theorem eq_smul_E0 (E : LinearMap.BilinForm ℚ B) (halt : ∀ x, E x x = 0)
    (hros : ∀ a x y, E (a * x) y = E x (dag a * y)) :
    ∃ r : ℚ, ∀ x y, E x y = r * E0 x y := by
  set f : B →ₗ[ℚ] ℚ := E 1 with hf
  have hE : ∀ x y, E x y = f (dag x * y) := by
    intro x y; rw [hf, ← hros x 1 y, mul_one]
  have hf0 : ∀ x, f (dag x * x) = 0 := fun x => by rw [← hE]; exact halt x
  -- the three relations
  have r1 : f 1 = 0 := by simpa [dag_one] using hf0 1
  have e2 : dag (⟨1, 1, 0, 0⟩ : B) * ⟨1, 1, 0, 0⟩ = (3 : ℚ) • (1 : B) + (2 : ℚ) • ⟨0, 1, 0, 0⟩ := by
    simp only [dag, muInv, mu]; ext <;> simp <;> norm_num
  have e3 : dag (⟨1, 0, 1, 0⟩ : B) * ⟨1, 0, 1, 0⟩ = (10 : ℚ) • (1 : B) + (6 : ℚ) • ⟨0, 1, 0, 0⟩
      + (-2 : ℚ) • (⟨0, 0, 1, 0⟩ + ⟨0, 0, 0, 1⟩) := by
    simp only [dag, muInv, mu]; ext <;> simp <;> norm_num
  have r2 : f ⟨0, 1, 0, 0⟩ = 0 := by
    have := hf0 ⟨1, 1, 0, 0⟩
    rw [e2, map_add, map_smul, map_smul, r1] at this
    simp at this; linarith
  have r3 : f ⟨0, 0, 0, 1⟩ = - f ⟨0, 0, 1, 0⟩ := by
    have := hf0 ⟨1, 0, 1, 0⟩
    rw [e3, map_add, map_add, map_smul, map_smul, map_smul, map_add, r1, r2] at this
    simp at this; linarith
  refine ⟨-(f ⟨0, 0, 1, 0⟩) / 2, fun x y => ?_⟩
  rw [hE, decomp (dag x * y)]
  simp only [map_add, map_smul, r1, r2, r3, smul_eq_mul]
  simp only [E0, trd, dag, muInv, mu]
  simp
  ring

/-- The scalar is unique (`E₀ ≠ 0`). -/
theorem E0_ne_zero : E0 (oBasis 0) (oBasis 2) ≠ 0 := by
  rw [E0_gram]; simp [gram]

/-- **Principal ⇒ `r = ±1`.** If a Rosati-compatible alternating form has Gram determinant 1 on
N5's basis of `𝒪` (a principal polarization on the lattice `𝒪`), it is `±E₀`. -/
theorem eq_pm_E0_of_principal (E : LinearMap.BilinForm ℚ B) (halt : ∀ x, E x x = 0)
    (hros : ∀ a x y, E (a * x) y = E x (dag a * y))
    (hdet : (Matrix.of fun r s => E (oBasis r) (oBasis s)).det = 1) :
    (∀ x y, E x y = E0 x y) ∨ (∀ x y, E x y = - E0 x y) := by
  obtain ⟨r, hr⟩ := eq_smul_E0 E halt hros
  have hM : (Matrix.of fun r' s => E (oBasis r') (oBasis s)) = r • gram := by
    ext a b; simp [hr, E0_gram]
  rw [hM, Matrix.det_smul, gram_det, Fintype.card_fin, mul_one] at hdet
  have h4 : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination hdet
  have hr2 : r ^ 2 = 1 := by
    rcases mul_eq_zero.1 h4 with h | h
    · linarith
    · nlinarith [sq_nonneg r]
  have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
  rcases mul_eq_zero.1 this with h | h
  · left; intro x y; rw [hr, show r = 1 by linarith, one_mul]
  · right; intro x y; rw [hr, show r = -1 by linarith]; ring

/-! ## §5 Atkin–Lehner elements -/

/-- `x` is invertible in `B` and conjugation by `x` maps `𝒪` into itself in both directions. -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z ∈ O, x * z * y ∈ O ∧ y * z * x ∈ O

/-- `w₂ = 1 + i + j`, reduced norm 2. -/
def w2 : B := ⟨1, 1, 1, 0⟩
/-- `w₃ = j`, reduced norm 3. -/
def w3 : B := ⟨0, 0, 1, 0⟩

theorem nrd_w2 : nrd w2 = 2 := by norm_num [nrd, w2]
theorem nrd_w3 : nrd w3 = 3 := by norm_num [nrd, w3]
theorem nrd_mu : nrd mu = 6 := by norm_num [nrd, mu]

theorem w2_normalizes : NormalizesO w2 := by
  refine ⟨⟨1/2, -1/2, -1/2, 0⟩, ?_, ?_, ?_⟩
  · ext <;> simp [w2] <;> norm_num
  · ext <;> simp [w2] <;> norm_num
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨![n 0 + 2 * n 1 - n 2, -n 1 + n 2 + n 3, -4 * n 1 + 3 * n 2, -2 * n 1 + n 2 - n 3],
      ?_⟩, ⟨![n 0 + 2 * n 1 - n 2 + 2 * n 3, -3 * n 1 + 2 * n 2 - 3 * n 3,
        -4 * n 1 + 3 * n 2 - 4 * n 3, 2 * n 1 - n 2 + n 3], ?_⟩⟩ <;>
    · simp only [w2, ofInt]; ext <;> simp <;> ring

theorem w3_normalizes : NormalizesO w3 := by
  refine ⟨⟨0, 0, -1/3, 0⟩, ?_, ?_, ?_⟩
  · ext <;> simp [w3] <;> norm_num
  · ext <;> simp [w3] <;> norm_num
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨![n 0, -n 1, n 2, -n 3], ?_⟩, ⟨![n 0, -n 1, n 2, -n 3], ?_⟩⟩ <;>
    · simp only [w3, ofInt]; ext <;> simp <;> ring

theorem mu_normalizes : NormalizesO mu := by
  refine ⟨muInv, mu_mul_muInv, muInv_mul_mu, ?_⟩
  rintro _ ⟨n, rfl⟩
  refine ⟨⟨![n 0 - n 2 + 2 * n 3, -n 1 - n 2 + n 3, 3 * n 2 - 4 * n 3, 2 * n 2 - 3 * n 3], ?_⟩,
    ⟨![n 0 - n 2 + 2 * n 3, -n 1 - n 2 + n 3, 3 * n 2 - 4 * n 3, 2 * n 2 - 3 * n 3], ?_⟩⟩ <;>
  · simp only [mu, muInv, ofInt]; ext <;> simp <;> ring

/-- The relations of `W ≅ (ℤ/2)²` modulo `ℚ^×𝒪¹` that are used: `w₃² = −3`, `μ² = −6`,
`w₂² = 2(i+j)` with `i + j ∈ 𝒪` of reduced norm 1, and `w₂w₃ = u·μ` with `u ∈ 𝒪`, `nrd u = 1`. -/
theorem atkinLehner_relations :
    w3 * w3 = -3 ∧ mu * mu = -6 ∧
    w2 * w2 = (2 : ℚ) • (⟨0, 1, 1, 0⟩ : B) ∧ (⟨0, 1, 1, 0⟩ : B) ∈ O ∧ nrd ⟨0, 1, 1, 0⟩ = 1 ∧
    ∃ u ∈ O, nrd u = 1 ∧ w2 * w3 = u * mu := by
  refine ⟨?_, mu_mul_mu, ?_, ⟨![-1, 1, 2, 0], ?_⟩, by norm_num [nrd], ⟨0, 1/2, 1, 1/2⟩,
    ⟨![-1, 0, 2, 1], ?_⟩, by norm_num [nrd], ?_⟩
  · ext <;> simp [w3, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
  · ext <;> simp [w2] <;> norm_num
  · ext <;> simp [ofInt] <;> norm_num
  · ext <;> simp [ofInt] <;> norm_num
  · ext <;> simp [w2, w3, mu] <;> norm_num

/-! ## §6 `ℚ(√−2)` does not embed in `B` (h-b1 M9: no elliptic element of type `(0,2)`)

`x² = −2` has no solution in `B`: for `x = a + bi + cj + dk`, `a = 0` and
`3c² = 2b² + 6d² + 2`, which has no rational solution (3-adic descent: clearing denominators,
`3C² = 2B² + 6D² + 2N²` forces `3 | B, N`, then `3 | C, D`, and `(B, C, D, N)/3` is again a
solution). Equivalently, 3 splits in `ℚ(√−2)` while `B` ramifies at 3. -/

theorem zmod3_a (b n : ZMod 3) : b ^ 2 + n ^ 2 = 0 → b = 0 ∧ n = 0 := by
  revert b n; decide

theorem zmod3_b (c d : ZMod 3) : c ^ 2 = 2 * d ^ 2 → c = 0 ∧ d = 0 := by
  revert c d; decide

theorem dvd3_of_zmod {z : ℤ} (h : (z : ZMod 3) = 0) : (3 : ℤ) ∣ z :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).1 h

theorem descent (n : ℕ) : ∀ B C D N : ℤ, N.natAbs = n → N ≠ 0 →
    3 * C ^ 2 ≠ 2 * B ^ 2 + 6 * D ^ 2 + 2 * N ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B C D N hn hN h
  have h3 : ((B : ZMod 3)) ^ 2 + (N : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at this
    have h2 : (2 : ZMod 3) * ((B : ZMod 3) ^ 2 + (N : ZMod 3) ^ 2) = 0 := by
      rw [show (3 : ZMod 3) = 0 from rfl, show (6 : ZMod 3) = 0 from rfl] at this
      linear_combination -this
    have hu : (2 : ZMod 3) * 2 = 1 := rfl
    linear_combination 2 * h2 - ((B : ZMod 3) ^ 2 + (N : ZMod 3) ^ 2) * hu
  obtain ⟨hB, hN3⟩ := zmod3_a _ _ h3
  obtain ⟨B', rfl⟩ := dvd3_of_zmod hB
  obtain ⟨N', rfl⟩ := dvd3_of_zmod hN3
  have h' : C ^ 2 = 6 * B' ^ 2 + 2 * D ^ 2 + 6 * N' ^ 2 := by linarith
  have h4 : ((C : ZMod 3)) ^ 2 = 2 * (D : ZMod 3) ^ 2 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h'
    push_cast at this
    rw [show (6 : ZMod 3) = 0 from rfl] at this
    linear_combination this
  obtain ⟨hC, hD⟩ := zmod3_b _ _ h4
  obtain ⟨C', rfl⟩ := dvd3_of_zmod hC
  obtain ⟨D', rfl⟩ := dvd3_of_zmod hD
  have hN' : N' ≠ 0 := by rintro rfl; simp at hN
  have hlt : N'.natAbs < n := by
    rw [← hn, Int.natAbs_mul]
    have : 0 < N'.natAbs := Int.natAbs_pos.2 hN'
    simp; omega
  exact ih _ hlt B' C' D' N' rfl hN' (by linarith)

/-- **No `x ∈ B` with `x² = −2`.** -/
theorem no_sq_eq_neg_two (x : B) : x * x ≠ -2 := by
  intro hx
  have hre := congrArg QuaternionAlgebra.re hx
  have hI := congrArg QuaternionAlgebra.imI hx
  have hJ := congrArg QuaternionAlgebra.imJ hx
  have hK := congrArg QuaternionAlgebra.imK hx
  simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] at hre hI hJ hK
  by_cases ha : x.re = 0
  · rw [ha] at hre
    set d1 := x.imI.den
    set d2 := x.imJ.den
    set d3 := x.imK.den
    have hm0 : ((d1 * d2 * d3 : ℕ) : ℚ) ≠ 0 := by positivity
    have eB : x.imI * ((d1 * d2 * d3 : ℕ) : ℚ) = ((x.imI.num * (d2 * d3) : ℤ) : ℚ) := by
      push_cast
      rw [show x.imI * (d1 * d2 * d3 : ℚ) = (x.imI * d1) * (d2 * d3) by ring, Rat.mul_den_eq_num]
    have eC : x.imJ * ((d1 * d2 * d3 : ℕ) : ℚ) = ((x.imJ.num * (d1 * d3) : ℤ) : ℚ) := by
      push_cast
      rw [show x.imJ * (d1 * d2 * d3 : ℚ) = (x.imJ * d2) * (d1 * d3) by ring, Rat.mul_den_eq_num]
    have eD : x.imK * ((d1 * d2 * d3 : ℕ) : ℚ) = ((x.imK.num * (d1 * d2) : ℤ) : ℚ) := by
      push_cast
      rw [show x.imK * (d1 * d2 * d3 : ℚ) = (x.imK * d3) * (d1 * d2) by ring, Rat.mul_den_eq_num]
    have key : ((3 * (x.imJ.num * (d1 * d3)) ^ 2 : ℤ) : ℚ) =
        ((2 * (x.imI.num * (d2 * d3)) ^ 2 + 6 * (x.imK.num * (d1 * d2)) ^ 2 +
          2 * ((d1 * d2 * d3 : ℕ) : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast at eB eC eD ⊢
      rw [← eB, ← eC, ← eD]
      linear_combination (-((d1 : ℚ) * d2 * d3) ^ 2) * hre
    exact descent _ _ _ _ ((d1 * d2 * d3 : ℕ) : ℤ) rfl (by exact_mod_cast hm0)
      (by exact_mod_cast key)
  · have hb : x.imI = 0 := by
      rcases mul_eq_zero.1 (show x.re * x.imI = 0 by linarith) with h | h
      · exact absurd h ha
      · exact h
    have hc : x.imJ = 0 := by
      rcases mul_eq_zero.1 (show x.re * x.imJ = 0 by linarith) with h | h
      · exact absurd h ha
      · exact h
    have hd : x.imK = 0 := by
      rcases mul_eq_zero.1 (show x.re * x.imK = 0 by linarith) with h | h
      · exact absurd h ha
      · exact h
    rw [hb, hc, hd] at hre
    nlinarith [sq_nonneg x.re]

end BPQM

#print axioms BPQM.eq_smul_E0
#print axioms BPQM.eq_pm_E0_of_principal
#print axioms BPQM.trd_mul_dag_pos
#print axioms BPQM.atkinLehner_relations
#print axioms BPQM.w2_normalizes
#print axioms BPQM.no_sq_eq_neg_two

/-! rv-blueprints axiom audit (appended): every declaration added in this file. -/
open Lean Elab Command in
elab "#rv_audit_axioms" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (c, _) in env.constants.map₂.toList do
    if c.isInternal then continue
    n := n + 1
    let axs ← liftCoreM <| Lean.collectAxioms c
    let extra := axs.filter (fun a => !std.contains a)
    if extra.size > 0 then bad := bad.push (c, extra)
  logInfo m!"rv_audit: {n} declarations; non-standard axioms in {bad.size}: {bad.toList.take 20}"
#rv_audit_axioms
