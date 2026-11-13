import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ZInQKernel.HDecomp.QM.Structures

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/rv-qm-polar/QMPolar.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# rv-qm-polar: Rosati types of principal polarizations on QM lattices (discriminant 6)

Mathlib only. §§1-4 are copied verbatim from `scratch/bp-qmmoduli/QMOrder.lean` §§1-4 (the order
`𝒪`, `μ = 2j + k`, `x† = μ⁻¹x̄μ`, N5's form `E₀`, and the uniqueness theorem
`eq_pm_E0_of_principal`), renamed into the namespace `RvQMPolar`. New here (§§5-8):

* §5 **Non-uniqueness without a fixed Rosati type.** `ν = 2j − k ∈ 𝒪` has `ν² = −6`; its form
  `E_ν(x, y) = trd(ν⁻¹xȳ)` is alternating, integral and unimodular on `𝒪` and compatible with
  `x ↦ ν⁻¹x̄ν`, but is not a rational multiple of `E₀` and not compatible with `†`. So (argued, not
  compiled at the level of tori) on every QM torus `ℂ²/𝒪v` both `±E₀` and `±E_ν` give principal polarizations whose Rosati involution
  preserves `ι(𝒪)` (one sign each is positive): "the" principal polarization of `(A, ι)` is unique
  only after the type `μ` is fixed (`eq_pm_E0_of_principal`). `ν = −v μ v⁻¹` with `v = −1 + i` a
  unit of norm −1, so the two polarizations differ by the automorphism `ι(v)`.
* §6 **Every type is a unit transport of `μ`.** For every `c ∈ 𝒪` with `c² = −6` there is
  `v ∈ 𝒪` with `c = μv`, `nrd v = 1`, `v† = v`, and `E_c(x, y) = E₀(x, vy)`: the principal
  polarization of type `c` is `λ_μ ∘ ι(v)`.
* §7 **The Atkin–Lehner twists preserve the type `μ`.** `i` and `j + k` lie in `𝒪`, normalize it,
  square to `2` and `3`, anticommute with `μ`, and `i(j+k) = μ`; conjugation by each of
  `i, j + k, μ` commutes with `†`. So `(A, ι, λ) ↦ (A, ι ∘ Ad χ, λ)` is the `W`-action on PEL
  objects of type `μ` (Rotger's twisting involutions; N5 L533-534).
* §8 **The sign step (existence over `ℂ`).** For every `j ∈ B_ℝ` with `j² = −1` (a complex
  structure commuting with `𝒪`), `x ↦ E₀(xj, x)` is definite (`riemann_sign`) and `E₀` is
  `j`-invariant (`E0R_mul_j`); `lemmaP_lattice`: exactly one of `±E₀` is a principal Riemann form.
  These are the lattice steps of Lemma P (characteristic 0) for N5's `μ` on `Λ = 𝒪`. Not compiled:
  the identification of `E0R` with `E₀ ⊗ ℝ`, the combination with `eq_smul_E0`, the transport to
  `Λ = 𝒪v`, Riemann forms ↔ polarizations, other `μ`, class number one and the descent from `ℂ`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace RvQMPolar

/-! `B`, `ofInt`, `InO`, `mulCoord`, `ofInt_mul`, … and `O` (copied in the draft) are
`LeafQM`'s, from `ZInQKernel.HDecomp.QM.Structures` (identical code). -/
open LeafQM (B ofInt InO mulCoord ofInt_mul ofInt_add ofInt_neg ofInt_zero ofInt_one O)

/-! ## §1 The maximal order `𝒪` -/

/-- N5's basis `(1, i, (1+j)/2, (i+k)/2)` (same as `PkgI1.oBasis`). -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

theorem ofInt_eq_sum (n : Fin 4 → ℤ) : ofInt n = ∑ k, (n k : ℚ) • oBasis k := by
  ext <;> simp [ofInt, oBasis, Fin.sum_univ_four] <;> ring

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

/-! ## §5 A second Rosati type: non-uniqueness when the type is not fixed -/

/-- `ν = 2j − k`, another element of `𝒪` with `ν² = −6`. -/
def nu : B := ⟨0, 0, 2, -1⟩

/-- `ν⁻¹ = −ν/6`. -/
def nuInv : B := ⟨0, 0, -1/3, 1/6⟩

theorem nu_mul_nuInv : nu * nuInv = 1 := by ext <;> simp [nu, nuInv] <;> norm_num
theorem nu_mul_nu : nu * nu = -6 := by
  ext <;> simp [nu, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num
theorem nu_mem : nu ∈ O := ⟨![-2, 1, 4, -2], by ext <;> simp [nu, ofInt] <;> norm_num⟩

/-- The involution of type `ν`: `x ↦ ν⁻¹x̄ν`. -/
def dagNu (x : B) : B := nuInv * star x * nu

/-- `E_ν(x, y) = trd(ν⁻¹xȳ)`. -/
def Enu (x y : B) : ℚ := trd (nuInv * x * star y)

def Enubil : LinearMap.BilinForm ℚ B :=
  LinearMap.mk₂ ℚ Enu
    (fun x x' y => by simp only [Enu, mul_add, add_mul, trd_add])
    (fun r x y => by simp only [Enu, mul_smul_comm, smul_mul_assoc, trd_smul, smul_eq_mul])
    (fun x y y' => by simp only [Enu, star_add, mul_add, trd_add])
    (fun r x y => by
      simp only [Enu, star_smul, mul_smul_comm, trd_smul, smul_eq_mul, star_trivial])

theorem Enu_alt (x : B) : Enu x x = 0 := by
  simp only [Enu, mul_assoc, mul_star_eq_nrd, nuInv, trd]; simp

theorem Enu_rosati (a x y : B) : Enu (a * x) y = Enu x (dagNu a * y) := by
  simp only [Enu, dagNu, nuInv, nu, trd]; simp; ring

def gramNu : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, -1; 0, 0, -1, -2; 1, 1, 0, 0; 1, 2, 0, 0]

theorem Enu_gram (r s : Fin 4) : Enu (oBasis r) (oBasis s) = gramNu r s := by
  fin_cases r <;> fin_cases s <;> simp [Enu, trd, nuInv, oBasis, gramNu] <;> norm_num

theorem gramNu_det : gramNu.det = 1 := by
  simp [gramNu, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-- `E_ν` is `ℤ`-valued on `𝒪 × 𝒪` (its Gram matrix on the `ℤ`-basis is integral). -/
theorem Enu_int (n m : Fin 4 → ℤ) : ∃ z : ℤ, Enu (ofInt n) (ofInt m) = z := by
  refine ⟨∑ r, ∑ s, n r * m s * (![![0, 0, -1, -1], ![0, 0, -1, -2], ![1, 1, 0, 0],
    ![1, 2, 0, 0]] r s), ?_⟩
  simp only [Enu, trd, nuInv, ofInt, Fin.sum_univ_four]; simp; ring

/-- The two types give different involutions on `𝒪`. -/
theorem dagNu_ne_dag : dagNu (oBasis 2) ≠ dag (oBasis 2) := by
  intro h
  have := congrArg QuaternionAlgebra.imK h
  simp [dagNu, dag, nuInv, nu, muInv, mu, oBasis] at this
  norm_num at this

/-- `E_ν` is not a rational multiple of `E₀`. -/
theorem Enu_ne_smul_E0 : ¬ ∃ r : ℚ, ∀ x y, Enu x y = r * E0 x y := by
  rintro ⟨r, hr⟩
  have h1 := hr (oBasis 0) (oBasis 2)
  have h2 := hr (oBasis 0) (oBasis 3)
  rw [Enu_gram, E0_gram] at h1 h2
  simp [gramNu, gram] at h1 h2
  linarith

/-- **`E_ν` is not compatible with the type `μ`.** -/
theorem Enu_not_rosati_mu : ¬ ∀ a x y, Enu (a * x) y = Enu x (dag a * y) := by
  intro h
  obtain ⟨r, hr⟩ := eq_smul_E0 Enubil Enu_alt (fun a x y => h a x y)
  exact Enu_ne_smul_E0 ⟨r, fun x y => hr x y⟩

/-- **Lattice-level non-uniqueness.** Two principal (Gram determinant 1), alternating forms on
`𝒪`, each compatible with an involution `x ↦ c⁻¹x̄c` (`c = μ, ν`, `c² = −6`, both preserving `𝒪`),
neither a multiple of the other. -/
theorem two_principal_types :
    (gram.det = 1 ∧ (∀ x, E0 x x = 0) ∧ ∀ a x y, E0 (a * x) y = E0 x (dag a * y)) ∧
    (gramNu.det = 1 ∧ (∀ x, Enu x x = 0) ∧ ∀ a x y, Enu (a * x) y = Enu x (dagNu a * y)) ∧
    nu * nu = -6 ∧ nu ∈ O ∧ (¬ ∃ r : ℚ, ∀ x y, Enu x y = r * E0 x y) :=
  ⟨⟨gram_det, E0_alt, E0_rosati⟩, ⟨gramNu_det, Enu_alt, Enu_rosati⟩, nu_mul_nu, nu_mem,
    Enu_ne_smul_E0⟩

/-- `v = −1 + i`, a unit of `𝒪` of reduced norm −1. -/
def vUnit : B := ⟨-1, 1, 0, 0⟩

theorem vUnit_mem : vUnit ∈ O := ⟨![-1, 1, 0, 0], by ext <;> simp [vUnit, ofInt]⟩
theorem nrd_vUnit : nrd vUnit = -1 := by norm_num [nrd, vUnit]

/-- `ν = −vμv⁻¹`, i.e. `νv = −vμ`: type `ν` is the transport of type `−μ` (the same involution as
`μ`) by the unit `v`. -/
theorem nu_conj : nu * vUnit = -(vUnit * mu) := by
  ext <;> simp [nu, vUnit, mu] <;> norm_num

/-! ## §6 Every Rosati type `c ∈ 𝒪`, `c² = −6`, is `μ` times a symmetric unit of norm one -/

/-- `E_c(x, y) = trd(c⁻¹xȳ)` for `c² = −6`, written with `c⁻¹ = −c/6`. -/
def Ec (c x y : B) : ℚ := trd (((-1/6 : ℚ) • c) * x * star y)

theorem Ec_mu (x y : B) : Ec mu x y = E0 x y := by
  simp only [Ec, E0, muInv, mu, trd]; simp; ring

private theorem zmod2_aux : ∀ x y z : ZMod 2,
    3 * x ^ 2 - 2 * (y ^ 2 + y * z + z ^ 2) = 6 → x = 0 := by decide

private theorem zmod3_aux : ∀ x y z : ZMod 3,
    3 * x ^ 2 - 2 * (y ^ 2 + y * z + z ^ 2) = 6 → y - z = 0 := by decide

/-- **Classification of the types.** If `c ∈ 𝒪` and `c² = −6`, then `c = μv` with `v ∈ 𝒪`,
`nrd v = 1`, `v† = v`, and `E_c(x, y) = E₀(x, vy)` for all `x, y`. (So a principal polarization
of type `c` on `(A, ι)` is `λ_μ ∘ ι(v)`, `v` a `†`-symmetric unit.) -/
theorem type_eq_mu_mul (c : B) (hc : c ∈ O) (hcc : c * c = -6) :
    ∃ v ∈ O, c = mu * v ∧ nrd v = 1 ∧ dag v = v ∧ ∀ x y, Ec c x y = E0 x (v * y) := by
  obtain ⟨n, rfl⟩ := hc
  have hre := congrArg QuaternionAlgebra.re hcc
  have hI := congrArg QuaternionAlgebra.imI hcc
  have hJ := congrArg QuaternionAlgebra.imJ hcc
  have hK := congrArg QuaternionAlgebra.imK hcc
  simp only [ofInt, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_neg,
    QuaternionAlgebra.imI_neg, QuaternionAlgebra.imJ_neg, QuaternionAlgebra.imK_neg,
    QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
    QuaternionAlgebra.imK_ofNat] at hre hI hJ hK
  have eK : (n 3 * (2 * n 0 + n 2) : ℤ) = 0 := by
    have : ((n 3 * (2 * n 0 + n 2) : ℤ) : ℚ) = 0 := by push_cast; linear_combination 2 * hK
    exact_mod_cast this
  have eJ : (n 2 * (2 * n 0 + n 2) : ℤ) = 0 := by
    have : ((n 2 * (2 * n 0 + n 2) : ℤ) : ℚ) = 0 := by push_cast; linear_combination 2 * hJ
    exact_mod_cast this
  have eI : ((2 * n 1 + n 3) * (2 * n 0 + n 2) : ℤ) = 0 := by
    have : (((2 * n 1 + n 3) * (2 * n 0 + n 2) : ℤ) : ℚ) = 0 := by
      push_cast; linear_combination 2 * hI
    exact_mod_cast this
  have eR : (2 * n 0 ^ 2 + 2 * n 0 * n 2 - n 2 ^ 2 + 4 * n 1 ^ 2 + 4 * n 1 * n 3
      + 4 * n 3 ^ 2 : ℤ) = -12 := by
    have : ((2 * n 0 ^ 2 + 2 * n 0 * n 2 - n 2 ^ 2 + 4 * n 1 ^ 2 + 4 * n 1 * n 3
        + 4 * n 3 ^ 2 : ℤ) : ℚ) = -12 := by
      push_cast; linear_combination 2 * hre
    exact_mod_cast this
  -- `c` is pure: `n₂ = −2n₀`
  have h2 : n 2 = -2 * n 0 := by
    by_contra hne
    have hs : 2 * n 0 + n 2 ≠ 0 := fun h => hne (by linarith)
    have a2 : n 2 = 0 := (mul_eq_zero.1 eJ).resolve_right hs
    have a3 : n 3 = 0 := (mul_eq_zero.1 eK).resolve_right hs
    have a1' : 2 * n 1 + n 3 = 0 := (mul_eq_zero.1 eI).resolve_right hs
    have a1 : n 1 = 0 := by omega
    rw [a1, a2, a3] at eR
    nlinarith [sq_nonneg (n 0)]
  have eq6 : 3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) = 6 := by
    have h' : 2 * (3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)) = 2 * 6 := by
      rw [h2] at eR; linear_combination -eR
    exact mul_left_cancel₀ two_ne_zero h'
  -- `2 ∣ n₀` and `3 ∣ n₁ − n₃`
  have d2 : (2 : ℤ) ∣ n 0 := by
    have := congrArg (Int.cast : ℤ → ZMod 2) eq6
    push_cast at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n 0) 2).1 (zmod2_aux _ _ _ this)
  have d3 : (3 : ℤ) ∣ n 1 - n 3 := by
    have := congrArg (Int.cast : ℤ → ZMod 3) eq6
    push_cast at this
    have h := zmod3_aux _ _ _ this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (n 1 - n 3) 3).1 (by push_cast; exact h)
  obtain ⟨a, ha⟩ := d2
  obtain ⟨b, hb⟩ := d3
  have hn1 : n 1 = n 3 + 3 * b := by linarith
  have hn2 : n 2 = -4 * a := by rw [h2, ha]; ring
  set w : Fin 4 → ℤ := ![-(2 * a + b + n 3), -(a + b + n 3), 2 * b + n 3, 2 * b + n 3] with hw
  have hc' : ofInt n = mu * ofInt w := by
    simp only [ofInt, mu, hw]; ext <;> simp [ha, hn1, hn2] <;> ring
  refine ⟨ofInt w, ofInt_mem w, hc', ?_, ?_, ?_⟩
  · simp only [nrd, ofInt, hw]
    simp
    rw [ha, hn1] at eq6
    have : ((3 * (2 * a) ^ 2 - 2 * ((n 3 + 3 * b) ^ 2 + (n 3 + 3 * b) * n 3 + n 3 ^ 2) : ℤ) : ℚ)
        = 6 := by exact_mod_cast eq6
    push_cast at this
    linear_combination this / 6
  · simp only [dag, muInv, mu, ofInt, hw]; ext <;> simp <;> ring
  · intro x y
    rw [hc']
    simp only [Ec, E0, muInv, mu, ofInt, hw, trd]; simp; ring

/-- **The PEL form of every `Aut(𝒪)`-twist.** For a ring automorphism `α` of `𝒪`, `α(μ)² = −6`,
so `α(μ) = μv` with `v ∈ 𝒪`, `nrd v = 1`, `v† = v`. Hence the type-`μ` polarization of the twisted
object `(A, ι ∘ α)` is `λ ∘ ι(±v)` (the type-`α(μ)` polarization of `(A, ι)`), defined in families:
the twist is an automorphism of the PEL moduli functor of type `μ`, as R1hecke needs. -/
theorem twist_type (α : O ≃+* O) :
    ∃ v ∈ O, ((α ⟨mu, mu_mem⟩ : O) : B) = mu * v ∧ nrd v = 1 ∧ dag v = v := by
  have hm6 : ((-6 : O) : B) = -6 := by
    first
    | (push_cast; rfl)
    | norm_num
    | (rw [show (-6 : O) = -((6 : ℕ) : O) by norm_num, Subring.coe_neg, Subring.coe_natCast];
       norm_num)
  have hsq : ((α ⟨mu, mu_mem⟩ : O) : B) * ((α ⟨mu, mu_mem⟩ : O) : B) = -6 := by
    have h1 : (⟨mu, mu_mem⟩ : O) * ⟨mu, mu_mem⟩ = -6 := by
      apply Subtype.ext; rw [Subring.coe_mul, hm6]; exact mu_mul_mu
    have h2 : α ((⟨mu, mu_mem⟩ : O) * ⟨mu, mu_mem⟩) = -6 := by rw [h1, map_neg, map_ofNat]
    rw [map_mul] at h2
    have := congrArg (fun z : O => (z : B)) h2
    simp only [Subring.coe_mul] at this
    rw [this, hm6]
  obtain ⟨v, hv, h1, h2, h3, -⟩ := type_eq_mu_mul _ (α ⟨mu, mu_mem⟩).2 hsq
  exact ⟨v, hv, h1, h2, h3⟩

/-! ## §7 The Atkin–Lehner twists preserve the type `μ` -/

/-- `χ₂ = i` (`i² = 2`). -/
def chi2 : B := ⟨0, 1, 0, 0⟩
def chi2Inv : B := ⟨0, 1/2, 0, 0⟩
/-- `χ₃ = j + k` (`(j+k)² = 3`). -/
def chi3 : B := ⟨0, 0, 1, 1⟩
def chi3Inv : B := ⟨0, 0, 1/3, 1/3⟩

theorem chi2_mem : chi2 ∈ O := ⟨![0, 1, 0, 0], by ext <;> simp [chi2, ofInt]⟩
theorem chi3_mem : chi3 ∈ O := ⟨![-1, -1, 2, 2], by ext <;> simp [chi3, ofInt] <;> norm_num⟩

theorem chi2_sq : chi2 * chi2 = 2 := by
  ext <;> simp [chi2, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat]
theorem chi3_sq : chi3 * chi3 = 3 := by
  ext <;> simp [chi3, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem chi2_mu : chi2 * mu = -(mu * chi2) := by ext <;> simp [chi2, mu] <;> norm_num
theorem chi3_mu : chi3 * mu = -(mu * chi3) := by ext <;> simp [chi3, mu] <;> norm_num
theorem chi2_chi3 : chi2 * chi3 = mu := by ext <;> simp [chi2, chi3, mu] <;> norm_num

/-- `x` is invertible in `B` and conjugation by `x` maps `𝒪` into itself in both directions
(as in `scratch/bp-qmmoduli/QMOrder.lean`). -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z ∈ O, x * z * y ∈ O ∧ y * z * x ∈ O

theorem chi2_normalizes : NormalizesO chi2 := by
  refine ⟨chi2Inv, ?_, ?_, ?_⟩
  · ext <;> simp [chi2, chi2Inv]
  · ext <;> simp [chi2, chi2Inv]
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨![n 0 + n 2, n 1 + n 3, -n 2, -n 3], ?_⟩, ⟨![n 0 + n 2, n 1 + n 3, -n 2, -n 3], ?_⟩⟩
        <;>
    · simp only [chi2, chi2Inv, ofInt]; ext <;> simp <;> ring

theorem chi3_normalizes : NormalizesO chi3 := by
  refine ⟨chi3Inv, ?_, ?_, ?_⟩
  · ext <;> simp [chi3, chi3Inv] <;> norm_num
  · ext <;> simp [chi3, chi3Inv] <;> norm_num
  · rintro _ ⟨n, rfl⟩
    refine ⟨⟨![n 0 + 2 * n 2 - 2 * n 3, -n 1 + n 2 - 2 * n 3, -3 * n 2 + 4 * n 3,
      -2 * n 2 + 3 * n 3], ?_⟩, ⟨![n 0 + 2 * n 2 - 2 * n 3, -n 1 + n 2 - 2 * n 3,
      -3 * n 2 + 4 * n 3, -2 * n 2 + 3 * n 3], ?_⟩⟩ <;>
    · simp only [chi3, chi3Inv, ofInt]; ext <;> simp <;> ring

/-- **Twisting by `χ₂`, `χ₃`, `μ` commutes with `†`**: `(χxχ⁻¹)† = χx†χ⁻¹`. Hence for a PEL object
`(A, ι, λ)` of type `μ`, `(A, ι ∘ Ad χ, λ)` is again of type `μ`, with the same `λ`. -/
theorem dag_conj_chi2 (x : B) : dag (chi2 * x * chi2Inv) = chi2 * dag x * chi2Inv := by
  simp only [dag, muInv, mu, chi2, chi2Inv]; ext <;> simp <;> ring
theorem dag_conj_chi3 (x : B) : dag (chi3 * x * chi3Inv) = chi3 * dag x * chi3Inv := by
  simp only [dag, muInv, mu, chi3, chi3Inv]; ext <;> simp <;> ring
theorem dag_conj_mu (x : B) : dag (mu * x * muInv) = mu * dag x * muInv := by
  simp only [dag, muInv, mu]; ext <;> simp <;> ring

/-- The bp-qmmoduli Atkin–Lehner elements differ from `χ₂, χ₃` by units of `𝒪`:
`w₂ = 1 + i + j = χ₂ · u₂` and `w₃ = j = χ₃ · u₃`, `u₂ = 1 + (i + k)/2`, `u₃ = −1 − i`. -/
theorem w_eq_chi_mul :
    (⟨1, 1, 1, 0⟩ : B) = chi2 * ⟨1, 1/2, 0, 1/2⟩ ∧ (⟨1, 1/2, 0, 1/2⟩ : B) ∈ O ∧
      nrd ⟨1, 1/2, 0, 1/2⟩ = -1 ∧
    (⟨0, 0, 1, 0⟩ : B) = chi3 * ⟨-1, -1, 0, 0⟩ ∧ (⟨-1, -1, 0, 0⟩ : B) ∈ O ∧
      nrd ⟨-1, -1, 0, 0⟩ = -1 := by
  refine ⟨?_, ⟨![1, 0, 0, 1], ?_⟩, ?_, ?_, ⟨![-1, -1, 0, 0], ?_⟩, ?_⟩
  · ext <;> simp [chi2] <;> norm_num
  · ext <;> simp [ofInt] <;> norm_num
  · norm_num [nrd]
  · ext <;> simp [chi3] <;> norm_num
  · ext <;> simp [ofInt]
  · norm_num [nrd]

/-! ## §8 The sign step: existence of the type-`μ` Riemann form on the lattice `𝒪`

`B_ℝ = (2,−3) ⊗ ℝ`. A complex structure on `H₁(A, ℝ) = B_ℝ` commuting with the left `𝒪`-action is
right multiplication by some `j ∈ B_ℝ` with `j² = −1`. The Gram matrix of `x ↦ E₀(xj, x)` (in the
coordinates `re, imI, imJ, imK`, `j = ai + bj + ck`) has leading minors `2(b−c)`, `4(b²−2c²)`,
`8(b+c)q`, `16q²`, `q = 3b²−2a²−6c² = nrd j = 1`; the proof is the explicit `LDLᵀ` decomposition
(`Qpoly_ldl`). -/

abbrev BR := QuaternionAlgebra ℝ 2 0 (-3)

/-- `μ⁻¹ = −μ/6` in `B_ℝ`. -/
def muInvR : BR := ⟨0, 0, -1/3, -1/6⟩

/-- `E₀(x, y) = trd(μ⁻¹xȳ)` on `B_ℝ`. -/
def E0R (x y : BR) : ℝ := 2 * (muInvR * x * star y).re

/-- The quadratic form `x ↦ E₀(xj, x)` for `j = ai + bj + ck`, in coordinates. -/
def Qpoly (a b c x0 x1 x2 x3 : ℝ) : ℝ :=
  4*a*x0*x2 - 8*a*x0*x3 - 8*a*x1*x2 + 8*a*x1*x3 + 2*b*x0^2 - 4*b*x0*x1 + 4*b*x1^2
    + 6*b*x2^2 - 12*b*x2*x3 + 12*b*x3^2 - 2*c*x0^2 + 8*c*x0*x1 - 4*c*x1^2 + 6*c*x2^2
    - 24*c*x2*x3 + 12*c*x3^2

theorem E0R_mul_j_self (j x : BR) (h0 : j.re = 0) :
    E0R (x * j) x = Qpoly j.imI j.imJ j.imK x.re x.imI x.imJ x.imK := by
  simp only [E0R, muInvR, Qpoly]; simp [h0]; ring

/-- `j² = −1` forces `j` pure with `3b² − 2a² − 6c² = 1`. -/
theorem pure_of_sq (j : BR) (hj : j * j = -1) :
    j.re = 0 ∧ 3 * j.imJ ^ 2 - 2 * j.imI ^ 2 - 6 * j.imK ^ 2 = 1 := by
  have hre := congrArg QuaternionAlgebra.re hj
  have hI := congrArg QuaternionAlgebra.imI hj
  have hJ := congrArg QuaternionAlgebra.imJ hj
  have hK := congrArg QuaternionAlgebra.imK hj
  simp at hre hI hJ hK
  have h0 : j.re = 0 := by
    by_contra hne
    have a1 : j.imI = 0 := by
      have : j.re * j.imI = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    have a2 : j.imJ = 0 := by
      have : j.re * j.imJ = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    have a3 : j.imK = 0 := by
      have : j.re * j.imK = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [a1, a2, a3] at hre
    nlinarith [sq_nonneg j.re]
  refine ⟨h0, ?_⟩
  rw [h0] at hre
  nlinarith [hre]

/-- `J`-invariance: `E₀(xj, yj) = E₀(x, y)` when `j² = −1`. -/
theorem E0R_mul_j (j x y : BR) (hj : j * j = -1) : E0R (x * j) (y * j) = E0R x y := by
  obtain ⟨h0, hq⟩ := pure_of_sq j hj
  have key : E0R (x * j) (y * j) =
      (j.re ^ 2 - 2 * j.imI ^ 2 + 3 * j.imJ ^ 2 - 6 * j.imK ^ 2) * E0R x y := by
    simp only [E0R, muInvR]; simp; ring
  rw [key, h0]
  have : (0 : ℝ) ^ 2 - 2 * j.imI ^ 2 + 3 * j.imJ ^ 2 - 6 * j.imK ^ 2 = 1 := by linarith
  rw [this, one_mul]

/-- **The `LDLᵀ` decomposition.** -/
theorem Qpoly_ldl (a b c x0 x1 x2 x3 : ℝ) (h1 : b - c ≠ 0) (h2 : b ^ 2 - 2 * c ^ 2 ≠ 0)
    (h3 : b + c ≠ 0) :
    Qpoly a b c x0 x1 x2 x3 =
      2 * (b - c) * (x0 - (b - 2*c) / (b - c) * x1 + a / (b - c) * x2 - 2*a / (b - c) * x3) ^ 2
      + 2 * (b ^ 2 - 2 * c ^ 2) / (b - c) *
          (x1 - a * b / (b ^ 2 - 2 * c ^ 2) * x2 + 2 * a * c / (b ^ 2 - 2 * c ^ 2) * x3) ^ 2
      + 2 * (b + c) * (3 * b ^ 2 - 2 * a ^ 2 - 6 * c ^ 2) / (b ^ 2 - 2 * c ^ 2) *
          (x2 - (b + 2*c) / (b + c) * x3) ^ 2
      + 2 * (3 * b ^ 2 - 2 * a ^ 2 - 6 * c ^ 2) / (b + c) * x3 ^ 2 := by
  simp only [Qpoly]
  field_simp
  ring

/-- **Definiteness on the sheet `b > 0`.** -/
theorem Qpoly_pos (a b c x0 x1 x2 x3 : ℝ) (hb : 0 < b) (hq : 3 * b ^ 2 - 2 * a ^ 2 - 6 * c ^ 2 = 1)
    (hx : ¬ (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0)) : 0 < Qpoly a b c x0 x1 x2 x3 := by
  have hbc2 : 0 < b ^ 2 - 2 * c ^ 2 := by nlinarith [sq_nonneg a, sq_nonneg c]
  have hm : 0 < b - c := by nlinarith [sq_nonneg (b + c), sq_nonneg c]
  have hp : 0 < b + c := by nlinarith [sq_nonneg (b - c), sq_nonneg c]
  rw [Qpoly_ldl a b c x0 x1 x2 x3 hm.ne' hbc2.ne' hp.ne', hq]
  set y0 := x0 - (b - 2*c) / (b - c) * x1 + a / (b - c) * x2 - 2*a / (b - c) * x3
  set y1 := x1 - a * b / (b ^ 2 - 2 * c ^ 2) * x2 + 2 * a * c / (b ^ 2 - 2 * c ^ 2) * x3
  set y2 := x2 - (b + 2*c) / (b + c) * x3
  have d0 : 0 < 2 * (b - c) := by positivity
  have d1 : 0 < 2 * (b ^ 2 - 2 * c ^ 2) / (b - c) := by positivity
  have d2 : 0 < 2 * (b + c) * 1 / (b ^ 2 - 2 * c ^ 2) := by positivity
  have d3 : 0 < 2 * 1 / (b + c) := by positivity
  have t0 := mul_nonneg d0.le (sq_nonneg y0)
  have t1 := mul_nonneg d1.le (sq_nonneg y1)
  have t2 := mul_nonneg d2.le (sq_nonneg y2)
  have t3 := mul_nonneg d3.le (sq_nonneg x3)
  by_contra hle
  push_neg at hle
  have e3 : 2 * 1 / (b + c) * x3 ^ 2 = 0 := by linarith
  have e2 : 2 * (b + c) * 1 / (b ^ 2 - 2 * c ^ 2) * y2 ^ 2 = 0 := by linarith
  have e1 : 2 * (b ^ 2 - 2 * c ^ 2) / (b - c) * y1 ^ 2 = 0 := by linarith
  have e0 : 2 * (b - c) * y0 ^ 2 = 0 := by linarith
  have z3 : x3 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
    ((mul_eq_zero.1 e3).resolve_left d3.ne')
  have z2' : y2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
    ((mul_eq_zero.1 e2).resolve_left d2.ne')
  have z1' : y1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
    ((mul_eq_zero.1 e1).resolve_left d1.ne')
  have z0' : y0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1
    ((mul_eq_zero.1 e0).resolve_left d0.ne')
  have z2 : x2 = 0 := by simpa [y2, z3] using z2'
  have z1 : x1 = 0 := by simpa [y1, z3, z2] using z1'
  have z0 : x0 = 0 := by simpa [y0, z3, z2, z1] using z0'
  exact hx ⟨z0, z1, z2, z3⟩

theorem Qpoly_neg (a b c x0 x1 x2 x3 : ℝ) :
    Qpoly (-a) (-b) (-c) x0 x1 x2 x3 = - Qpoly a b c x0 x1 x2 x3 := by
  simp only [Qpoly]; ring

theorem ne_zero_coords {x : BR} (hx : x ≠ 0) :
    ¬ (x.re = 0 ∧ x.imI = 0 ∧ x.imJ = 0 ∧ x.imK = 0) := by
  rintro ⟨h0, h1, h2, h3⟩
  exact hx (by ext <;> simp [h0, h1, h2, h3])

/-- **The sign step of Lemma P.** For every complex structure `x ↦ xj` (`j² = −1`) on
`B_ℝ = H₁(A, ℝ)`, the form `x ↦ E₀(xj, x)` is definite: positive if `imJ(j) > 0`, negative if
`imJ(j) < 0` (and `imJ(j) ≠ 0` always). So exactly one of `±E₀` is a Riemann form. -/
theorem riemann_sign (j : BR) (hj : j * j = -1) :
    (0 < j.imJ ∧ ∀ x : BR, x ≠ 0 → 0 < E0R (x * j) x) ∨
      (j.imJ < 0 ∧ ∀ x : BR, x ≠ 0 → E0R (x * j) x < 0) := by
  obtain ⟨h0, hq⟩ := pure_of_sq j hj
  rcases lt_trichotomy j.imJ 0 with hb | hb | hb
  · right
    refine ⟨hb, fun x hx => ?_⟩
    rw [E0R_mul_j_self j x h0]
    have := Qpoly_pos (-j.imI) (-j.imJ) (-j.imK) x.re x.imI x.imJ x.imK (by linarith)
      (by nlinarith [hq]) (ne_zero_coords hx)
    rw [Qpoly_neg] at this
    linarith
  · exfalso
    rw [hb] at hq
    nlinarith [sq_nonneg j.imI, sq_nonneg j.imK]
  · left
    refine ⟨hb, fun x hx => ?_⟩
    rw [E0R_mul_j_self j x h0]
    exact Qpoly_pos _ _ _ _ _ _ _ hb hq (ne_zero_coords hx)

/-- **Lemma P on the lattice.** For every complex structure `x ↦ xj` (`j ∈ B_ℝ`, `j² = −1`) on
`H₁ = 𝒪`, exactly one rational multiple `r·E₀` of N5's form is principal (Gram determinant 1 on
`𝒪`) and positive (`r·E₀(xj, x) > 0` for `x ≠ 0`); it is `J`-invariant by `E0R_mul_j`. By
`eq_smul_E0` every alternating form for which `𝒪` acts with adjoint `†` is such a multiple (argued:
the combination, the identification of `E0R` with `E₀ ⊗ ℝ`, the transport to a QM torus `ℂ²/𝒪v` and
Riemann forms ↔ polarizations are not compiled). So, in characteristic 0 and for N5's `μ`, every
QM torus `ℂ²/𝒪v` should have exactly one principal polarization of type `μ`; only the lattice
statement below is in Lean. -/
theorem lemmaP_lattice (j : BR) (hj : j * j = -1) :
    ∃! r : ℚ, (r • gram).det = 1 ∧ ∀ x : BR, x ≠ 0 → 0 < (r : ℝ) * E0R (x * j) x := by
  have hdet : ∀ r : ℚ, (r • gram).det = 1 → r = 1 ∨ r = -1 := by
    intro r h
    rw [Matrix.det_smul, gram_det, Fintype.card_fin, mul_one] at h
    have h4 : (r ^ 2 - 1) * (r ^ 2 + 1) = 0 := by linear_combination h
    have hr2 : r ^ 2 = 1 := by
      rcases mul_eq_zero.1 h4 with h | h
      · linarith
      · nlinarith [sq_nonneg r]
    have : (r - 1) * (r + 1) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  have one_ne : (1 : BR) ≠ 0 := one_ne_zero
  rcases riemann_sign j hj with ⟨-, hpos⟩ | ⟨-, hneg⟩
  · refine ⟨1, ⟨by simp [gram_det], fun x hx => by simpa using hpos x hx⟩, ?_⟩
    rintro r ⟨hr, hp⟩
    rcases hdet r hr with h | h
    · exact h
    · exfalso
      have := hp 1 one_ne
      have h1 := hpos 1 one_ne
      rw [h] at this
      push_cast at this
      linarith
  · refine ⟨-1, ⟨?_, fun x hx => ?_⟩, ?_⟩
    · rw [Matrix.det_smul, gram_det]; norm_num
    · have := hneg x hx
      push_cast
      linarith
    · rintro r ⟨hr, hp⟩
      rcases hdet r hr with h | h
      · exfalso
        have := hp 1 one_ne
        have h1 := hneg 1 one_ne
        rw [h] at this
        push_cast at this
        linarith
      · exact h

end RvQMPolar
