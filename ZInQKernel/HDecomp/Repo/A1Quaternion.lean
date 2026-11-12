import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-repo/A1Quaternion.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


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

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat
    QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

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
    (Matrix.of fun a b => trd (e a * e b)) = !![2, 0, 1, 0; 0, 4, 0, 2; 1, 0, -1, 0; 0, 2, 0, 4] :=
        by
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
    (Matrix.of fun a b => E (e a) (e b)) = !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0] :=
        by
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
  have h0 : a.re = 0 := by
      nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg
          a.imK]
  have h1 : a.imI = 0 := by
      nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg
          a.imK]
  have h3 : a.imK = 0 := by
      nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg
          a.imK]
  have h2 : a.imJ = 0 := by
    have : (3 * a.imJ - 4 * a.imK) = 0 := by
        nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg
            a.imK]
    rw [h3] at this; linarith
  exact ha (by ext <;> simp [h0, h1, h2, h3])

/-- `𝒪` is stable under the Rosati involution (`μ ∈ 𝒪` normalizes `𝒪`). -/
theorem ros_mem {x : B} (hx : x ∈ O) : ros x ∈ O := by
  obtain ⟨n, rfl⟩ := hx
  exact ⟨![n 0 + 2 * n 2 - 2 * n 3, n 1 + n 2 - n 3, -3 * n 2 + 4 * n 3, -2 * n 2 + 3 * n 3],
    by ext <;> simp [comb, ros, μ, μinv] <;> push_cast <;> ring⟩

/-! ### Elliptic elements (h-b1 M9, Lemma NV step 2; rv-h-cm (Emb)) -/

/-- Reduced norm `nrd x = x x̄` (a rational number). -/
def nrd (x : B) : ℚ := (x * star x).re

theorem nrd_eq (x : B) : nrd x = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
  simp [nrd]; ring

theorem mul_star_eq (x : B) : x * star x = (nrd x : B) := by
  ext <;> simp [nrd] <;> ring

theorem nrd_mul (x y : B) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd_eq]; simp; ring

/-- **Type `(0,3)`.** If `x ∈ 𝒪` has `Trd x = 0` and `nrd x = 3`, then `(1+x)/2 ∈ 𝒪`; so the CM
order `ℚ(x) ∩ 𝒪` contains `ℤ[(1+x)/2]`, of discriminant `−3` (maximal), not `ℤ[√−3]`. -/
theorem half_one_add_mem {x : B} (hx : x ∈ O) (ht : trd x = 0) (hn : nrd x = 3) :
    (1 / 2 : ℚ) • (1 + x) ∈ O := by
  obtain ⟨n, rfl⟩ := hx
  have ht' : (2 * n 0 + n 2 : ℤ) = 0 := by
    have := ht; simp [trd, comb] at this; exact_mod_cast (by linarith : (2 * (n 0 : ℚ) + n 2) = 0)
  have hn' : (n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2 : ℤ) = 3 :=
      by
    have := hn; rw [nrd_eq] at this; simp [comb] at this
    exact_mod_cast (by linarith : ((n 0 : ℚ) ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2
      - 2 * n 1 * n 3 - 2 * n 3 ^ 2) = 3)
  have h2 : n 2 = -2 * n 0 := by linarith
  rw [h2] at hn'
  have h4 : ((3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) : ℤ) : ZMod 4) = 3 := by
    rw [show (3 * n 0 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2) : ℤ) = 3 by linarith]; rfl
  push_cast at h4
  have key : ∀ a b c : ZMod 4, 3 * a ^ 2 - 2 * (b ^ 2 + b * c + c ^ 2) = 3 →
      (a = 1 ∨ a = 3) ∧ (b = 0 ∨ b = 2) ∧ (c = 0 ∨ c = 2) := by decide
  obtain ⟨ha, hb, hc⟩ := key _ _ _ h4
  have ev : ∀ z : ℤ, ((z : ZMod 4) = 0 ∨ (z : ZMod 4) = 2) → 2 ∣ z := by
    intro z hz
    rcases hz with hz | hz
    · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      exact (dvd_trans (by norm_num) hz)
    · have : ((z : ℤ) : ZMod 4) = ((2 : ℤ) : ZMod 4) := by rw [hz]; rfl
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      obtain ⟨k, hk⟩ := this
      exact ⟨1 - 2 * k, by push_cast at hk; linarith⟩
  have od : 2 ∣ n 0 + 1 := by
    rcases ha with ha | ha
    · have : ((n 0 : ℤ) : ZMod 4) = ((1 : ℤ) : ZMod 4) := by rw [ha]; rfl
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      obtain ⟨k, hk⟩ := this
      exact ⟨1 - 2 * k, by push_cast at hk; linarith⟩
    · have : ((n 0 : ℤ) : ZMod 4) = ((3 : ℤ) : ZMod 4) := by rw [ha]; rfl
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      obtain ⟨k, hk⟩ := this
      exact ⟨2 - 2 * k, by push_cast at hk; linarith⟩
  obtain ⟨a0, ha0⟩ := od
  obtain ⟨a1, ha1⟩ := ev _ hb
  obtain ⟨a3, ha3⟩ := ev _ hc
  have h2q : (n 2 : ℚ) = -2 * n 0 := by exact_mod_cast h2
  have ha0q : (n 0 : ℚ) + 1 = 2 * (a0 : ℚ) := by exact_mod_cast ha0
  have ha1q : (n 1 : ℚ) = 2 * (a1 : ℚ) := by exact_mod_cast ha1
  have ha3q : (n 3 : ℚ) = 2 * (a3 : ℚ) := by exact_mod_cast ha3
  refine ⟨![a0, a1, -n 0, a3], ?_⟩
  ext <;> simp [comb] <;> linarith

/-- `3C² = 2E² + 2B² + 6D²` has no integer solution with `E ≠ 0` (3-adic descent). -/
theorem descent : ∀ (n : ℕ) (E Bq C D : ℤ), E.natAbs = n →
    3 * C ^ 2 = 2 * E ^ 2 + 2 * Bq ^ 2 + 6 * D ^ 2 → E = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E Bq C D hn h
    by_contra hE
    have k1 : ∀ e b c d : ZMod 3, 3 * c ^ 2 = 2 * e ^ 2 + 2 * b ^ 2 + 6 * d ^ 2 →
        e = 0 ∧ b = 0 := by decide
    have h3 := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at h3
    obtain ⟨hE3, hB3⟩ := k1 _ _ _ _ h3
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hE3 hB3
    obtain ⟨E', rfl⟩ := hE3
    obtain ⟨B', rfl⟩ := hB3
    have h' : C ^ 2 = 6 * E' ^ 2 + 6 * B' ^ 2 + 2 * D ^ 2 := by push_cast at h; linarith
    have k2 : ∀ c d e b : ZMod 3, c ^ 2 = 6 * e ^ 2 + 6 * b ^ 2 + 2 * d ^ 2 →
        c = 0 ∧ d = 0 := by decide
    have h3' := congrArg (fun z : ℤ => (z : ZMod 3)) h'
    push_cast at h3'
    obtain ⟨hC3, hD3⟩ := k2 _ _ _ _ h3'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hC3 hD3
    obtain ⟨C', rfl⟩ := hC3
    obtain ⟨D', rfl⟩ := hD3
    have hE' : E' ≠ 0 := by rintro rfl; simp at hE
    have := ih E'.natAbs (by rw [← hn, Int.natAbs_mul]; simp; omega) E' B' C' D' rfl
      (by push_cast at h'; linarith)
    exact hE' this

/-- **Type `(0,2)` is absent:** no `x ∈ B` has `Trd x = 0` and `nrd x = 2`; i.e. `ℚ(√−2)` does
not embed in `B` (3 splits in it; h-b1 M9, rv-h-cm (Emb)). -/
theorem no_trd_zero_nrd_two (x : B) (ht : trd x = 0) (hn : nrd x = 2) : False := by
  have hre : x.re = 0 := by simp [trd] at ht; exact ht
  rw [nrd_eq, hre] at hn
  set b := x.imI; set c := x.imJ; set d := x.imK
  -- common denominator
  set E : ℤ := ((b.den * c.den * d.den : ℕ) : ℤ)
  have hE : E ≠ 0 := by simp [E]
  have hb : ∃ B' : ℤ, (B' : ℚ) = b * E := ⟨b.num * (c.den * d.den : ℕ), by
    simp only [E]; push_cast; rw [← Rat.mul_den_eq_num b]; ring⟩
  have hc : ∃ C' : ℤ, (C' : ℚ) = c * E := ⟨c.num * (b.den * d.den : ℕ), by
    simp only [E]; push_cast; rw [← Rat.mul_den_eq_num c]; ring⟩
  have hd : ∃ D' : ℤ, (D' : ℚ) = d * E := ⟨d.num * (b.den * c.den : ℕ), by
    simp only [E]; push_cast; rw [← Rat.mul_den_eq_num d]; ring⟩
  obtain ⟨B', hB'⟩ := hb
  obtain ⟨C', hC'⟩ := hc
  obtain ⟨D', hD'⟩ := hd
  have key : 3 * C' ^ 2 = 2 * E ^ 2 + 2 * B' ^ 2 + 6 * D' ^ 2 := by
    have : (3 * C' ^ 2 : ℚ) = 2 * E ^ 2 + 2 * B' ^ 2 + 6 * D' ^ 2 := by
      rw [hB', hC', hD']; linear_combination (E : ℚ) ^ 2 * hn
    exact_mod_cast this
  exact hE (descent _ E B' C' D' rfl key)

/-! ### `𝒪/3𝒪` and its unit group (A3: `|(𝒪/3𝒪)^*| = 72`)

`𝒪/3𝒪` is `(ZMod 3)⁴` (coordinates in N5's basis) with the reduction `mul3` of the structure
constants `combMul`; `red3_mul` says reduction mod 3 of coordinates is multiplicative. -/

/-- Multiplication of `𝒪/3𝒪` in coordinates. -/
def mul3 (n m : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0]

def one3 : Fin 4 → ZMod 3 := ![1, 0, 0, 0]

/-- Reduction of coordinates mod 3. -/
def red3 (n : Fin 4 → ℤ) : Fin 4 → ZMod 3 := fun k => (n k : ZMod 3)

theorem red3_mul (n m : Fin 4 → ℤ) : red3 (combMul n m) = mul3 (red3 n) (red3 m) := by
  ext k; fin_cases k <;> simp [red3, combMul, mul3]

/-- Reduced norm in coordinates (`nrd (comb n)`, cf. `nrd_eq`). -/
def nrd3 (x : Fin 4 → ZMod 3) : ZMod 3 :=
  x 0 ^ 2 + x 0 * x 2 + x 2 ^ 2 - 2 * x 1 ^ 2 - 2 * x 1 * x 3 - 2 * x 3 ^ 2

/-- Conjugation in coordinates. -/
def conj3 (x : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 := ![x 0 + x 2, -x 1, -x 2, -x 3]

theorem nrd3_mul (x y : Fin 4 → ZMod 3) : nrd3 (mul3 x y) = nrd3 x * nrd3 y := by
  simp [nrd3, mul3]; ring

theorem nrd3_one : nrd3 one3 = 1 := by simp [nrd3, one3]

theorem mul3_conj3 (x : Fin 4 → ZMod 3) : mul3 x (conj3 x) = fun k => nrd3 x * one3 k := by
  ext k; fin_cases k <;> simp [mul3, conj3, nrd3, one3] <;> ring

theorem conj3_mul3 (x : Fin 4 → ZMod 3) : mul3 (conj3 x) x = fun k => nrd3 x * one3 k := by
  ext k; fin_cases k <;> simp [mul3, conj3, nrd3, one3] <;> ring

theorem mul3_smul_right (x y : Fin 4 → ZMod 3) (c : ZMod 3) :
    mul3 x (fun k => c * y k) = fun k => c * mul3 x y k := by
  ext k; fin_cases k <;> simp [mul3] <;> ring

theorem mul3_smul_left (x y : Fin 4 → ZMod 3) (c : ZMod 3) :
    mul3 (fun k => c * x k) y = fun k => c * mul3 x y k := by
  ext k; fin_cases k <;> simp [mul3] <;> ring

/-- A residue is a unit of `𝒪/3𝒪` iff its reduced norm is nonzero mod 3. -/
theorem isUnit3_iff (x : Fin 4 → ZMod 3) :
    (∃ y, mul3 x y = one3 ∧ mul3 y x = one3) ↔ nrd3 x ≠ 0 := by
  constructor
  · rintro ⟨y, hy, -⟩ h0
    have := nrd3_mul x y
    rw [hy, nrd3_one, h0, zero_mul] at this
    exact one_ne_zero this
  · intro h
    refine ⟨fun k => (nrd3 x)⁻¹ * conj3 x k, ?_, ?_⟩
    · rw [mul3_smul_right, mul3_conj3]
      ext k; simp [← mul_assoc, inv_mul_cancel₀ h]
    · rw [mul3_smul_left, conj3_mul3]
      ext k; simp [← mul_assoc, inv_mul_cancel₀ h]

/-- **`|(𝒪/3𝒪)^*| = 72`** (`form_check.py`, `b1_checks.py` §B; N5 L440 prints `≤ 81`). -/
theorem card_units_mod3 :
    (Finset.univ.filter fun x : Fin 4 → ZMod 3 => ∃ y, mul3 x y = one3 ∧ mul3 y x = one3).card
      = 72 := by
  rw [Finset.filter_congr (fun x _ => isUnit3_iff x)]
  decide

/-! ### `B` is a division algebra; the toric part of PR(ii) step 2 vanishes -/

/-- `X₀² − 2X₁² + 3X₂² − 6X₃² = 0` has only the trivial integer solution (3-adic descent). -/
theorem norm_descent : ∀ (n : ℕ) (a b c d : ℤ), a.natAbs + b.natAbs + c.natAbs + d.natAbs = n →
    a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c d hn h
    have k1 : ∀ a b c d : ZMod 3, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
        a = 0 ∧ b = 0 := by decide
    have h3 := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at h3
    obtain ⟨ha, hb⟩ := k1 _ _ _ _ h3
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    have h' : c ^ 2 - 2 * d ^ 2 + 3 * a' ^ 2 - 6 * b' ^ 2 = 0 := by push_cast at h; linarith
    have h3' := congrArg (fun z : ℤ => (z : ZMod 3)) h'
    push_cast at h3'
    obtain ⟨hc, hd⟩ := k1 _ _ _ _ h3'
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hc hd
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨d', rfl⟩ := hd
    by_cases h0 : a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h0; simp
    · exfalso
      have hpos : 0 < a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs := by
        by_contra hz
        apply h0
        omega
      have := ih (a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs)
        (by rw [← hn]; simp only [Int.natAbs_mul]; norm_num; omega) a' b' c' d' rfl
        (by push_cast at h'; linarith)
      exact h0 this

/-- `nrd x = 0` only for `x = 0`: `B = (2,−3)` is a division algebra. -/
theorem nrd_ne_zero {x : B} (hx : x ≠ 0) : nrd x ≠ 0 := by
  intro hn
  rw [nrd_eq] at hn
  set E : ℤ := ((x.re.den * x.imI.den * x.imJ.den * x.imK.den : ℕ) : ℤ)
  have hE : (E : ℚ) ≠ 0 := by simp [E]
  obtain ⟨a, ha⟩ : ∃ z : ℤ, (z : ℚ) = x.re * E :=
    ⟨x.re.num * (x.imI.den * x.imJ.den * x.imK.den : ℕ), by
      simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.re]; ring⟩
  obtain ⟨b, hb⟩ : ∃ z : ℤ, (z : ℚ) = x.imI * E :=
    ⟨x.imI.num * (x.re.den * x.imJ.den * x.imK.den : ℕ), by
      simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imI]; ring⟩
  obtain ⟨c, hc⟩ : ∃ z : ℤ, (z : ℚ) = x.imJ * E :=
    ⟨x.imJ.num * (x.re.den * x.imI.den * x.imK.den : ℕ), by
      simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imJ]; ring⟩
  obtain ⟨d, hd⟩ : ∃ z : ℤ, (z : ℚ) = x.imK * E :=
    ⟨x.imK.num * (x.re.den * x.imI.den * x.imJ.den : ℕ), by
      simp only [E]; push_cast; rw [← Rat.mul_den_eq_num x.imK]; ring⟩
  have key : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 := by
    have : ((a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 : ℤ) : ℚ) = 0 := by
      push_cast; rw [ha, hb, hc, hd]; linear_combination (E : ℚ) ^ 2 * hn
    exact_mod_cast this
  obtain ⟨h0, h1, h2, h3⟩ := norm_descent _ a b c d rfl key
  apply hx
  have z : ∀ q : ℚ, ∀ z : ℤ, (z : ℚ) = q * E → z = 0 → q = 0 := by
    intro q z hz h0; rw [h0, Int.cast_zero] at hz
    exact (mul_eq_zero.mp hz.symm).resolve_right hE
  ext
  · exact z _ _ ha h0
  · exact z _ _ hb h1
  · exact z _ _ hc h2
  · exact z _ _ hd h3

/-- The inverse `x⁻¹ = x̄ / nrd x`. -/
theorem inv_mul_self {x : B} (hx : x ≠ 0) : ((nrd x)⁻¹ • star x) * x = 1 := by
  have hn := nrd_ne_zero hx
  rw [smul_mul_assoc]
  have : star x * x = (nrd x : B) := by ext <;> simp [nrd] <;> ring
  rw [this]
  ext <;> simp [hn]

/-- **Toric step of Lemma PR(ii)** (h-b1 §4(ii) step 2): a module `V` over `B`, compatible with its
`ℚ`-structure, of `ℚ`-dimension `< 4` is zero. Applied to `V = X(T) ⊗ ℚ` (the character group of
the toric part, `dim T ≤ 2`) with the action of `B = End⁰(A)` through the Néron model. -/
theorem module_eq_zero (V : Type*) [AddCommGroup V] [Module B V] [Module ℚ V]
    [IsScalarTower ℚ B V] [FiniteDimensional ℚ V] (ht : Module.finrank ℚ V < 4) (v : V) :
    v = 0 := by
  by_contra hv
  let f : B →ₗ[ℚ] V :=
    { toFun := fun b => b • v
      map_add' := fun b c => add_smul b c v
      map_smul' := fun q b => smul_assoc q b v }
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    by_contra hb0
    apply hv
    have : ((nrd b)⁻¹ • star b) • (b • v) = v := by rw [smul_smul, inv_mul_self hb0, one_smul]
    rw [← this]
    change ((nrd b)⁻¹ • star b) • f b = 0
    rw [hb, smul_zero]
  have := LinearMap.finrank_le_finrank_of_injective hf
  rw [QuaternionAlgebra.finrank_eq_four] at this
  omega

end GlueRepo.A1

