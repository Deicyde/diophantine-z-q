import Mathlib

/-!
# leafq-check: `ValenceBoundGammaStar` split into the published valence formula and the stabilizer bound

The Prop `HDec.HSyn.G0Split.FibreQM.PeriodMap.ValenceBoundGammaStar` (leaf-fold4's LEAF? field
`valenceBoundGammaStar`, period-map, period-glue §5.1) and what it depends on are copied verbatim from
`scratch/leaf-fold4/Leaves4.lean` (lines 170-235: `PkgI1` §1-§2; 113091-113092: `U`; 113426-113453:
`ValenceBoundGammaStar` with its docstring). Below: the two published inputs as named Props
(`ValenceFormulaGammaStar`, `EllipticOrderLe6`) and the valence count `valenceBound_of`, proved.
-/

namespace HDec

section PkgI1Sec
open Complex Matrix

noncomputable section

namespace PkgI1

/-! ## §1 The quaternion datum (N5 L410-420) -/

/-- `B = (2,-3)`: Mathlib's `QuaternionAlgebra R c₁ c₂ c₃` has `i² = c₁ + c₂ i`, `j² = c₃`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- `i`, `j`, `k = ij` in `B`. -/
def qi : B := ⟨0, 1, 0, 0⟩
def qj : B := ⟨0, 0, 1, 0⟩
def qk : B := ⟨0, 0, 0, 1⟩

/-- N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- Membership in `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`. -/
def InO (x : B) : Prop := ∃ n : Fin 4 → ℤ, x = ∑ k, (n k : ℚ) • oBasis k

/-- `μ = 2j + ij`. -/
def mu : B := ⟨0, 0, 2, 1⟩

/-- `μ⁻¹ = -μ/6`, since `μ² = -6`. -/
def muInv : B := ⟨0, 0, -1/3, -1/6⟩

/-- Reduced trace. -/
def trd (x : B) : ℚ := 2 * x.re

theorem mu_sq : mu * mu = (⟨-6, 0, 0, 0⟩ : B) := by
  ext <;> simp [mu]; norm_num

theorem mu_mul_muInv : mu * muInv = 1 := by
  ext <;> simp [mu, muInv] <;> norm_num

/-- N5's Gram matrix (L413-415). -/
def gram : Matrix (Fin 4) (Fin 4) ℚ := !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0]

/-- **A1 (glue, proved).** `Trd(μ⁻¹ x ȳ)` has N5's Gram matrix in N5's basis. -/
theorem gram_eq (r s : Fin 4) : trd (muInv * oBasis r * star (oBasis s)) = gram r s := by
  fin_cases r <;> fin_cases s <;> simp [trd, muInv, oBasis, gram] <;> norm_num

theorem gram_det : gram.det = 1 := by
  simp [gram, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  rw [show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 from rfl,
    show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 from rfl]
  norm_num

/-! ## §2 The real embedding and `Γ*` -/

/-- `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- The real embedding `ι : B → M₂(ℝ)` (a ring homomorphism: `qm_embed.py` checks it on the
basis; `Mi² = 2`, `Mj² = -3`, `Mi Mj = -Mj Mi`). -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- `x ∈ B` is invertible and normalizes `𝒪`. -/
def NormalizesO (x : B) : Prop :=
  ∃ y : B, x * y = 1 ∧ y * x = 1 ∧ ∀ z : B, InO z → InO (x * z * y) ∧ InO (y * z * x)

/-- `Γ* = ι(N_B(𝒪)⁺)` acting on `ℍ`; modulo scalars this is the group of the Atkin–Lehner
quotient `X₆/W` (positive reduced norm = positive determinant). -/
def GammaStar : Set (GL (Fin 2) ℝ) :=
  {γ | ∃ x : B, NormalizesO x ∧ (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x ∧
    0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det}

end PkgI1

end

end PkgI1Sec

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply ofComplex_apply_of_im_pos num denom denom_ne_zero)

/-- The open upper half-plane as a subset of `ℂ`. -/
def U : Set ℂ := {z : ℂ | 0 < z.im}


/-- **LEAF (valence formula for the cocompact group `Γ*`, inequality consequence).** Let `F` be
holomorphic on `ℍ`, not identically zero, with `|F(γτ)| det(γ)^m = |cτ + d|^{2m} |F(τ)|` for all
`γ ∈ Γ*` (weight `2m`, any unitary multiplier). Then for every finite set `T` of pairwise
`Γ*`-inequivalent points, `2 Σ_{τ ∈ T} ord_τ F ≤ m`.

Source: the valence formula for a Fuchsian group of the first kind,
`Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/2)(2g − 2 + Σ_j (1 − 1/e_j))` (Shimura, *Introduction to the
arithmetic theory of automorphic functions*, 1971, §2.4, Prop. 2.16 / Thm. 2.20; Rankin, *Modular
forms and functions*, 1977, Thm. 4.1.4, for general unitary multiplier systems; UNVERIFIED locators),
and the signature `(0; 2, 4, 6)` of `Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` for the quaternion algebra of
discriminant 6 (`X₆/W ≅ P¹` is the `(2, 4, 6)` triangle quotient: Elkies, *Shimura curve
computations*, ANTS 1998, §3; Baba–Granath 2008, §3.1, as quoted in pkg-I1; UNVERIFIED locators).
With `k = 2m` the right side is `m · (−2 + 1/2 + 3/4 + 5/6) = m/12`; since `e_P ≤ 6`,
`Σ_{T} ord ≤ 6 · m/12 = m/2`. A consequence of the published statements (weaker: an inequality,
and only the bound `e_P ≤ 6`). The absolute-value hypothesis gives a unitary multiplier
(`F(γτ)/(j(γ,τ)^k F(τ))` is holomorphic of modulus one off the zeros, hence constant). -/
def ValenceBoundGammaStar : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) →
      2 * ∑ z ∈ T, analyticOrderAt F (z : ℂ) ≤ (m : ℕ∞)


/-! ## The split (leafq-check) -/

open scoped ENNReal

/-- **`e_P`**: the order of the stabilizer of `P` in `Γ*/ℚ^×`, counted as the number of distinct Möbius
maps `z ↦ γ • z` with `γ ∈ Γ*`, `γ • P = P` (the image of `Γ*` in `PSL₂(ℝ)` acts faithfully on `ℍ`; the
rational scalars act trivially). `Nat.card` is `0` if the stabilizer were infinite. -/
noncomputable def ellOrder (P : UpperHalfPlane) : ℕ :=
  Nat.card {f : UpperHalfPlane → UpperHalfPlane //
    ∃ γ ∈ PkgI1.GammaStar, γ • P = P ∧ f = fun z => γ • z}

/-- **LEAF (the valence formula for `Γ*`, inequality form over a finite set of inequivalent points).**
For `F` holomorphic on `ℍ`, not identically zero, with `|F(γτ)| det(γ)^m = |cτ+d|^{2m}|F(τ)|` for all
`γ ∈ Γ*` (weight `k = 2m`, unitary multiplier), and every finite set `T` of pairwise `Γ*`-inequivalent
points: `Σ_{P ∈ T} ord_P(F)/e_P ≤ m/12`.

Published form: for a Fuchsian group `Γ` of the first kind without cusps and `F ≠ 0` an automorphic form of
weight `k` (unitary multiplier), `Σ_{P ∈ Γ\ℍ} ord_P(F)/e_P = (k/4π)·vol(Γ\ℍ) = (k/2)(2g − 2 + Σ_j(1 − 1/e_j))`
(Shimura, *Introduction to the arithmetic theory of automorphic functions*, 1971, Prop. 2.16 and
Thm. 2.20 / formula (2.4.x); Rankin, *Modular forms and functions*, 1977, Thm. 4.1.4 for arbitrary
unitary multiplier systems; theorem numbers UNVERIFIED), with the signature `(0; 2, 4, 6)` of
`Γ*/ℚ^× = N_B(𝒪)⁺/ℚ^×` for the quaternion algebra of discriminant 6 (Takeuchi, J. Fac. Sci. Univ. Tokyo
24 (1977), the arithmetic triangle group `(2,4,6)`; Elkies, ANTS-III (1998) §3; locators UNVERIFIED), so the
right side is `m·(−2 + 1/2 + 3/4 + 5/6) = m/12`. Dropping the points outside `T` (all terms are `≥ 0`)
gives the inequality. A consequence of the published statements. -/
def ValenceFormulaGammaStar : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) →
    (∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) →
    ∀ T : Finset UpperHalfPlane,
      (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) →
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞) ≤ (m : ℝ≥0∞) / 12

/-- **The stabilizer bound `1 ≤ e_P ≤ 6`** (the elliptic points of `Γ*` have orders `2, 4, 6`: the
signature `(0; 2, 4, 6)`, Takeuchi 1977; or, independently of the signature, the crystallographic
restriction: for `γ = ι(x)` fixing `P`, `trd(x)²/nrd(x)` is the trace of conjugation by `x` on the
lattice `𝒪`, an integer, so the rotation angle at `P` is a multiple of `π/2` or `π/3`). -/
def EllipticOrderLe6 : Prop := ∀ P : UpperHalfPlane, 0 < ellOrder P ∧ ellOrder P ≤ 6

/-- **The valence count (proved).** `ValenceBoundGammaStar` from the valence formula and `e_P ≤ 6`:
`Σ_T ord_P ≤ Σ_T 6·ord_P/e_P ≤ 6·m/12`. -/
theorem valenceBound_of (h1 : ValenceFormulaGammaStar) (h2 : EllipticOrderLe6) :
    ValenceBoundGammaStar := by
  intro m F hF hne haut T hT
  have hV := h1 m F hF hne haut T hT
  rw [← ENat.toENNReal_le]
  have hsum : ((∑ z ∈ T, analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) =
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) :=
    map_sum ENat.toENNRealRingHom _ _
  rw [ENat.toENNReal_mul, hsum, ENat.toENNReal_coe, ENat.toENNReal_ofNat]
  have key : ∀ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) ≤
      6 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞)) := by
    intro z _
    obtain ⟨h0, h6⟩ := h2 z
    set a : ℝ≥0∞ := ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞)
    calc a = 6 * (a / 6) := (ENNReal.mul_div_cancel (by norm_num) (by norm_num)).symm
      _ ≤ 6 * (a / (ellOrder z : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast h6
  calc 2 * ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞)
      ≤ 2 * ∑ z ∈ T, 6 * (((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞)) := by
        gcongr with z hz; exact key z hz
    _ = 12 * ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrder z : ℝ≥0∞) := by
        rw [← Finset.mul_sum, ← mul_assoc]; norm_num
    _ ≤ 12 * ((m : ℝ≥0∞) / 12) := by gcongr
    _ = m := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end HSyn.G0Split.FibreQM.PeriodMap

end HDec

#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMap.valenceBound_of
