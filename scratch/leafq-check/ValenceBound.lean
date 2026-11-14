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


/-! ## `EllipticOrderLe6` proved (crystallographic restriction; leafq-check)

For `γ = ι(x) ∈ Γ*` fixing `P`, put `μ = cP + d` and `ζ = det γ/μ² = μ̄/μ` (the rotation multiplier at `P`).
Then `|ζ| = 1`, `2 Re ζ = trd(x)²/nrd(x) − 2`, and `trd(x)²/nrd(x) = 4 re(x)²/nrd(x)` is the trace of
conjugation by `x` on the lattice `𝒪`, an integer; so `ζ` is one of the eight numbers
`±1, ±i, (±1 ± i√3)/2`. `γ ↦ ζ` is multiplicative on the stabilizer and determines the Möbius map, and a
product `(±1/2 ± i√3/2)·(±i)` is not among the eight, so the stabilizer embeds in `μ₄` or in `μ₆`. -/

section Elliptic

open PkgI1 ComplexConjugate

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj] <;> ring

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

/-- The reduced norm. -/
def nrd (x : PkgI1.B) : ℚ := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2

theorem det_iota_eq (x : PkgI1.B) : (PkgI1.iota x).det = (nrd x : ℝ) := by
  rw [iota_apply, Matrix.det_fin_two_of, nrd]
  push_cast
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

theorem inO_iff (v : PkgI1.B) : PkgI1.InO v ↔ ∃ n0 n1 n2 n3 : ℤ,
    v = ⟨n0 + n2 / 2, n1 + n3 / 2, n2 / 2, n3 / 2⟩ := by
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n 0, n 1, n 2, n 3, ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring
  · rintro ⟨n0, n1, n2, n3, rfl⟩
    refine ⟨![n0, n1, n2, n3], ?_⟩
    ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem inv_eq {x z : PkgI1.B} (hxz : x * z = 1) (hN : nrd x ≠ 0) :
    z = ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ := by
  set w : PkgI1.B := ⟨x.re / nrd x, -x.imI / nrd x, -x.imJ / nrd x, -x.imK / nrd x⟩ with hw_def
  have hN' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hN
  have hw : w * x = 1 := by
    ext <;> simp [w, nrd] <;> field_simp <;> ring
  calc z = (w * x) * z := by rw [hw, one_mul]
    _ = w * (x * z) := mul_assoc _ _ _
    _ = w := by rw [hxz, mul_one]

/-- The integer coordinates of `w ∈ 𝒪` in N5's basis. -/
theorem inO_coords {w : PkgI1.B} (hw : PkgI1.InO w) : ∃ n0 n1 n2 n3 : ℤ,
    w.re - w.imJ = n0 ∧ w.imI - w.imK = n1 ∧ 2 * w.imJ = n2 ∧ 2 * w.imK = n3 := by
  obtain ⟨n0, n1, n2, n3, rfl⟩ := (inO_iff w).1 hw
  exact ⟨n0, n1, n2, n3, by simp, by simp, by simp; ring, by simp; ring⟩

theorem oBasis_mem (k : Fin 4) : PkgI1.InO (PkgI1.oBasis k) := by
  rw [inO_iff]
  fin_cases k
  · exact ⟨1, 0, 0, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 1, 0, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 0, 1, 0, by ext <;> simp [PkgI1.oBasis]⟩
  · exact ⟨0, 0, 0, 1, by ext <;> simp [PkgI1.oBasis]⟩

/-- **The trace of conjugation by `x` on `𝒪` is the integer `4 re(x)²/nrd(x)`.** -/
theorem adTrace_int {x z : PkgI1.B} (hxz : x * z = 1)
    (hN : ∀ w, PkgI1.InO w → PkgI1.InO (x * w * z) ∧ PkgI1.InO (z * w * x)) (hn : nrd x ≠ 0) :
    ∃ k : ℤ, 4 * x.re ^ 2 / nrd x = k := by
  obtain ⟨a0, -, -, -, ha0, -, -, -⟩ := inO_coords (hN _ (oBasis_mem 0)).1
  obtain ⟨-, a1, -, -, -, ha1, -, -⟩ := inO_coords (hN _ (oBasis_mem 1)).1
  obtain ⟨-, -, a2, -, -, -, ha2, -⟩ := inO_coords (hN _ (oBasis_mem 2)).1
  obtain ⟨-, -, -, a3, -, -, -, ha3⟩ := inO_coords (hN _ (oBasis_mem 3)).1
  refine ⟨a0 + a1 + a2 + a3, ?_⟩
  push_cast
  rw [← ha0, ← ha1, ← ha2, ← ha3, inv_eq hxz hn]
  have hn' : x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 ≠ 0 := hn
  simp [PkgI1.oBasis, nrd]
  field_simp
  ring

/-- `Γ*` is closed under products. -/
theorem gammaStar_mul {γ γ' : GL (Fin 2) ℝ} (h : γ ∈ PkgI1.GammaStar) (h' : γ' ∈ PkgI1.GammaStar) :
    γ * γ' ∈ PkgI1.GammaStar := by
  obtain ⟨x, ⟨z, hxz, hzx, hN⟩, hγ, hd⟩ := h
  obtain ⟨x', ⟨z', hxz', hzx', hN'⟩, hγ', hd'⟩ := h'
  refine ⟨x * x', ⟨z' * z, ?_, ?_, fun w hw => ⟨?_, ?_⟩⟩, ?_, ?_⟩
  · calc x * x' * (z' * z) = x * (x' * z') * z := by simp only [mul_assoc]
      _ = 1 := by rw [hxz', mul_one, hxz]
  · calc z' * z * (x * x') = z' * (z * x) * x' := by simp only [mul_assoc]
      _ = 1 := by rw [hzx, mul_one, hzx']
  · have := (hN _ (hN' w hw).1).1
    have e : x * x' * w * (z' * z) = x * (x' * w * z') * z := by simp only [mul_assoc]
    rw [e]; exact this
  · have := (hN' _ (hN w hw).2).2
    have e : z' * z * w * (x * x') = z' * (z * w * x) * x' := by simp only [mul_assoc]
    rw [e]; exact this
  · rw [Units.val_mul, hγ, hγ', iota_mul]
  · rw [Units.val_mul, Matrix.det_mul]; exact mul_pos hd hd'

theorem one_mem_gammaStar' : (1 : GL (Fin 2) ℝ) ∈ PkgI1.GammaStar := by
  refine ⟨1, ⟨1, mul_one 1, mul_one 1, fun w hw => by simpa using hw⟩, ?_, by simp⟩
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The rotation multiplier `det γ / (cP + d)²`. -/
noncomputable def zeta (γ : GL (Fin 2) ℝ) (P : UpperHalfPlane) : ℂ :=
  (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) / denom γ P ^ 2

theorem fixed_data {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
        2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
        -(γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (P.re ^ 2 + P.im ^ 2) := by
  have hd' : 0 < γ.det.val := by rwa [Matrix.GeneralLinearGroup.val_det_apply]
  have h := congrArg (fun w : UpperHalfPlane => (w : ℂ)) hP
  rw [UpperHalfPlane.coe_smul_of_det_pos hd', div_eq_iff (denom_ne_zero γ P)] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [UpperHalfPlane.num, UpperHalfPlane.denom] at hre him
  have hq := P.im_pos
  have ha : ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - 2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re -
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) * P.im = 0 := by linear_combination him
  have ha' := (mul_eq_zero.1 ha).resolve_right hq.ne'
  refine ⟨by linarith, ?_⟩
  have : (γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      2 * (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    linarith
  rw [this] at hre
  linear_combination hre

theorem det_eq_normSq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    (γ : Matrix (Fin 2) (Fin 2) ℝ).det = Complex.normSq (denom γ P) := by
  obtain ⟨ha, hb⟩ := fixed_data hd hP
  rw [Matrix.det_fin_two, ha, hb]
  simp [UpperHalfPlane.denom, Complex.normSq_apply]
  ring

theorem zeta_eq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : zeta γ P = conj (denom γ P) / denom γ P := by
  have h0 := denom_ne_zero γ P
  unfold zeta
  rw [det_eq_normSq hd hP, Complex.normSq_eq_conj_mul_self]
  field_simp

theorem zeta_normSq {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) : Complex.normSq (zeta γ P) = 1 := by
  rw [zeta_eq hd hP, map_div₀, Complex.normSq_conj, div_self]
  exact (Complex.normSq_pos.2 (denom_ne_zero γ P)).ne'

theorem zeta_re {γ : GL (Fin 2) ℝ} (hd : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {P : UpperHalfPlane} (hP : γ • P = P) :
    2 * (zeta γ P).re = ((γ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1) ^ 2 /
      (γ : Matrix (Fin 2) (Fin 2) ℝ).det - 2 := by
  have hpos := Complex.normSq_pos.2 (denom_ne_zero γ P)
  obtain ⟨ha, -⟩ := fixed_data hd hP
  rw [zeta_eq hd hP, det_eq_normSq hd hP, Complex.div_re, ha]
  simp only [Complex.conj_re, Complex.conj_im]
  have hn : Complex.normSq (denom γ P) = (denom γ P).re ^ 2 + (denom γ P).im ^ 2 := by
    rw [Complex.normSq_apply]; ring
  have hre : (denom γ P).re = (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * P.re +
      (γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp [UpperHalfPlane.denom]
  field_simp
  rw [hn, hre]
  ring

/-- The eight values. -/
noncomputable def w1 : ℂ := ⟨-1 / 2, √3 / 2⟩
noncomputable def w2 : ℂ := ⟨-1 / 2, -(√3 / 2)⟩
noncomputable def w3 : ℂ := ⟨1 / 2, √3 / 2⟩
noncomputable def w4 : ℂ := ⟨1 / 2, -(√3 / 2)⟩

theorem sqrt3_sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem unit_cases (ζ : ℂ) (h1 : Complex.normSq ζ = 1) (k : ℤ) (hk : 2 * ζ.re = k - 2) :
    ζ = 1 ∨ ζ = -1 ∨ ζ = Complex.I ∨ ζ = -Complex.I ∨ ζ = w1 ∨ ζ = w2 ∨ ζ = w3 ∨ ζ = w4 := by
  rw [Complex.normSq_apply] at h1
  have hk0 : (0 : ℝ) ≤ k := by nlinarith [sq_nonneg ζ.im, sq_nonneg (ζ.re + 1)]
  have hk4 : (k : ℝ) ≤ 4 := by nlinarith [sq_nonneg ζ.im, sq_nonneg (ζ.re - 1)]
  have hk0' : 0 ≤ k := by exact_mod_cast hk0
  have hk4' : k ≤ 4 := by exact_mod_cast hk4
  have s3 := sqrt3_sq
  interval_cases k
  · -- re = -1
    have hr : ζ.re = -1 := by push_cast at hk; linarith
    have hi : ζ.im = 0 := by nlinarith [sq_nonneg ζ.im]
    right; left; exact Complex.ext (by simp [hr]) (by simp [hi])
  · -- re = -1/2
    have hr : ζ.re = -1 / 2 := by push_cast at hk; linarith
    have hi : (ζ.im - √3 / 2) * (ζ.im + √3 / 2) = 0 := by
      rw [hr] at h1; linear_combination h1 - s3 / 4
    rcases mul_eq_zero.1 hi with h | h
    · right; right; right; right; left; exact Complex.ext (by simp [w1, hr]) (by simp [w1]; linarith)
    · right; right; right; right; right; left
      exact Complex.ext (by simp [w2, hr]) (by simp [w2]; linarith)
  · -- re = 0
    have hr : ζ.re = 0 := by push_cast at hk; linarith
    have hi : (ζ.im - 1) * (ζ.im + 1) = 0 := by rw [hr] at h1; linear_combination h1
    rcases mul_eq_zero.1 hi with h | h
    · right; right; left; exact Complex.ext (by simp [hr]) (by simp; linarith)
    · right; right; right; left; exact Complex.ext (by simp [hr]) (by simp; linarith)
  · -- re = 1/2
    have hr : ζ.re = 1 / 2 := by push_cast at hk; linarith
    have hi : (ζ.im - √3 / 2) * (ζ.im + √3 / 2) = 0 := by
      rw [hr] at h1; linear_combination h1 - s3 / 4
    rcases mul_eq_zero.1 hi with h | h
    · right; right; right; right; right; right; left
      exact Complex.ext (by simp [w3, hr]) (by simp [w3]; linarith)
    · right; right; right; right; right; right; right
      exact Complex.ext (by simp [w4, hr]) (by simp [w4]; linarith)
  · -- re = 1
    have hr : ζ.re = 1 := by push_cast at hk; linarith
    have hi : ζ.im = 0 := by nlinarith [sq_nonneg ζ.im]
    left; exact Complex.ext (by simp [hr]) (by simp [hi])

end Elliptic

end HSyn.G0Split.FibreQM.PeriodMap

end HDec

#print axioms HDec.HSyn.G0Split.FibreQM.PeriodMap.valenceBound_of
