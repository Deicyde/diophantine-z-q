/-
pkg-I1: the discriminant-6 Shimura curve (h-trust steps A2-A5, A7, A10, F1).

Leaves statable today over genuine Mathlib objects, and the glue around them that can be
proved today.  Leaves are `def … : Prop`.  Nothing here is imported by `ZInQKernel`.

Contents.
* §1  N5's quaternion datum: `B = (2,-3)`, the maximal order `𝒪`, `μ = 2j + ij`; the Gram
      matrix of `Trd(μ⁻¹ x ȳ)` (A1, proved).
* §2  The real embedding `ι : B → M₂(ℝ)`, the group `Γ* = N_B(𝒪)⁺` acting on `ℍ`.
* §3  Siegel upper half-space of degree 2, the ten even theta constants, `Σθ⁸`, `∏θ²`.
* §4  The explicit modular embedding `Ωqm : ℍ → 𝔥₂` of N5's QM datum (computed in
      `qm_embed.py`).
* §5  LEAF `ThetaModularity` (Igusa: `ψ₄ = Σθ⁸/4` and `χ₁₀ = -∏θ²/2¹⁴` are Siegel modular
      forms of weight 4 and 10 for `Sp₄(ℤ)`), and the glue `thetaRatio_invariant`.
* §6  LEAF `QMHauptmodul` (Lin–Yang 2020 Ex. 30 + Igusa 1967 + Baba–Granath 2008: the theta
      expression of F1 restricted to the QM locus is the Hauptmodul of `Γ*\ℍ` with the values
      `0, ∞, -16/27` at the CM points of discriminants `-4, -3, -24`).
* §7  F1 algebra (proved): Lin–Yang's Igusa vector and Igusa's theta conventions give
      `j·(Σθ⁸)⁵ = 3779136·(∏θ²)²`.
* §8  The pull-back `J(u)` (proved): `G⁶ - 97200F² = H²`; for rational `u ∉ 𝒞`, `J(u)` is
      finite, nonzero and not the branch value `-16/27` (A5, A7).
* §9  Igusa invariants of binary sextics (explicit polynomials, `igusa_poly.py`), and LEAF
      `IgusaClebschSeparation` (Clebsch, Bolza, Igusa 1960).
-/
import Mathlib

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

/-! ## §3 Siegel upper half-space and theta constants -/

/-- The Siegel upper half-space of degree 2. -/
def SiegelH2 : Set (Matrix (Fin 2) (Fin 2) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- A half-integral characteristic `m = (a, b)`, `a b ∈ {0,1}²`. -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- Theta constant `θ_m(Ω) = Σ_{n ∈ ℤ²} exp(πi (n+a/2)ᵀΩ(n+a/2) + πi (n+a/2)ᵀ b)`. -/
def thetaConst (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
    Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

/-- The ten even characteristics (`aᵀb ≡ 0 mod 2`). -/
def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0

theorem card_evenChars : evenChars.card = 10 := by decide

/-- `Σ_{m even} θ_m⁸` (`= 4ψ₄`). -/
def thetaSum8 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∑ m ∈ evenChars, thetaConst m Ω ^ 8

/-- `∏_{m even} θ_m²` (`= -2¹⁴χ₁₀`). -/
def thetaProd2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := ∏ m ∈ evenChars, thetaConst m Ω ^ 2

/-- Numerator of F1: `3779136·(∏θ_m)⁴`. -/
def jNum (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 3779136 * thetaProd2 Ω ^ 2

/-- Denominator of F1: `(Σθ_m⁸)⁵`. -/
def jDen (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := thetaSum8 Ω ^ 5

/-- The action of `Sp₄` on degree-2 matrices: `(AΩ+B)(CΩ+D)⁻¹`. -/
def spAct (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₁₁ * Ω + Mc.toBlocks₁₂) * (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂)⁻¹

/-- The automorphy factor `det(CΩ+D)`. -/
def spFactor (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    ℂ :=
  let Mc := M.map (Int.cast : ℤ → ℂ)
  (Mc.toBlocks₂₁ * Ω + Mc.toBlocks₂₂).det

/-! ## §4 The modular embedding of N5's QM datum (`qm_embed.py`)

For `τ ∈ ℍ` put `v_τ = (τ, 1)ᵀ` and `Λ_τ = ι(𝒪)v_τ ⊂ ℂ²`, with Riemann form
`E(ι(x)v_τ, ι(y)v_τ) = Trd(μ⁻¹xȳ)`. In N5's basis the Gram matrix is `[[0,P],[-Pᵀ,0]]` with
`P = [[-1,1],[1,-2]]`, `P⁻¹ = [[-2,-1],[-1,-1]]`. So `e = (ι(1)v, ι(i)v)` and
`f' = (ι((1+j)/2)v, ι((i+ij)/2)v)·P⁻¹` is a symplectic basis, and `Ω(τ) = F'(τ)⁻¹E(τ)` is a
period matrix of the principally polarized QM surface `A_τ = ℂ²/Λ_τ` (symmetric with positive
definite imaginary part: VERIFIED numerically; the other normalization `E⁻¹F'` belongs to `-E`). -/

/-- `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` of the QM surface at `τ`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

/-! ## §5 LEAF: theta modularity (Igusa) -/

/-- **LEAF (Igusa).** `ψ₄ = 2⁻²Σθ_m⁸` and `χ₁₀ = -2⁻¹⁴∏θ_m²` are Siegel modular forms of
weight 4 and 10 for `Sp₄(ℤ)`: for `M = [[A,B],[C,D]] ∈ Sp₄(ℤ)` and `Ω ∈ 𝔥₂`,
`Σθ⁸(M·Ω) = det(CΩ+D)⁴ Σθ⁸(Ω)` and `∏θ²(M·Ω) = det(CΩ+D)¹⁰ ∏θ²(Ω)`.
Sources: Igusa, *On Siegel modular forms of genus two*, Amer. J. Math. 84 (1962), and *Modular
forms and projective invariants*, Amer. J. Math. 89 (1967) (the theta expressions of `ψ₄`,
`χ₁₀`; pages UNVERIFIED); the theta transformation formula (Igusa, *Theta functions*, 1972,
Ch. V, UNVERIFIED). Exact form (signs, weights) VERIFIED numerically on five generators of
`Sp₄(ℤ)` (`theta_modular.py`). -/
def ThetaModularity : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    thetaSum8 (spAct M Ω) = spFactor M Ω ^ 4 * thetaSum8 Ω ∧
    thetaProd2 (spAct M Ω) = spFactor M Ω ^ 10 * thetaProd2 Ω

/-- **Glue (proved).** The F1 ratio `jNum/jDen` is `Sp₄(ℤ)`-invariant (cross-multiplied), so the
value of F1's theta expression does not depend on the choice of symplectic basis ("permitted
changes of theta structure", N5 L937-938). -/
theorem thetaRatio_invariant (h : ThetaModularity) :
    ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
      jNum (spAct M Ω) * jDen Ω = jNum Ω * jDen (spAct M Ω) := by
  intro M hM Ω hΩ
  obtain ⟨h1, h2⟩ := h M hM Ω hΩ
  simp only [jNum, jDen, h1, h2]
  ring

/-! ## §6 LEAF: the QM Hauptmodul (A2 and F1, analytic form) -/

/-- **LEAF (Baba–Granath 2008 Thm 2.1 and §3; Lin–Yang 2020 Ex. 30 with eqs. (13)-(14);
Igusa 1967; Lauter–Naehrig–Yang 2015 §2.2).** On the QM locus, F1's theta expression
`j_θ = 3779136(∏θ_m)⁴/(Σθ_m⁸)⁵ ∘ Ω` is a Hauptmodul of `Γ*\ℍ = X₆/W`, with value `0` at the
CM points of discriminant `-4`, a pole at those of discriminant `-3`, and value `-16/27` at
those of discriminant `-24`.

Formally: there is a continuous `f : ℍ → ℂ ∪ {∞}` equal to `jNum/jDen ∘ Ω` wherever the
denominator is nonzero (so `f` is the meromorphic quotient), whose fibres are exactly the
`Γ*`-orbits, which is surjective, and which takes the three values at the fixed points of
`ι(x)` for `x ∈ 𝒪` with `x² = -1`, `x² - x + 1 = 0`, `x² = -6` respectively (the CM points of
the maximal orders of discriminants `-4, -3, -24`; every such point is the unique elliptic point
of `Γ*` of order 4, 6, 2).

Faithfulness: `Ω` is a period matrix of the polarized QM surface at `τ` (§4); Lin–Yang's
divisors of `ψ₄` and `χ₁₀` on the QM curve `X ≅ P¹` make `χ₁₀²/ψ₄⁵` a degree-one function with
zero at `P₋₄` and pole at `P₋₃`, and Igusa's theta expressions turn `16·144⁵χ₁₀²/ψ₄⁵` into
`jNum/jDen` (§7). This leaf is weaker than what N5 uses at A2: it says nothing about the
`ℚ`-structure (the canonical model; see `docs/research/pkg-I1.md`, leaf I1-a). Numerically
VERIFIED (`qm_embed.py`): invariance under five generators of `Γ*` and a non-torsion unit of
`𝒪¹`; `j_θ = 0` at `√2 + i`, a pole of order 6 in `τ` at `i√3`, `j_θ = -16/27` at `i√(9+6√2)`,
and `j_θ = 81/64` at the disc `-19` point. -/
def QMHauptmodul : Prop :=
  ∃ f : UpperHalfPlane → OnePoint ℂ, Continuous f ∧
    (∀ τ : UpperHalfPlane, jDen (Omega τ) ≠ 0 →
      f τ = ((jNum (Omega τ) / jDen (Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ γ ∈ GammaStar, γ • τ = τ') ∧
    Function.Surjective f ∧
    (∀ x : B, InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : B, InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : B, InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        f τ = ((-16/27 : ℂ) : OnePoint ℂ))

/-! ## §7 F1 algebra (glue, proved)

Lin–Yang's Igusa vector in a weighted representative with scale `λ`
(`J₂ = 12(j+1)λ`, `J₄ = 6(j²+j+1)λ²`, `J₁₀ = j³λ⁵`), Igusa's `ψ₄ = J₂² - 24J₄`, `χ₁₀ = -J₁₀/4`
(eq. (13)-(14) as used at N5 L911-915), and LNY's theta conventions `ψ₄ = Σ/4`, `χ₁₀ = -Π/2¹⁴`
(`Σ = Σθ⁸`, `Π = ∏θ²`) give `j·Σ⁵ = 3779136·Π²`, i.e. N5's
`j = 16·144⁵χ₁₀²/ψ₄⁵ = 3779136(∏θ)⁴/(Σθ⁸)⁵`. -/
theorem f1_algebra {K : Type*} [Field K] [CharZero K] (j lam J2 J4 J10 Sig Pi : K)
    (hJ2 : J2 = 12 * (j + 1) * lam) (hJ4 : J4 = 6 * (j ^ 2 + j + 1) * lam ^ 2)
    (hJ10 : J10 = j ^ 3 * lam ^ 5)
    (hpsi : J2 ^ 2 - 24 * J4 = Sig / 4) (hchi : -J10 / 4 = -Pi / 2 ^ 14) :
    j * Sig ^ 5 = 3779136 * Pi ^ 2 := by
  have hS : Sig = 576 * j * lam ^ 2 := by
    rw [hJ2, hJ4] at hpsi; linear_combination (-4 : K) * hpsi
  have hP : Pi = 4096 * j ^ 3 * lam ^ 5 := by
    rw [hJ10] at hchi; linear_combination (16384 : K) * hchi
  rw [hS, hP]; ring

/-- The constant: `16·144⁵·2⁻²⁸/2⁻¹⁰ = 3779136` (N5 L922-923). -/
theorem f1_constant : (16 * 144 ^ 5 : ℚ) / 2 ^ 18 = 3779136 := by norm_num

/-! ## §8 The pull-back `J(u)` (N5 L381-386, L510-516, L538-541) -/

def Fu (u : ℚ) : ℚ := u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)
def Gu (u : ℚ) : ℚ := 7 * u ^ 2 + 300 * u + 3600
def Hu (u : ℚ) : ℚ :=
  (u ^ 2 - 60 * u - 1800) * (13 * u ^ 2 + 480 * u + 3600) * (11 * u ^ 2 + 600 * u + 7200)
/-- `J(u) = -57600F(u)²/G(u)⁶`. -/
def Ju (u : ℚ) : ℚ := -57600 * Fu u ^ 2 / Gu u ^ 6

/-- **Glue (proved).** `G⁶ - 97200F² = H²` (N5 L514-516). -/
theorem G6_sub_F2 (u : ℚ) : Gu u ^ 6 - 97200 * Fu u ^ 2 = Hu u ^ 2 := by
  simp only [Gu, Fu, Hu]; ring

/-- No rational square root of `3`. -/
theorem rat_sq_ne_three (r : ℚ) : r ^ 2 ≠ 3 := by
  intro h
  have hirr : Irrational (√(3 : ℕ)) := Nat.prime_three.irrational_sqrt
  have h3 : ((r : ℝ)) ^ 2 = 3 := by exact_mod_cast h
  apply hirr
  refine ⟨|r|, ?_⟩
  push_cast
  rw [← Real.sqrt_sq_eq_abs, h3]

theorem quad_ne_zero (u : ℚ) :
    u ^ 2 - 60 * u - 1800 ≠ 0 ∧ 13 * u ^ 2 + 480 * u + 3600 ≠ 0 ∧
      11 * u ^ 2 + 600 * u + 7200 ≠ 0 := by
  refine ⟨fun h => rat_sq_ne_three ((2 * u - 60) / 60) ?_,
    fun h => rat_sq_ne_three ((26 * u + 480) / 120) ?_,
    fun h => rat_sq_ne_three ((22 * u + 600) / 120) ?_⟩
  · field_simp; linear_combination 4 * h
  · field_simp; linear_combination 52 * h
  · field_simp; linear_combination 44 * h

theorem Hu_ne_zero (u : ℚ) : Hu u ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := quad_ne_zero u
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

theorem Gu_ne_zero (u : ℚ) : Gu u ≠ 0 := by
  unfold Gu; nlinarith [sq_nonneg (7 * u + 150)]

/-- **Glue (proved).** For `u ∈ ℚ \ 𝒞`, `J(u) ≠ 0` (finite since `G(u) ≠ 0`). -/
theorem Ju_ne_zero (u : ℚ) (hu : u ∉ ({0, -15, -20, -24, -30, -60} : Set ℚ)) : Ju u ≠ 0 := by
  have hF : Fu u ≠ 0 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
    simp only [Fu]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact h0
    all_goals intro h; first
      | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith)
      | exact h4 (by linarith) | exact h5 (by linarith)
  unfold Ju
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hF)) (pow_ne_zero 6 (Gu_ne_zero u))

/-- **Glue (proved).** `J(u) + 16/27 = 16H(u)²/(27G(u)⁶)`. -/
theorem Ju_add (u : ℚ) : Ju u + 16 / 27 = 16 * Hu u ^ 2 / (27 * Gu u ^ 6) := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  rw [← G6_sub_F2 u]; unfold Ju; field_simp; ring

/-- **Glue (proved).** For every rational `u`, `J(u)` is not the branch value `-16/27`: the
fibre over `J(u)` lies where `Y₃ → P¹_j` is étale (A5, A7; h-trust A5 last item). -/
theorem Ju_ne_branch (u : ℚ) : Ju u ≠ -16 / 27 := by
  intro h
  have h2 := Ju_add u
  rw [h] at h2
  have : 16 * Hu u ^ 2 / (27 * Gu u ^ 6) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Hu_ne_zero u)))
      (mul_ne_zero (by norm_num) (pow_ne_zero 6 (Gu_ne_zero u)))
  exact this (by rw [← h2]; norm_num)

/-! ### CM elements of `𝒪` (the hypotheses of the three value clauses of `QMHauptmodul` are
satisfiable; glue, proved) -/

theorem inO_of (x : B) (n : Fin 4 → ℤ) (h : x = ∑ k, (n k : ℚ) • oBasis k) : InO x := ⟨n, h⟩

/-- `i + j ∈ 𝒪`, `(i+j)² = -1` (disc `-4`). -/
theorem cm4 : InO ⟨0, 1, 1, 0⟩ ∧ (⟨0, 1, 1, 0⟩ : B) * ⟨0, 1, 1, 0⟩ = -1 := by
  refine ⟨inO_of _ ![-1, 1, 2, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp <;> norm_num

/-- `ω = (1+j)/2 ∈ 𝒪`, `ω² - ω + 1 = 0` (disc `-3`). -/
theorem cm3 : InO ⟨1/2, 0, 1/2, 0⟩ ∧
    (⟨1/2, 0, 1/2, 0⟩ : B) * ⟨1/2, 0, 1/2, 0⟩ - ⟨1/2, 0, 1/2, 0⟩ + 1 = 0 := by
  refine ⟨inO_of _ ![0, 0, 1, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four]
  · ext <;> simp <;> norm_num

/-- `μ = 2j + ij ∈ 𝒪`, `μ² = -6` (disc `-24`). -/
theorem cm24 : InO mu ∧ mu * mu = -6 := by
  refine ⟨inO_of _ ![-2, -1, 4, 2] ?_, ?_⟩
  · ext <;> simp [mu, oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp [mu, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

/-! ### Elkies' coordinate (A10 glue, proved): `t = 1 + 27J/16`, `t(u) = H²/G⁶`,
`t(u) - 1 = -3(180F/G³)²` (h-cm 4.1.1) -/

theorem elkies_t (u : ℚ) : 1 + 27 / 16 * Ju u = Hu u ^ 2 / Gu u ^ 6 := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  rw [← G6_sub_F2 u]; unfold Ju; field_simp; ring

theorem elkies_t_sub_one (u : ℚ) : 27 / 16 * Ju u = -3 * (180 * Fu u / Gu u ^ 3) ^ 2 := by
  have hG : Gu u ≠ 0 := Gu_ne_zero u
  unfold Ju; field_simp; ring

/-! ## §9 Igusa invariants of binary sextics, and the Clebsch–Bolza–Igusa separation leaf

`J₂, J₄, J₆, J₁₀` of the genus-2 curve `y² = f(x)`, `f = Σ aᵢxⁱ` (`deg f ∈ {5, 6}`), in Igusa's
normalization as computed by PARI's `genus2igusa` (Igusa's invariants of the binary sextic
`4f`). The polynomials were found by exact interpolation on isobaric monomials and checked on 10
fresh random sextics against PARI; `J₁₀ = 2⁸·disc(f)` (`igusa_poly.py`, VERIFIED). -/

section Igusa
variable {K : Type*} [Field K]

def J2 (a : Fin 7 → K) : K :=
    (-480 : K) * a 0 * a 6 +
    (80 : K) * a 1 * a 5 +
    (-32 : K) * a 2 * a 4 +
    (12 : K) * a 3 ^ 2

def J4 (a : Fin 7 → K) : K :=
    (5280 : K) * a 0 ^ 2 * a 6 ^ 2 +
    (-1760 : K) * a 0 * a 1 * a 5 * a 6 +
    (2624 : K) * a 0 * a 2 * a 4 * a 6 +
    (-800 : K) * a 0 * a 2 * a 5 ^ 2 +
    (-1344 : K) * a 0 * a 3 ^ 2 * a 6 +
    (480 : K) * a 0 * a 3 * a 4 * a 5 +
    (-128 : K) * a 0 * a 4 ^ 3 +
    (-800 : K) * a 1 ^ 2 * a 4 * a 6 +
    (480 : K) * a 1 ^ 2 * a 5 ^ 2 +
    (480 : K) * a 1 * a 2 * a 3 * a 6 +
    (-224 : K) * a 1 * a 2 * a 4 * a 5 +
    (-16 : K) * a 1 * a 3 ^ 2 * a 5 +
    (32 : K) * a 1 * a 3 * a 4 ^ 2 +
    (-128 : K) * a 2 ^ 3 * a 6 +
    (32 : K) * a 2 ^ 2 * a 3 * a 5 +
    (32 : K) * a 2 ^ 2 * a 4 ^ 2 +
    (-32 : K) * a 2 * a 3 ^ 2 * a 4 +
    (6 : K) * a 3 ^ 4

def J6 (a : Fin 7 → K) : K :=
    (20480 : K) * a 0 ^ 3 * a 6 ^ 3 +
    (-10240 : K) * a 0 ^ 2 * a 1 * a 5 * a 6 ^ 2 +
    (-57344 : K) * a 0 ^ 2 * a 2 * a 4 * a 6 ^ 2 +
    (25600 : K) * a 0 ^ 2 * a 2 * a 5 ^ 2 * a 6 +
    (-10176 : K) * a 0 ^ 2 * a 3 ^ 2 * a 6 ^ 2 +
    (42240 : K) * a 0 ^ 2 * a 3 * a 4 * a 5 * a 6 +
    (-16000 : K) * a 0 ^ 2 * a 3 * a 5 ^ 3 +
    (-16384 : K) * a 0 ^ 2 * a 4 ^ 3 * a 6 +
    (6400 : K) * a 0 ^ 2 * a 4 ^ 2 * a 5 ^ 2 +
    (25600 : K) * a 0 * a 1 ^ 2 * a 4 * a 6 ^ 2 +
    (-8960 : K) * a 0 * a 1 ^ 2 * a 5 ^ 2 * a 6 +
    (42240 : K) * a 0 * a 1 * a 2 * a 3 * a 6 ^ 2 +
    (-26112 : K) * a 0 * a 1 * a 2 * a 4 * a 5 * a 6 +
    (6400 : K) * a 0 * a 1 * a 2 * a 5 ^ 3 +
    (-17728 : K) * a 0 * a 1 * a 3 ^ 2 * a 5 * a 6 +
    (10496 : K) * a 0 * a 1 * a 3 * a 4 ^ 2 * a 6 +
    (2560 : K) * a 0 * a 1 * a 3 * a 4 * a 5 ^ 2 +
    (-1536 : K) * a 0 * a 1 * a 4 ^ 3 * a 5 +
    (-16384 : K) * a 0 * a 2 ^ 3 * a 6 ^ 2 +
    (10496 : K) * a 0 * a 2 ^ 2 * a 3 * a 5 * a 6 +
    (4096 : K) * a 0 * a 2 ^ 2 * a 4 ^ 2 * a 6 +
    (-2560 : K) * a 0 * a 2 ^ 2 * a 4 * a 5 ^ 2 +
    (-6272 : K) * a 0 * a 2 * a 3 ^ 2 * a 4 * a 6 +
    (320 : K) * a 0 * a 2 * a 3 ^ 2 * a 5 ^ 2 +
    (768 : K) * a 0 * a 2 * a 3 * a 4 ^ 2 * a 5 +
    (1248 : K) * a 0 * a 3 ^ 4 * a 6 +
    (-192 : K) * a 0 * a 3 ^ 3 * a 4 * a 5 +
    (-16000 : K) * a 1 ^ 3 * a 3 * a 6 ^ 2 +
    (6400 : K) * a 1 ^ 3 * a 4 * a 5 * a 6 +
    (-1280 : K) * a 1 ^ 3 * a 5 ^ 3 +
    (6400 : K) * a 1 ^ 2 * a 2 ^ 2 * a 6 ^ 2 +
    (2560 : K) * a 1 ^ 2 * a 2 * a 3 * a 5 * a 6 +
    (-2560 : K) * a 1 ^ 2 * a 2 * a 4 ^ 2 * a 6 +
    (256 : K) * a 1 ^ 2 * a 2 * a 4 * a 5 ^ 2 +
    (320 : K) * a 1 ^ 2 * a 3 ^ 2 * a 4 * a 6 +
    (704 : K) * a 1 ^ 2 * a 3 ^ 2 * a 5 ^ 2 +
    (-896 : K) * a 1 ^ 2 * a 3 * a 4 ^ 2 * a 5 +
    (256 : K) * a 1 ^ 2 * a 4 ^ 4 +
    (-1536 : K) * a 1 * a 2 ^ 3 * a 5 * a 6 +
    (768 : K) * a 1 * a 2 ^ 2 * a 3 * a 4 * a 6 +
    (-896 : K) * a 1 * a 2 ^ 2 * a 3 * a 5 ^ 2 +
    (512 : K) * a 1 * a 2 ^ 2 * a 4 ^ 2 * a 5 +
    (-192 : K) * a 1 * a 2 * a 3 ^ 3 * a 6 +
    (448 : K) * a 1 * a 2 * a 3 ^ 2 * a 4 * a 5 +
    (-256 : K) * a 1 * a 2 * a 3 * a 4 ^ 3 +
    (-112 : K) * a 1 * a 3 ^ 4 * a 5 +
    (64 : K) * a 1 * a 3 ^ 3 * a 4 ^ 2 +
    (256 : K) * a 2 ^ 4 * a 5 ^ 2 +
    (-256 : K) * a 2 ^ 3 * a 3 * a 4 * a 5 +
    (64 : K) * a 2 ^ 2 * a 3 ^ 3 * a 5 +
    (64 : K) * a 2 ^ 2 * a 3 ^ 2 * a 4 ^ 2 +
    (-32 : K) * a 2 * a 3 ^ 4 * a 4 +
    (4 : K) * a 3 ^ 6

/-- Monomials of `J₁₀ = 2⁸·disc` as (coefficient, exponents of `a₀…a₆`). -/
def j10Data : List (ℤ × List ℕ) :=
  [(-11943936, [5, 0, 0, 0, 0, 0, 5]),
   (9953280, [4, 1, 0, 0, 0, 1, 4]),
   (15925248, [4, 0, 1, 0, 1, 0, 4]),
   (-8294400, [4, 0, 1, 0, 0, 2, 3]),
   (8957952, [4, 0, 0, 2, 0, 0, 4]),
   (-19906560, [4, 0, 0, 1, 1, 1, 3]),
   (6912000, [4, 0, 0, 1, 0, 3, 2]),
   (-3538944, [4, 0, 0, 0, 3, 0, 3]),
   (11059200, [4, 0, 0, 0, 2, 2, 2]),
   (-5760000, [4, 0, 0, 0, 1, 4, 1]),
   (800000, [4, 0, 0, 0, 0, 6, 0]),
   (-8294400, [3, 2, 0, 0, 1, 0, 4]),
   (138240, [3, 2, 0, 0, 0, 2, 3]),
   (-19906560, [3, 1, 1, 1, 0, 0, 4]),
   (8183808, [3, 1, 1, 0, 1, 1, 3]),
   (-460800, [3, 1, 1, 0, 0, 3, 2]),
   (3981312, [3, 1, 0, 2, 0, 1, 3]),
   (11943936, [3, 1, 0, 1, 2, 0, 3]),
   (-8017920, [3, 1, 0, 1, 1, 2, 2]),
   (576000, [3, 1, 0, 1, 0, 4, 1]),
   (-5603328, [3, 1, 0, 0, 3, 1, 2]),
   (3993600, [3, 1, 0, 0, 2, 3, 1]),
   (-640000, [3, 1, 0, 0, 1, 5, 0]),
   (-3538944, [3, 0, 3, 0, 0, 0, 4]),
   (11943936, [3, 0, 2, 1, 0, 1, 3]),
   (-4423680, [3, 0, 2, 0, 2, 0, 3]),
   (-1658880, [3, 0, 2, 0, 1, 2, 2]),
   (384000, [3, 0, 2, 0, 0, 4, 1]),
   (995328, [3, 0, 1, 2, 1, 0, 3]),
   (-7050240, [3, 0, 1, 2, 0, 2, 2]),
   (-884736, [3, 0, 1, 1, 2, 1, 2]),
   (5068800, [3, 0, 1, 1, 1, 3, 1]),
   (-960000, [3, 0, 1, 1, 0, 5, 0]),
   (2359296, [3, 0, 1, 0, 4, 0, 2]),
   (-2703360, [3, 0, 1, 0, 3, 2, 1]),
   (512000, [3, 0, 1, 0, 2, 4, 0]),
   (-2239488, [3, 0, 0, 4, 0, 0, 3]),
   (5474304, [3, 0, 0, 3, 1, 1, 2]),
   (-345600, [3, 0, 0, 3, 0, 3, 1]),
   (-2211840, [3, 0, 0, 2, 3, 0, 2]),
   (-2488320, [3, 0, 0, 2, 2, 2, 1]),
   (576000, [3, 0, 0, 2, 1, 4, 0]),
   (1769472, [3, 0, 0, 1, 4, 1, 1]),
   (-409600, [3, 0, 0, 1, 3, 3, 0]),
   (-262144, [3, 0, 0, 0, 6, 0, 1]),
   (65536, [3, 0, 0, 0, 5, 2, 0]),
   (6912000, [2, 3, 0, 1, 0, 0, 4]),
   (-460800, [2, 3, 0, 0, 1, 1, 3]),
   (104960, [2, 3, 0, 0, 0, 3, 2]),
   (11059200, [2, 2, 2, 0, 0, 0, 4]),
   (-8017920, [2, 2, 1, 1, 0, 1, 3]),
   (-1658880, [2, 2, 1, 0, 2, 0, 3]),
   (2239488, [2, 2, 1, 0, 1, 2, 2]),
   (-435200, [2, 2, 1, 0, 0, 4, 1]),
   (-7050240, [2, 2, 0, 2, 1, 0, 3]),
   (3946752, [2, 2, 0, 2, 0, 2, 2]),
   (4257792, [2, 2, 0, 1, 2, 1, 2]),
   (-3156480, [2, 2, 0, 1, 1, 3, 1]),
   (512000, [2, 2, 0, 1, 0, 5, 0]),
   (-49152, [2, 2, 0, 0, 4, 0, 2]),
   (63488, [2, 2, 0, 0, 3, 2, 1]),
   (-12800, [2, 2, 0, 0, 2, 4, 0]),
   (-5603328, [2, 1, 3, 0, 0, 1, 3]),
   (-884736, [2, 1, 2, 1, 1, 0, 3]),
   (4257792, [2, 1, 2, 1, 0, 2, 2]),
   (3907584, [2, 1, 2, 0, 2, 1, 2]),
   (-3338240, [2, 1, 2, 0, 1, 3, 1]),
   (576000, [2, 1, 2, 0, 0, 5, 0]),
   (5474304, [2, 1, 1, 3, 0, 0, 3]),
   (-5861376, [2, 1, 1, 2, 1, 1, 2]),
   (506880, [2, 1, 1, 2, 0, 3, 1]),
   (-1474560, [2, 1, 1, 1, 3, 0, 2]),
   (2598912, [2, 1, 1, 1, 2, 2, 1]),
   (-524800, [2, 1, 1, 1, 1, 4, 0]),
   (-163840, [2, 1, 1, 0, 4, 1, 1]),
   (40960, [2, 1, 1, 0, 3, 3, 0]),
   (-1617408, [2, 1, 0, 4, 0, 1, 2]),
   (1492992, [2, 1, 0, 3, 2, 0, 2]),
   (1009152, [2, 1, 0, 3, 1, 2, 1]),
   (-230400, [2, 1, 0, 3, 0, 4, 0]),
   (-1142784, [2, 1, 0, 2, 3, 1, 1]),
   (261120, [2, 1, 0, 2, 2, 3, 0]),
   (196608, [2, 1, 0, 1, 5, 0, 1]),
   (-49152, [2, 1, 0, 1, 4, 2, 0]),
   (2359296, [2, 0, 4, 0, 1, 0, 3]),
   (-49152, [2, 0, 4, 0, 0, 2, 2]),
   (-2211840, [2, 0, 3, 2, 0, 0, 3]),
   (-1474560, [2, 0, 3, 1, 1, 1, 2]),
   (-30720, [2, 0, 3, 1, 0, 3, 1]),
   (-1114112, [2, 0, 3, 0, 3, 0, 2]),
   (1232896, [2, 0, 3, 0, 2, 2, 1]),
   (-230400, [2, 0, 3, 0, 1, 4, 0]),
   (1492992, [2, 0, 2, 3, 0, 1, 2]),
   (2101248, [2, 0, 2, 2, 2, 0, 2]),
   (-1161216, [2, 0, 2, 2, 1, 2, 1]),
   (211200, [2, 0, 2, 2, 0, 4, 0]),
   (-638976, [2, 0, 2, 1, 3, 1, 1]),
   (143360, [2, 0, 2, 1, 2, 3, 0]),
   (131072, [2, 0, 2, 0, 5, 0, 1]),
   (-32768, [2, 0, 2, 0, 4, 2, 0]),
   (-1244160, [2, 0, 1, 4, 1, 0, 2]),
   (41472, [2, 0, 1, 4, 0, 2, 1]),
   (718848, [2, 0, 1, 3, 2, 1, 1]),
   (-161280, [2, 0, 1, 3, 1, 3, 0]),
   (-147456, [2, 0, 1, 2, 4, 0, 1]),
   (36864, [2, 0, 1, 2, 3, 2, 0]),
   (186624, [2, 0, 0, 6, 0, 0, 2]),
   (-124416, [2, 0, 0, 5, 1, 1, 1]),
   (27648, [2, 0, 0, 5, 0, 3, 0]),
   (27648, [2, 0, 0, 4, 3, 0, 1]),
   (-6912, [2, 0, 0, 4, 2, 2, 0]),
   (-5760000, [1, 4, 1, 0, 0, 0, 4]),
   (576000, [1, 4, 0, 1, 0, 1, 3]),
   (384000, [1, 4, 0, 0, 2, 0, 3]),
   (-435200, [1, 4, 0, 0, 1, 2, 2]),
   (81920, [1, 4, 0, 0, 0, 4, 1]),
   (3993600, [1, 3, 2, 0, 0, 1, 3]),
   (5068800, [1, 3, 1, 1, 1, 0, 3]),
   (-3156480, [1, 3, 1, 1, 0, 2, 2]),
   (-3338240, [1, 3, 1, 0, 2, 1, 2]),
   (2500608, [1, 3, 1, 0, 1, 3, 1]),
   (-409600, [1, 3, 1, 0, 0, 5, 0]),
   (-345600, [1, 3, 0, 3, 0, 0, 3]),
   (506880, [1, 3, 0, 2, 1, 1, 2]),
   (-53248, [1, 3, 0, 2, 0, 3, 1]),
   (-30720, [1, 3, 0, 1, 3, 0, 2]),
   (-174592, [1, 3, 0, 1, 2, 2, 1]),
   (40960, [1, 3, 0, 1, 1, 4, 0]),
   (36864, [1, 3, 0, 0, 4, 1, 1]),
   (-9216, [1, 3, 0, 0, 3, 3, 0]),
   (-2703360, [1, 2, 3, 0, 1, 0, 3]),
   (63488, [1, 2, 3, 0, 0, 2, 2]),
   (-2488320, [1, 2, 2, 2, 0, 0, 3]),
   (2598912, [1, 2, 2, 1, 1, 1, 2]),
   (-174592, [1, 2, 2, 1, 0, 3, 1]),
   (1232896, [1, 2, 2, 0, 3, 0, 2]),
   (-1389568, [1, 2, 2, 0, 2, 2, 1]),
   (261120, [1, 2, 2, 0, 1, 4, 0]),
   (1009152, [1, 2, 1, 3, 0, 1, 2]),
   (-1161216, [1, 2, 1, 2, 2, 0, 2]),
   (-617472, [1, 2, 1, 2, 1, 2, 1]),
   (143360, [1, 2, 1, 2, 0, 4, 0]),
   (837632, [1, 2, 1, 1, 3, 1, 1]),
   (-190976, [1, 2, 1, 1, 2, 3, 0]),
   (-147456, [1, 2, 1, 0, 5, 0, 1]),
   (36864, [1, 2, 1, 0, 4, 2, 0]),
   (41472, [1, 2, 0, 4, 1, 0, 2]),
   (-27648, [1, 2, 0, 3, 2, 1, 1]),
   (6144, [1, 2, 0, 3, 1, 3, 0]),
   (6144, [1, 2, 0, 2, 4, 0, 1]),
   (-1536, [1, 2, 0, 2, 3, 2, 0]),
   (1769472, [1, 1, 4, 1, 0, 0, 3]),
   (-163840, [1, 1, 4, 0, 1, 1, 2]),
   (36864, [1, 1, 4, 0, 0, 3, 1]),
   (-1142784, [1, 1, 3, 2, 0, 1, 2]),
   (-638976, [1, 1, 3, 1, 2, 0, 2]),
   (837632, [1, 1, 3, 1, 1, 2, 1]),
   (-161280, [1, 1, 3, 1, 0, 4, 0]),
   (-24576, [1, 1, 3, 0, 3, 1, 1]),
   (6144, [1, 1, 3, 0, 2, 3, 0]),
   (718848, [1, 1, 2, 3, 1, 0, 2]),
   (-27648, [1, 1, 2, 3, 0, 2, 1]),
   (-405504, [1, 1, 2, 2, 2, 1, 1]),
   (91136, [1, 1, 2, 2, 1, 3, 0]),
   (81920, [1, 1, 2, 1, 4, 0, 1]),
   (-20480, [1, 1, 2, 1, 3, 2, 0]),
   (-124416, [1, 1, 1, 5, 0, 0, 2]),
   (82944, [1, 1, 1, 4, 1, 1, 1]),
   (-18432, [1, 1, 1, 4, 0, 3, 0]),
   (-18432, [1, 1, 1, 3, 3, 0, 1]),
   (4608, [1, 1, 1, 3, 2, 2, 0]),
   (-262144, [1, 0, 6, 0, 0, 0, 3]),
   (196608, [1, 0, 5, 1, 0, 1, 2]),
   (131072, [1, 0, 5, 0, 2, 0, 2]),
   (-147456, [1, 0, 5, 0, 1, 2, 1]),
   (27648, [1, 0, 5, 0, 0, 4, 0]),
   (-147456, [1, 0, 4, 2, 1, 0, 2]),
   (6144, [1, 0, 4, 2, 0, 2, 1]),
   (81920, [1, 0, 4, 1, 2, 1, 1]),
   (-18432, [1, 0, 4, 1, 1, 3, 0]),
   (-16384, [1, 0, 4, 0, 4, 0, 1]),
   (4096, [1, 0, 4, 0, 3, 2, 0]),
   (27648, [1, 0, 3, 4, 0, 0, 2]),
   (-18432, [1, 0, 3, 3, 1, 1, 1]),
   (4096, [1, 0, 3, 3, 0, 3, 0]),
   (4096, [1, 0, 3, 2, 3, 0, 1]),
   (-1024, [1, 0, 3, 2, 2, 2, 0]),
   (800000, [0, 6, 0, 0, 0, 0, 4]),
   (-640000, [0, 5, 1, 0, 0, 1, 3]),
   (-960000, [0, 5, 0, 1, 1, 0, 3]),
   (512000, [0, 5, 0, 1, 0, 2, 2]),
   (576000, [0, 5, 0, 0, 2, 1, 2]),
   (-409600, [0, 5, 0, 0, 1, 3, 1]),
   (65536, [0, 5, 0, 0, 0, 5, 0]),
   (512000, [0, 4, 2, 0, 1, 0, 3]),
   (-12800, [0, 4, 2, 0, 0, 2, 2]),
   (576000, [0, 4, 1, 2, 0, 0, 3]),
   (-524800, [0, 4, 1, 1, 1, 1, 2]),
   (40960, [0, 4, 1, 1, 0, 3, 1]),
   (-230400, [0, 4, 1, 0, 3, 0, 2]),
   (261120, [0, 4, 1, 0, 2, 2, 1]),
   (-49152, [0, 4, 1, 0, 1, 4, 0]),
   (-230400, [0, 4, 0, 3, 0, 1, 2]),
   (211200, [0, 4, 0, 2, 2, 0, 2]),
   (143360, [0, 4, 0, 2, 1, 2, 1]),
   (-32768, [0, 4, 0, 2, 0, 4, 0]),
   (-161280, [0, 4, 0, 1, 3, 1, 1]),
   (36864, [0, 4, 0, 1, 2, 3, 0]),
   (27648, [0, 4, 0, 0, 5, 0, 1]),
   (-6912, [0, 4, 0, 0, 4, 2, 0]),
   (-409600, [0, 3, 3, 1, 0, 0, 3]),
   (40960, [0, 3, 3, 0, 1, 1, 2]),
   (-9216, [0, 3, 3, 0, 0, 3, 1]),
   (261120, [0, 3, 2, 2, 0, 1, 2]),
   (143360, [0, 3, 2, 1, 2, 0, 2]),
   (-190976, [0, 3, 2, 1, 1, 2, 1]),
   (36864, [0, 3, 2, 1, 0, 4, 0]),
   (6144, [0, 3, 2, 0, 3, 1, 1]),
   (-1536, [0, 3, 2, 0, 2, 3, 0]),
   (-161280, [0, 3, 1, 3, 1, 0, 2]),
   (6144, [0, 3, 1, 3, 0, 2, 1]),
   (91136, [0, 3, 1, 2, 2, 1, 1]),
   (-20480, [0, 3, 1, 2, 1, 3, 0]),
   (-18432, [0, 3, 1, 1, 4, 0, 1]),
   (4608, [0, 3, 1, 1, 3, 2, 0]),
   (27648, [0, 3, 0, 5, 0, 0, 2]),
   (-18432, [0, 3, 0, 4, 1, 1, 1]),
   (4096, [0, 3, 0, 4, 0, 3, 0]),
   (4096, [0, 3, 0, 3, 3, 0, 1]),
   (-1024, [0, 3, 0, 3, 2, 2, 0]),
   (65536, [0, 2, 5, 0, 0, 0, 3]),
   (-49152, [0, 2, 4, 1, 0, 1, 2]),
   (-32768, [0, 2, 4, 0, 2, 0, 2]),
   (36864, [0, 2, 4, 0, 1, 2, 1]),
   (-6912, [0, 2, 4, 0, 0, 4, 0]),
   (36864, [0, 2, 3, 2, 1, 0, 2]),
   (-1536, [0, 2, 3, 2, 0, 2, 1]),
   (-20480, [0, 2, 3, 1, 2, 1, 1]),
   (4608, [0, 2, 3, 1, 1, 3, 0]),
   (4096, [0, 2, 3, 0, 4, 0, 1]),
   (-1024, [0, 2, 3, 0, 3, 2, 0]),
   (-6912, [0, 2, 2, 4, 0, 0, 2]),
   (4608, [0, 2, 2, 3, 1, 1, 1]),
   (-1024, [0, 2, 2, 3, 0, 3, 0]),
   (-1024, [0, 2, 2, 2, 3, 0, 1]),
   (256, [0, 2, 2, 2, 2, 2, 0])]

def J10 (a : Fin 7 → K) : K :=
  (j10Data.map fun p => (p.1 : K) * ∏ i : Fin 7, a i ^ p.2.getD i 0).sum

/-- `e·(cx+d)⁶ f((ax+b)/(cx+d))` for `M = [[a,b],[c,d]]`: the action of `GL₂ × 𝔾_m` on binary
sextics (as coefficient vectors). -/
def sexticAct (f : Fin 7 → K) (M : Matrix (Fin 2) (Fin 2) K) (e : K) : Fin 7 → K :=
  fun i => (Polynomial.C e * ∑ k : Fin 7, Polynomial.C (f k) *
    (Polynomial.C (M 0 0) * Polynomial.X + Polynomial.C (M 0 1)) ^ (k : ℕ) *
    (Polynomial.C (M 1 0) * Polynomial.X + Polynomial.C (M 1 1)) ^ (6 - (k : ℕ))).coeff i

/-- **LEAF (Clebsch 1872, Bolza 1888, Igusa 1960).** Over an algebraically closed field of
characteristic 0, two binary sextics with nonzero discriminant are equivalent under
`GL₂ × 𝔾_m` iff their Igusa invariants agree in weighted projective space `P(1,2,3,5)`.
(Equivalently: two genus-2 curves are isomorphic iff `[J₂:J₄:J₆:J₁₀]` agree.) The `⇒`
direction is the transformation law `J_{2k}(e·f|M) = (e·det³M)^{2k} J_{2k}(f)` (checked in
`igusa_poly.py`); the content is `⇐`. Igusa, *Arithmetic variety of moduli for genus two*,
Ann. of Math. 72 (1960) (§§1-2, UNVERIFIED locator); Mestre, *Construction de courbes de genre 2
à partir de leurs modules*, Progr. Math. 94 (1991) (UNVERIFIED locator). -/
def IgusaClebschSeparation : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 →
    ((∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e) ↔
      ∃ r : L, r ≠ 0 ∧ J2 g = r * J2 f ∧ J4 g = r ^ 2 * J4 f ∧ J6 g = r ^ 3 * J6 f ∧
        J10 g = r ^ 5 * J10 f)

/-- Lin–Yang's Igusa vector on the QM locus (N5 L538-540), weights `1, 2, 3, 5`. -/
def lyVec (j : K) : Fin 4 → K := ![12 * (j + 1), 6 * (j ^ 2 + j + 1), 4 * (j ^ 3 - 2 * j ^ 2 + 1), j ^ 3]

end Igusa

/-- Spot checks against PARI `genus2igusa` (VERIFIED by `norm_num`). -/
example : J10 (K := ℚ) ![-1, 0, 0, 0, 0, 1, 0] = 800000 := by decide +kernel
example : J2 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = -480 ∧ J4 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = 5280 ∧
    J6 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = 20480 ∧ J10 (K := ℚ) ![1, 1, 0, 0, 0, 0, 1] = -11143936 := by
  refine ⟨by norm_num [J2], by norm_num [J4], by norm_num [J6], ?_⟩
  decide +kernel
example : J2 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -896 ∧ J4 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = 6976 ∧
    J6 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -303616 ∧
    J10 (K := ℚ) ![2, -1, 3, 0, 1, -2, 1] = -2288538368 := by
  refine ⟨by norm_num [J2], by norm_num [J4], by norm_num [J6], ?_⟩
  decide +kernel

/-- **Glue (proved), A7's algebraic step.** If two sextics over an algebraically closed field of
characteristic 0 both have Igusa vector proportional (with weights) to `lyVec j`, `j ≠ 0`, they
are equivalent, i.e. the curves are isomorphic. With Baba–Granath/Lin–Yang (leaf I1-d, not
statable today) this gives "all conjugates of `A` are geometrically isomorphic" for rational `j`. -/
theorem equiv_of_lyVec (hIC : IgusaClebschSeparation) (L : Type) [Field L] [IsAlgClosed L]
    [CharZero L] (j : L) (hj : j ≠ 0) (f g : Fin 7 → L) (lf lg : L) (hlf : lf ≠ 0) (hlg : lg ≠ 0)
    (hf : J2 f = lf * lyVec j 0 ∧ J4 f = lf ^ 2 * lyVec j 1 ∧ J6 f = lf ^ 3 * lyVec j 2 ∧
      J10 f = lf ^ 5 * lyVec j 3)
    (hg : J2 g = lg * lyVec j 0 ∧ J4 g = lg ^ 2 * lyVec j 1 ∧ J6 g = lg ^ 3 * lyVec j 2 ∧
      J10 g = lg ^ 5 * lyVec j 3) :
    ∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e := by
  have h3 : lyVec j 3 ≠ 0 := by simp [lyVec, hj]
  have hf10 : J10 f ≠ 0 := by rw [hf.2.2.2]; exact mul_ne_zero (pow_ne_zero 5 hlf) h3
  have hg10 : J10 g ≠ 0 := by rw [hg.2.2.2]; exact mul_ne_zero (pow_ne_zero 5 hlg) h3
  refine (hIC L f g hf10 hg10).2 ⟨lg / lf, div_ne_zero hlg hlf, ?_, ?_, ?_, ?_⟩
  · rw [hf.1, hg.1]; field_simp
  · rw [hf.2.1, hg.2.1]; field_simp
  · rw [hf.2.2.1, hg.2.2.1]; field_simp
  · rw [hf.2.2.2, hg.2.2.2]; field_simp

end PkgI1

#print axioms PkgI1.gram_det
#print axioms PkgI1.thetaRatio_invariant
#print axioms PkgI1.f1_algebra
#print axioms PkgI1.Ju_ne_branch
#print axioms PkgI1.elkies_t_sub_one
#print axioms PkgI1.equiv_of_lyVec
