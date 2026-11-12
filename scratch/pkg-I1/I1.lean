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

end PkgI1
