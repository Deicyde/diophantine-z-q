import Mathlib

/-! # period-map: the light part (`HauptmodulUnique`, `QMDenZeroCM3`)

Task period-map, 2026-11-13. This file imports only Mathlib. It contains, verbatim:
* the `PkgI1` section of `scratch/g0-thetapoint/ThetaPoint.lean` (lines 77-289: the quaternion datum,
  `Γ*`, theta constants, `Ω`, `ThetaModularity`, `QMHauptmodul`), which is itself copied from
  `scratch/pkg-I1/I1.lean`;
* from `scratch/fibre-qm-period/part_fqm.lean`: `QMHauptmodulFn`, `qmHauptmodul_iff`, `QMDenZeroCM3`,
  `IsHolP1At`, `GammaStarFibresCM`, `IsGammaStarHauptmodul`, `HauptmodulUnique` (in the same
  namespace `HSyn.G0Split.FibreQM`).
Then the section `HSyn.G0Split.FibreQM.PeriodMap` (this task) proves `HauptmodulUnique` and
`QMDenZeroCM3` from strictly smaller named Props. -/

section PkgI1Sec
/-! ### Copied from `scratch/pkg-I1/I1.lean` (compiled there). -/

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

/-- **LEAF, COMPOSITE (rv-leaves-a: faithful, but not printed as one theorem; Baba–Granath 2008
Thm 2.1 and the datum of §3 only, not Props. 3.7-3.10; Lin–Yang 2020, arXiv v1 Example 29 (formerly
cited as Ex. 30, v1's discriminant-14 example; corrected 2026-11-12 by loc-fix) with eqs. (13)-(14);
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

end PkgI1

end
end PkgI1Sec

noncomputable section

namespace HSyn

namespace G0Split

namespace FibreQM

open Complex

/-- The clauses of `PkgI1.QMHauptmodul` for one function `f` (verbatim; `PkgI1.QMHauptmodul` is
`∃ f, QMHauptmodulFn f`, `qmHauptmodul_iff`). -/
def QMHauptmodulFn (f : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous f ∧
    (∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 →
      f τ = ((PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) : ℂ) : OnePoint ℂ)) ∧
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    Function.Surjective f ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        f τ = ((-16/27 : ℂ) : OnePoint ℂ))

theorem qmHauptmodul_iff : PkgI1.QMHauptmodul ↔ ∃ f, QMHauptmodulFn f := Iff.rfl

/-- **LEAF candidate (zeros of `ψ₄` on the QM curve).** `Σ_{m even} θ_m(Ω(τ))⁸ = 4ψ₄(Ω(τ))`
vanishes at `τ ∈ ℍ` only at the CM points of discriminant `−3`, the fixed points of `ι(x)` for
`x ∈ 𝒪` with `x² − x + 1 = 0`.

Source: Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020)
(arXiv:1807.00466v1, Example 29 with eqs. (13)-(14)): on the Shimura curve `X = X₆/W ≅ P¹` the
pull-back of `ψ₄` has its zeros only at the elliptic point `P₋₃` (so `j = χ₁₀²/ψ₄⁵`-type functions
have their only pole there), with Igusa's theta expression of `ψ₄` (R4) (locators UNVERIFIED; the
exact divisor statement was not read). Consistent with `QMHauptmodul` (`j_θ` has its only pole at
`P₋₃`) unless `ψ₄` and `χ₁₀` had a common zero on `Ω(ℍ)`. Numerically: `jDen(Ω(i√3)) = 0` with a
zero of order 30 in `τ` (pkg-I1's pole of order 6 of `j_θ`). SPECULATIVE as a reading of the
source. -/
def QMDenZeroCM3 : Prop :=
  ∀ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) = 0 →
    ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ g • τ = τ

/-- `h : ℍ → P¹(ℂ)` is holomorphic at `τ` (as a map to the Riemann sphere): near `τ` it is an
analytic function `g`, or `1/g` with `g` analytic and `g(τ) = 0` (a pole). -/
def IsHolP1At (h : UpperHalfPlane → OnePoint ℂ) (τ : UpperHalfPlane) : Prop :=
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im, h ⟨z, hz⟩ = (g z : OnePoint ℂ)) ∨
  (∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
      ∀ᶠ z in nhds (τ : ℂ), ∀ hz : 0 < z.im,
        h ⟨z, hz⟩ = if g z = 0 then OnePoint.infty else (((g z)⁻¹ : ℂ) : OnePoint ℂ))

/-- The fibre and CM clauses of a normalized Hauptmodul of `Γ*`: fibres exactly the `Γ*`-orbits,
values `0, ∞, −16/27` at the fixed points of `ι(x)` for `x ∈ 𝒪` with `x² = −1`, `x² − x + 1 = 0`,
`x² = −6` (as in `PkgI1.QMHauptmodul`). -/
def GammaStarFibresCM (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  (∀ τ τ' : UpperHalfPlane, h τ = h τ' ↔ ∃ g ∈ PkgI1.GammaStar, g • τ = τ') ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, g • τ = τ →
        h τ = ((-16/27 : ℂ) : OnePoint ℂ))

/-- The clauses shared by `QMHauptmodul`'s `f` and the period map `h`: continuous, holomorphic into
`P¹(ℂ)`, and `GammaStarFibresCM`. -/
def IsGammaStarHauptmodul (h : UpperHalfPlane → OnePoint ℂ) : Prop :=
  Continuous h ∧ (∀ τ, IsHolP1At h τ) ∧ GammaStarFibresCM h

/-- **GLUE (complex analysis: uniqueness of the normalized Hauptmodul of `Γ*`).** A function
`h : ℍ → P¹(ℂ)` with the clauses `IsGammaStarHauptmodul` equals `QMHauptmodul`'s `f`.

Proof sketch (model argument; every step is textbook complex analysis): `Γ*\ℍ` is compact (`B` is
a division algebra; Shimura, *Introduction to the arithmetic theory of automorphic functions*,
Prop. 9.2, UNVERIFIED number). `f` and `h` induce continuous injections `Γ*\ℍ → P¹`; `f`'s is
onto (`QMHauptmodul`), hence a homeomorphism, and `h`'s is open (open mapping theorem) with closed
image, hence onto. So `φ = h ∘ f⁻¹` is a homeomorphism of `P¹`. Away from the finitely many images
of elliptic points and of the zeros of `jDen ∘ Ω`, `f = jNum/jDen ∘ Ω` is holomorphic (theta
series are holomorphic on `𝔥₂`, `Ω` is holomorphic on `ℍ`) and locally injective, so `φ` is
holomorphic there; the finitely many remaining points are removable singularities (`φ` is
continuous). So `φ` is a biholomorphism of `P¹`, a Möbius map, fixing `0, ∞, −16/27` (both satisfy
the CM clauses, and the fixed points exist: `(i+j)² = −1`, `((1+j)/2)² − (1+j)/2 + 1 = 0`,
`(2j+ij)² = −6`), so `φ = id` and `h = f`. Statable over Mathlib as it stands; size: medium-large
(compactness of `Γ*\ℍ`, removable singularities on `P¹`, Möbius rigidity). -/
def HauptmodulUnique : Prop :=
  ∀ f h : UpperHalfPlane → OnePoint ℂ, QMHauptmodulFn f → IsGammaStarHauptmodul h → h = f

end FibreQM

end G0Split

end HSyn

end

/-! ## period-map: `HauptmodulUnique` and `QMDenZeroCM3` from strictly smaller named Props

Task period-map, 2026-11-13. Statements above are verbatim copies; nothing above is changed.

* `hauptmodulUnique_of : ThetaOmegaAnalytic → S8Nonzero → SphereFactorAffine → HauptmodulUnique`.
  Proved here: `QMHauptmodul`'s `f` is holomorphic into `P¹(ℂ)` (`isHolP1At_of_hauptFn`, removable
  singularities and the identity theorem), the three CM points exist (`cm4_exists`, `cm3_exists`,
  `cm24_exists`: explicit `x ∈ 𝒪` and fixed points `√2 + i`, `i√3`, `i√(9+6√2)`), and an affine map
  fixing `0` and `−16/27` is the identity.
* `qmDenZeroCM3_of : ThetaOmegaAnalytic → S8Nonzero → S8Weight8 → S8OrderCM3 →
  ValenceBoundGammaStar → QMDenZeroCM3`. Proved here: `ι` is multiplicative (`iota_mul`), `Γ*` is
  closed under inverses, a point `Γ*`-equivalent to `i√3` is a fixed point of some `ι(x')`,
  `x' ∈ 𝒪`, `x'² − x' + 1 = 0` (conjugation by the normalizer), and the counting argument. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology
open UpperHalfPlane (ofComplex ofComplex_apply ofComplex_apply_of_im_pos num denom denom_ne_zero)
open HSyn.G0Split.FibreQM

/-- The open upper half-plane as a subset of `ℂ`. -/
def U : Set ℂ := {z : ℂ | 0 < z.im}

theorem isOpen_U : IsOpen U := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_U : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected

/-! ### Named Props (glue) shared by both reductions -/

/-- **Holomorphy of the theta constants along the modular embedding** (stated as glue here; PROVED
below, `thetaOmegaAnalytic_proof` in the section on `OmegaSiegel`). `Σ_{m even} θ_m⁸ ∘ Ω`
and `∏_{m even} θ_m² ∘ Ω` are holomorphic on the upper half-plane.

Why true: each `θ_m` is a holomorphic function on the Siegel upper half-space `𝔥₂` (the series
converges normally on the compact subsets of `𝔥₂`: `|exp(πi vᵀΩv)| = exp(−π vᵀ(Im Ω)v)`; Igusa,
*Theta functions*, 1972, Ch. I, or Mumford, *Tata lectures on theta I*, §II.1, UNVERIFIED locators);
`Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)` is a rational function of `τ` whose denominator
`det F₀(τ) ∝ (τ − 3)(τ + 1)` (`QMLattice.det_Fp`) does not vanish on `ℍ`, and `Ω(ℍ) ⊆ 𝔥₂`
(pkg-I1 §4, VERIFIED numerically there). Size: small-medium (Mathlib has the one-variable
`jacobiTheta₂` analyticity proof to imitate: `differentiableOn_tsum_of_summable_norm`). -/
def ThetaOmegaAnalytic : Prop :=
  AnalyticOnNhd ℂ (fun z => PkgI1.thetaSum8 (PkgI1.Omega z)) U ∧
    AnalyticOnNhd ℂ (fun z => PkgI1.thetaProd2 (PkgI1.Omega z)) U

/-- **GLUE (a numerical value).** `Σ_{m even} θ_m⁸(Ω(√2 + i)) ≠ 0`. Numerically
`Σθ_m⁸(Ω(√2 + i)) = −33.9079295761…` (VERIFIED: `py/al_weight.py`, mpmath 40 digits, theta series
truncated at `|n_k| ≤ 12`). A certified bound on the tail of the theta series would prove it.
Size: small. -/
def S8Nonzero : Prop := PkgI1.thetaSum8 (PkgI1.Omega ((√2 : ℂ) + Complex.I)) ≠ 0

theorem mem_U_s2I : ((√2 : ℂ) + Complex.I) ∈ U := by simp [U]

theorem jNum_analytic (hT : ThetaOmegaAnalytic) :
    AnalyticOnNhd ℂ (fun z => PkgI1.jNum (PkgI1.Omega z)) U :=
  fun z hz => analyticAt_const.mul ((hT.2 z hz).pow 2)

theorem jDen_analytic (hT : ThetaOmegaAnalytic) :
    AnalyticOnNhd ℂ (fun z => PkgI1.jDen (PkgI1.Omega z)) U :=
  fun z hz => (hT.1 z hz).pow 5

/-! ### `QMHauptmodul`'s `f` is holomorphic into `P¹(ℂ)` (proved) -/

theorem isHolP1At_of_hauptFn (hT : ThetaOmegaAnalytic) (hS : S8Nonzero)
    {f : UpperHalfPlane → OnePoint ℂ} (hf : QMHauptmodulFn f) (τ : UpperHalfPlane) :
    IsHolP1At f τ := by
  classical
  set N : ℂ → ℂ := fun z => PkgI1.jNum (PkgI1.Omega z) with hNdef
  set D : ℂ → ℂ := fun z => PkgI1.jDen (PkgI1.Omega z) with hDdef
  have hN : AnalyticOnNhd ℂ N U := jNum_analytic hT
  have hD : AnalyticOnNhd ℂ D U := jDen_analytic hT
  have hτU : (τ : ℂ) ∈ U := τ.im_pos
  have hUn : U ∈ 𝓝 (τ : ℂ) := isOpen_U.mem_nhds hτU
  have hfval : ∀ z (hz : 0 < z.im), D z ≠ 0 → f ⟨z, hz⟩ = ((N z / D z : ℂ) : OnePoint ℂ) :=
    fun z hz h => hf.2.1 ⟨z, hz⟩ h
  -- `D` has no zeros in a punctured neighbourhood of `τ` (identity theorem)
  have hDev : ∀ᶠ z in 𝓝[≠] (τ : ℂ), D z ≠ 0 := by
    rcases (hD τ hτU).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have h0 := hD.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_U hτU h
      apply hS
      have := h0 mem_U_s2I
      simpa [D, PkgI1.jDen] using this
    · exact h
  -- `f ∘ ofComplex` is continuous at `τ`
  have hFc : Tendsto (fun z : ℂ => f (ofComplex z)) (𝓝 (τ : ℂ)) (𝓝 (f τ)) := by
    rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, tendsto_map'_iff]
    simp only [Function.comp_def, ofComplex_apply]
    exact hf.1.tendsto τ
  have hF_eq : ∀ᶠ z in 𝓝[≠] (τ : ℂ), f (ofComplex z : UpperHalfPlane) = ((N z / D z : ℂ) : OnePoint ℂ) := by
    filter_upwards [hDev, nhdsWithin_le_nhds hUn] with z hz hzU
    rw [ofComplex_apply_of_im_pos hzU]
    exact hfval z hzU hz
  have hlim : Tendsto (fun z => ((N z / D z : ℂ) : OnePoint ℂ)) (𝓝[≠] (τ : ℂ)) (𝓝 (f τ)) :=
    Tendsto.congr' hF_eq (hFc.mono_left nhdsWithin_le_nhds)
  have hevU : ∀ᶠ z in 𝓝 (τ : ℂ), z ≠ (τ : ℂ) → D z ≠ 0 := eventually_nhdsWithin_iff.mp hDev
  have hτeq : ∀ z (hz : 0 < z.im), z = (τ : ℂ) → (⟨z, hz⟩ : UpperHalfPlane) = τ :=
    fun z hz h => UpperHalfPlane.ext h
  by_cases hinf : f τ = OnePoint.infty
  · -- a pole: `1/f = D/N` extends analytically by `0`
    right
    rw [hinf] at hlim
    have hq : Tendsto (fun z => N z / D z) (𝓝[≠] (τ : ℂ)) (Bornology.cobounded ℂ) := by
      have := (tendsto_comap_iff (g := ((↑) : ℂ → OnePoint ℂ)) (f := fun z => N z / D z)).mpr hlim
      rwa [OnePoint.comap_coe_nhds_infty, coclosedCompact_eq_cocompact,
        ← Metric.cobounded_eq_cocompact] at this
    have hinv : Tendsto (fun z => (N z / D z)⁻¹) (𝓝[≠] (τ : ℂ)) (𝓝 0) :=
      tendsto_inv₀_cobounded.comp hq
    have hne : ∀ᶠ z in 𝓝[≠] (τ : ℂ), N z / D z ≠ 0 := by
      have h1 : ∀ᶠ w in Bornology.cobounded ℂ, w ≠ 0 := by
        have := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually (eventually_gt_atTop 0)
        filter_upwards [this] with w hw
        exact norm_pos_iff.mp hw
      exact hq.eventually h1
    set g : ℂ → ℂ := Function.update (fun z => (N z / D z)⁻¹) (τ : ℂ) 0 with hg
    have hgτ : g τ = 0 := by simp [g]
    have hgc : ContinuousAt g (τ : ℂ) := by
      rw [hg, continuousAt_update_same]
      exact hinv
    have hgd : ∀ᶠ z in 𝓝[≠] (τ : ℂ), DifferentiableAt ℂ g z := by
      filter_upwards [hDev, hne, nhdsWithin_le_nhds hUn, self_mem_nhdsWithin] with z hDz hqz hzU hzτ
      have hd : DifferentiableAt ℂ (fun z => (N z / D z)⁻¹) z :=
        ((hN z hzU).differentiableAt.div (hD z hzU).differentiableAt hDz).inv hqz
      exact hd.congr_of_eventuallyEq
        ((eventually_ne_nhds hzτ).mono fun w hw => Function.update_of_ne hw _ _)
    have hga : AnalyticAt ℂ g (τ : ℂ) :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
    refine ⟨g, hga, hgτ, ?_⟩
    filter_upwards [hevU, eventually_nhdsWithin_iff.mp hne] with z hz1 hz2
    intro hz
    by_cases hzτ : z = τ
    · rw [hτeq z hz hzτ, hinf, hzτ, hgτ, if_pos rfl]
    · have hgz : g z = (N z / D z)⁻¹ := Function.update_of_ne hzτ _ _
      rw [hgz, if_neg (inv_ne_zero (hz2 hzτ)), inv_inv]
      exact hfval z hz (hz1 hzτ)
  · -- a finite value: `f = N/D` extends analytically
    left
    obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← hc] at hlim
    have hq : Tendsto (fun z => N z / D z) (𝓝[≠] (τ : ℂ)) (𝓝 c) :=
      (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).mpr hlim
    set g : ℂ → ℂ := Function.update (fun z => N z / D z) (τ : ℂ) c with hg
    have hgτ : g τ = c := by simp [g]
    have hgc : ContinuousAt g (τ : ℂ) := by
      rw [hg, continuousAt_update_same]
      exact hq
    have hgd : ∀ᶠ z in 𝓝[≠] (τ : ℂ), DifferentiableAt ℂ g z := by
      filter_upwards [hDev, nhdsWithin_le_nhds hUn, self_mem_nhdsWithin] with z hDz hzU hzτ
      have hd : DifferentiableAt ℂ (fun z => N z / D z) z :=
        (hN z hzU).differentiableAt.div (hD z hzU).differentiableAt hDz
      exact hd.congr_of_eventuallyEq
        ((eventually_ne_nhds hzτ).mono fun w hw => Function.update_of_ne hw _ _)
    have hga : AnalyticAt ℂ g (τ : ℂ) :=
      analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
    refine ⟨g, hga, ?_⟩
    filter_upwards [hevU] with z hz1
    intro hz
    by_cases hzτ : z = τ
    · rw [hτeq z hz hzτ, ← hc, hzτ, hgτ]
    · have hgz : g z = N z / D z := Function.update_of_ne hzτ _ _
      rw [hgz]
      exact hfval z hz (hz1 hzτ)

/-! ### The three CM points (proved) -/

/-- A fixed-point criterion for `g ∈ GL₂(ℝ)` of positive determinant. -/
theorem smul_eq_self_of {g : GL (Fin 2) ℝ} (hg : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (τ : UpperHalfPlane)
    (h : ((g 1 0 : ℝ) : ℂ) * (τ : ℂ) ^ 2 + (((g 1 1 : ℝ) : ℂ) - (g 0 0 : ℝ)) * τ
      - (g 0 1 : ℝ) = 0) : g • τ = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hg), div_eq_iff (denom_ne_zero g τ)]
  simp only [num, denom]
  linear_combination -h

theorem sqrt2_sq : (√2 : ℂ) * √2 = 2 := by
  rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num

theorem sqrt2_sq' : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `x = i + j`, `x² = −1`. -/
def x4 : PkgI1.B := ⟨0, 1, 1, 0⟩
/-- `x = (1 + j)/2`, `x² − x + 1 = 0`. -/
def x3 : PkgI1.B := ⟨1/2, 0, 1/2, 0⟩
/-- `x = 2j + ij = μ`, `x² = −6`. -/
def x24 : PkgI1.B := ⟨0, 0, 2, 1⟩

theorem inO_x4 : PkgI1.InO x4 :=
  ⟨![-1, 1, 2, 0], by ext <;> simp [x4, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩
theorem inO_x3 : PkgI1.InO x3 :=
  ⟨![0, 0, 1, 0], by ext <;> simp [x3, PkgI1.oBasis, Fin.sum_univ_four]⟩
theorem inO_x24 : PkgI1.InO x24 :=
  ⟨![-2, -1, 4, 2], by ext <;> simp [x24, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

theorem x4_sq : x4 * x4 = -1 := by ext <;> simp [x4] <;> norm_num
theorem x3_sq : x3 * x3 - x3 + 1 = 0 := by ext <;> simp [x3] <;> norm_num
theorem x24_sq : x24 * x24 = -6 := by
  ext <;> simp [x24, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem iota_apply (x : PkgI1.B) : PkgI1.iota x =
    !![(x.re : ℝ) + x.imI * √2, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
       (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - x.imI * √2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PkgI1.iota, PkgI1.Mi, PkgI1.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_iota (x : PkgI1.B) : (PkgI1.iota x).det =
    (x.re : ℝ) ^ 2 - 2 * (x.imI : ℝ) ^ 2 + 3 * (x.imJ : ℝ) ^ 2 - 6 * (x.imK : ℝ) ^ 2 := by
  rw [iota_apply, Matrix.det_fin_two_of]
  linear_combination (-(x.imI : ℝ) ^ 2 - 3 * (x.imK : ℝ) ^ 2) * sqrt2_sq'

/-- The element of `GL₂(ℝ)` given by `ι(x)` when `nrd(x) ≠ 0`. -/
def glOf (x : PkgI1.B) (h : (PkgI1.iota x).det ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (PkgI1.iota x) h

theorem coe_glOf (x : PkgI1.B) (h : (PkgI1.iota x).det ≠ 0) :
    (glOf x h : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x := rfl

theorem det_x4 : (PkgI1.iota x4).det = 1 := by rw [det_iota]; simp [x4]; norm_num
theorem det_x3 : (PkgI1.iota x3).det = 1 := by rw [det_iota]; simp [x3]; norm_num
theorem det_x24 : (PkgI1.iota x24).det = 6 := by rw [det_iota]; simp [x24]; norm_num

/-- `√2 + i`. -/
def tau4 : UpperHalfPlane := ⟨(√2 : ℂ) + Complex.I, by simp⟩
/-- `i√3`. -/
def tau3 : UpperHalfPlane := ⟨(√3 : ℂ) * Complex.I, by simp⟩
/-- `i√(9 + 6√2)`. -/
def tau24 : UpperHalfPlane := ⟨(√(9 + 6 * √2) : ℂ) * Complex.I, by
  simp only [mul_im, ofReal_re, Complex.I_im, mul_one, ofReal_im, Complex.I_re, mul_zero, add_zero]
  positivity⟩

theorem cm4_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x = -1 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ := by
  refine ⟨x4, inO_x4, x4_sq, glOf x4 (by rw [det_x4]; norm_num), rfl, tau4, ?_⟩
  apply smul_eq_self_of (by rw [coe_glOf, det_x4]; norm_num)
  simp only [coe_glOf, iota_apply, x4, tau4]
  simp
  linear_combination (-1 : ℂ) * sqrt2_sq + Complex.I_sq

theorem cm3_tau3 : glOf x3 (by rw [det_x3]; norm_num) • tau3 = tau3 := by
  apply smul_eq_self_of (by rw [coe_glOf, det_x3]; norm_num)
  simp only [coe_glOf, iota_apply, x3, tau3]
  simp
  have h3 : (√3 : ℂ) * √3 = 3 := by
    rw [← ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  linear_combination (-(1 : ℂ) / 2) * h3 + (1 / 2 : ℂ) * (√3 : ℂ) ^ 2 * Complex.I_sq

theorem cm3_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ :=
  ⟨x3, inO_x3, x3_sq, _, rfl, tau3, cm3_tau3⟩

theorem cm24_exists : ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x = -6 ∧ ∃ g : GL (Fin 2) ℝ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ ∃ τ : UpperHalfPlane, g • τ = τ := by
  refine ⟨x24, inO_x24, x24_sq, glOf x24 (by rw [det_x24]; norm_num), rfl, tau24, ?_⟩
  apply smul_eq_self_of (by rw [coe_glOf, det_x24]; norm_num)
  simp only [coe_glOf, iota_apply, x24, tau24]
  simp
  have h0 : (0 : ℝ) ≤ 9 + 6 * √2 := by positivity
  have h1 : (√(9 + 6 * √2) : ℂ) * √(9 + 6 * √2) = 9 + 6 * √2 := by
    rw [← ofReal_mul, Real.mul_self_sqrt h0]; push_cast; ring
  linear_combination (-(2 : ℂ) + √2) * h1 + (6 : ℂ) * sqrt2_sq
    + (2 - (√2 : ℂ)) * (√(9 + 6 * √2) : ℂ) ^ 2 * Complex.I_sq

/-! ### `HauptmodulUnique` -/

/-- **TEXTBOOK (complex analysis on the Riemann sphere; GLUE as a combination).** Let
`f, h : ℍ → P¹(ℂ)` be holomorphic into `P¹(ℂ)` (`IsHolP1At` at every point), `f` surjective, with
the same fibres, and with a common point mapped to `∞` by both. Then `h = A ∘ f` for an affine map
`A(z) = az + b`, `a ≠ 0`.

Why true (textbook): `φ(f(τ)) := h(τ)` is a well-defined injection `P¹ → P¹` (same fibres, `f`
onto) with `φ(∞) = ∞`. It is holomorphic at every point `f(τ₀)`: in charts `f` is `w ↦ w^m`
near `τ₀` (`f` is not locally constant: a surjective holomorphic map on the connected `ℍ`), and
`h = φ ∘ f` is holomorphic and invariant under `w ↦ ζw` (`ζ^m = 1`), hence a holomorphic function
of `w^m` (Ahlfors, *Complex Analysis*, Ch. 4, §3.3 local mapping; UNVERIFIED locator). An injective
holomorphic `φ : P¹ → P¹` with `φ(∞) = ∞` restricts to an injective entire function with a pole at
`∞`, i.e. a polynomial of degree one (Ahlfors Ch. 4 §3.2 Casorati–Weierstrass, or Conway, *Functions
of One Complex Variable*, Ch. V, UNVERIFIED locators). Size: medium (local normal form of a
holomorphic map, removable singularities on `P¹`, injective polynomials have degree one). -/
def SphereFactorAffine : Prop :=
  ∀ f h : UpperHalfPlane → OnePoint ℂ, (∀ τ, IsHolP1At f τ) → (∀ τ, IsHolP1At h τ) →
    Function.Surjective f → (∀ τ τ', f τ = f τ' ↔ h τ = h τ') →
    (∃ τ, f τ = OnePoint.infty ∧ h τ = OnePoint.infty) →
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ τ, h τ = OnePoint.map (fun z => a * z + b) (f τ)

/-- **`HauptmodulUnique` from strictly smaller named Props (proved).** -/
theorem hauptmodulUnique_of (hT : ThetaOmegaAnalytic) (hS : S8Nonzero)
    (hSF : SphereFactorAffine) : HauptmodulUnique := by
  intro f h hf hh
  have hfib : ∀ τ τ', f τ = f τ' ↔ h τ = h τ' :=
    fun τ τ' => (hf.2.2.1 τ τ').trans (hh.2.2.1 τ τ').symm
  obtain ⟨y3, hy3O, hy3, g3, hg3, τ3, hτ3⟩ := cm3_exists
  obtain ⟨a, b, ha, hab⟩ := hSF f h (isHolP1At_of_hauptFn hT hS hf) hh.2.1 hf.2.2.2.1 hfib
    ⟨τ3, hf.2.2.2.2.2.1 y3 hy3O hy3 g3 hg3 τ3 hτ3, hh.2.2.2.2.1 y3 hy3O hy3 g3 hg3 τ3 hτ3⟩
  obtain ⟨y4, hy4O, hy4, g4, hg4, τ4, hτ4⟩ := cm4_exists
  obtain ⟨y24, hy24O, hy24, g24, hg24, τ24, hτ24⟩ := cm24_exists
  have hb : b = 0 := by
    have := hab τ4
    rw [hf.2.2.2.2.1 y4 hy4O hy4 g4 hg4 τ4 hτ4, hh.2.2.2.1 y4 hy4O hy4 g4 hg4 τ4 hτ4,
      OnePoint.map_some] at this
    have := OnePoint.coe_injective this
    simpa using this.symm
  have ha1 : a = 1 := by
    have := hab τ24
    rw [hf.2.2.2.2.2.2 y24 hy24O hy24 g24 hg24 τ24 hτ24,
      hh.2.2.2.2.2 y24 hy24O hy24 g24 hg24 τ24 hτ24, OnePoint.map_some, hb] at this
    have := OnePoint.coe_injective this
    have h' : (a - 1) * (-16 / 27 : ℂ) = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · norm_num at h''
  funext τ
  have hid : (fun z : ℂ => a * z + b) = id := by funext z; simp [ha1, hb]
  rw [hab τ, hid, OnePoint.map_id]
  rfl

/-! ### `QMDenZeroCM3` -/

/-- `S/dF⁴ = Σθ_m⁸(Ω(τ)) / ((τ − 3)(τ + 1))⁴`, the weight-8 automorphic form of `Γ*`
(`dF(τ) = (τ − 3)(τ + 1)` is proportional to `det F₀(τ)`, `QMLattice.det_Fp`; it has no zero on
`ℍ`). -/
def G8 (z : ℂ) : ℂ := PkgI1.thetaSum8 (PkgI1.Omega z) / ((z - 3) * (z + 1)) ^ 4

/-- **The weight of `Σθ⁸ ∘ Ω` under `Γ*`** (absolute-value form; derived below from the exact form
`S8WeightExact`, `s8Weight8_of`). For `γ ∈ Γ*` and `τ ∈ ℍ`,
`|G8(γτ)| · det(γ)⁴ = |cτ + d|⁸ |G8(τ)|`, i.e. `G8` has weight 8 for the automorphy factor
`(cτ + d)/√det γ`, in absolute value.

Numerically VERIFIED (`py/al_weight.py`, `al_weight_out.txt`; and fibre-qm-period's
`psi4_zeros_out.txt`, the `detF'^(-4)` rows): ratio `1.0` to 10 digits for `γ = ι(x)` with
`x = (1+j)/2, i+j, 3+2i` (reduced norm 1) and the Atkin–Lehner elements `x = j` (norm 3),
`2+i` (norm 2), `2j+ij` (norm 6), `1+j` (norm 4), each at two points. (fibre-qm-period's report
calls this form `S·dF⁴`; its printed formula `|S(γτ)/S(τ)| = |cτ+d|⁸|dF(τ)/dF(γτ)|⁴` is the
correct one and gives `S/dF⁴`.) Why true: for `γ ∈ Γ*` the QM surfaces at `τ` and `γτ` are
isomorphic as principally polarized abelian surfaces (the principal polarization of a QM surface
of discriminant 6 is unique up to `Aut`; Rotger), so `Ω(γτ) = M·Ω(τ)` for some `M ∈ Sp₄(ℤ)`, and
Igusa's `ThetaModularity` (pkg-I1 leaf) gives `Σθ⁸(Ω(γτ)) = det(CΩ + D)⁴ Σθ⁸(Ω(τ))`, with
`det(CΩ(τ) + D) = ±(cτ + d)² dF(γτ)/(det γ · dF(τ))` from the explicit `Ω` (SPECULATIVE in this
generality; the Sp₄(ℤ) matrix for each generator of `Γ*` is a finite computation). Size: medium. -/
def S8Weight8 : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
    ‖G8 ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ 4 =
      ‖denom γ z‖ ^ 8 * ‖G8 (z : ℂ)‖

/-- **A vanishing order** (derived below from `S8WeightExact` and holomorphy, `s8OrderCM3_of`). `S/dF⁴` (equivalently `Σθ_m⁸ ∘ Ω`, since `dF(i√3) ≠ 0`) vanishes
to order at least 2 at `i√3`, the fixed point of `ι((1+j)/2)`.

Numerically VERIFIED: order `1.99992` (fibre-qm-period, `psi4_zeros_out.txt`) and `|S(Ω(i√3))| ≈
4·10⁻⁴⁰` at 40 digits. Why true: `ι((1+j)/2)` fixes `i√3`, with `cτ + d = e^{iπ/3}` there; the
automorphy of `S8Weight8` with its unitary multiplier forces a zero whose order is fixed mod 6
(the usual argument at an elliptic point), and Lin–Yang's divisor of `ψ₄` on `X₆/W` puts a double
zero (in the local parameter of `ℍ`) at `P₋₃` (Lin–Yang 2020, Example 29, UNVERIFIED reading). A
certified numerical proof needs `S(Ω(i√3)) = 0` exactly (which follows from the multiplier if it
is trivial on the stabilizer) and one derivative. Size: small-medium. -/
def S8OrderCM3 : Prop := 2 ≤ analyticOrderAt G8 (tau3 : ℂ)

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

/-! #### `ι` is multiplicative; `Γ*` is closed under inverses; conjugation (proved) -/

theorem iota_mul (x y : PkgI1.B) : PkgI1.iota (x * y) = PkgI1.iota x * PkgI1.iota y := by
  rw [iota_apply, iota_apply, iota_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;>
    (try simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) <;> (try ring_nf)

theorem iota_one : PkgI1.iota 1 = 1 := by
  rw [iota_apply]; ext i j; fin_cases i <;> fin_cases j <;> simp

theorem gammaStar_inv {γ : GL (Fin 2) ℝ} (hγ : γ ∈ PkgI1.GammaStar) : γ⁻¹ ∈ PkgI1.GammaStar := by
  obtain ⟨x, ⟨y, hxy, hyx, hcl⟩, hγx, hdet⟩ := hγ
  have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota y = 1 := by
    rw [hγx, ← iota_mul, hxy, iota_one]
  refine ⟨y, ⟨x, hyx, hxy, fun z hz => ⟨(hcl z hz).2, (hcl z hz).1⟩⟩, ?_, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_right_inv h1
  · rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.inv_eq_right_inv h1]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    rcases lt_or_ge 0 (PkgI1.iota y).det with h | h
    · exact h
    · nlinarith

/-- A point `Γ*`-equivalent to `i√3` is a fixed point of `ι(x')` for some `x' ∈ 𝒪` with
`x'² − x' + 1 = 0` (conjugation by the normalizer). -/
theorem cm3_of_equiv {γ : GL (Fin 2) ℝ} (hγ : γ ∈ PkgI1.GammaStar) {τ : UpperHalfPlane}
    (hτ : γ • tau3 = τ) :
    ∃ x : PkgI1.B, PkgI1.InO x ∧ x * x - x + 1 = 0 ∧ ∃ g : GL (Fin 2) ℝ,
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ g • τ = τ := by
  obtain ⟨u, ⟨v, huv, hvu, hcl⟩, hγu, -⟩ := hγ
  have hγinv : ((γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota v := by
    have h1 : (γ : Matrix (Fin 2) (Fin 2) ℝ) * PkgI1.iota v = 1 := by
      rw [hγu, ← iota_mul, huv, iota_one]
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.inv_eq_right_inv h1
  refine ⟨u * x3 * v, (hcl x3 inO_x3).1, ?_, γ * glOf x3 (by rw [det_x3]; norm_num) * γ⁻¹, ?_, ?_⟩
  · have e1 : u * x3 * v * (u * x3 * v) = u * (x3 * x3) * v := by
      rw [show u * x3 * v * (u * x3 * v) = u * x3 * (v * u) * x3 * v by noncomm_ring, hvu]
      noncomm_ring
    calc u * x3 * v * (u * x3 * v) - u * x3 * v + 1
        = u * (x3 * x3) * v - u * x3 * v + u * v := by rw [e1, huv]
      _ = u * (x3 * x3 - x3 + 1) * v := by noncomm_ring
      _ = 0 := by rw [x3_sq]; simp
  · simp only [Matrix.GeneralLinearGroup.coe_mul, hγinv, hγu, coe_glOf, iota_mul]
  · rw [← hτ, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul, cm3_tau3]

/-- **`QMDenZeroCM3` from strictly smaller named Props (proved).** -/
theorem qmDenZeroCM3_of (hT : ThetaOmegaAnalytic) (hS : S8Nonzero) (hW : S8Weight8)
    (hO : S8OrderCM3) (hV : ValenceBoundGammaStar) : QMDenZeroCM3 := by
  classical
  intro τ hτ
  have hdF : ∀ z ∈ U, ((z - 3) * (z + 1)) ^ 4 ≠ 0 := by
    intro z hz
    apply pow_ne_zero
    have hz' : (0 : ℝ) < z.im := hz
    apply mul_ne_zero <;> intro h0 <;> have := congrArg Complex.im h0 <;> simp at this <;>
      exact hz'.ne' this
  have hGa : AnalyticOnNhd ℂ G8 U := by
    intro z hz
    exact (hT.1 z hz).div ((((analyticAt_id.sub analyticAt_const).mul
      (analyticAt_id.add analyticAt_const))).pow 4) (hdF z hz)
  have hGne : ∃ z ∈ U, G8 z ≠ 0 :=
    ⟨_, mem_U_s2I, div_ne_zero hS (hdF _ mem_U_s2I)⟩
  have hGτ : G8 (τ : ℂ) = 0 := by
    have : PkgI1.thetaSum8 (PkgI1.Omega τ) = 0 := pow_eq_zero_iff (n := 5) (by norm_num) |>.mp hτ
    simp [G8, this]
  by_cases heq : ∃ γ ∈ PkgI1.GammaStar, γ • tau3 = τ
  · obtain ⟨γ, hγ, hγτ⟩ := heq
    obtain ⟨x, hxO, hx, g, hg, hgτ⟩ := cm3_of_equiv hγ hγτ
    exact ⟨x, hxO, hx, g, hg, hgτ⟩
  · exfalso
    push Not at heq
    have hne : tau3 ≠ τ := by
      intro h
      apply heq 1 ⟨1, ⟨1, by simp, by simp, fun z hz => by simp only [one_mul, mul_one]; exact ⟨hz, hz⟩⟩,
        by simp [iota_one], by simp⟩
      simpa using h
    have hpair : ((({tau3, τ} : Finset UpperHalfPlane)) : Set UpperHalfPlane).Pairwise
        (fun z w => ∀ γ ∈ PkgI1.GammaStar, γ • z ≠ w) := by
      intro a ha b hb hab γ hγ
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd rfl hab
      · exact heq γ hγ
      · intro h
        apply heq γ⁻¹ (gammaStar_inv hγ)
        rw [← h, inv_smul_smul]
      · exact absurd rfl hab
    have hval := hV 4 G8 hGa hGne (fun γ hγ z => hW γ hγ z) {tau3, τ} hpair
    rw [Finset.sum_pair hne] at hval
    have h1 : 1 ≤ analyticOrderAt G8 (τ : ℂ) := by
      have : analyticOrderAt G8 (τ : ℂ) ≠ 0 :=
        analyticOrderAt_ne_zero.mpr ⟨hGa _ τ.im_pos, hGτ⟩
      exact Order.one_le_iff_ne_zero.mpr this
    have h3 : (3 : ℕ∞) ≤ analyticOrderAt G8 (tau3 : ℂ) + analyticOrderAt G8 (τ : ℂ) :=
      calc (3 : ℕ∞) = 2 + 1 := by norm_num
        _ ≤ _ := add_le_add hO h1
    have h6 : (2 : ℕ∞) * 3 ≤ 2 * (analyticOrderAt G8 (tau3 : ℂ) + analyticOrderAt G8 (τ : ℂ)) := by
      gcongr
    have := h6.trans hval
    norm_num at this

end HSyn.G0Split.FibreQM.PeriodMap

end

/-! ### Axiom checks -/

#print axioms HSyn.G0Split.FibreQM.PeriodMap.isHolP1At_of_hauptFn
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm4_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm3_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm24_exists
#print axioms HSyn.G0Split.FibreQM.PeriodMap.hauptmodulUnique_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.iota_mul
#print axioms HSyn.G0Split.FibreQM.PeriodMap.gammaStar_inv
#print axioms HSyn.G0Split.FibreQM.PeriodMap.cm3_of_equiv
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of

/-! ## period-map: `ThetaOmegaAnalytic` from `OmegaSiegel` (the theta series converge locally uniformly)

`thetaOmegaAnalytic_of : OmegaSiegel → ThetaOmegaAnalytic`. `OmegaSiegel` (`Ω(τ) ∈ 𝔥₂` for `τ ∈ ℍ`)
is a closed-form computation (VERIFIED with sympy, `py/omega_sym.py`). The proof: the entries of
`Ω` are holomorphic on `ℍ` (adjugate formula; `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2`); near `τ₀` the form
`w ↦ wᵀ Im Ω(τ) w` is bounded below by `c|w|²` uniformly (`(p+r)Q(w) − (pr−q²)|w|² =
(pw₀+qw₁)² + (qw₀+rw₁)²`, continuity); so each theta term is bounded by a summable Gaussian
(Mathlib's Jacobi-theta bound) and the series is holomorphic (`differentiableOn_tsum_of_summable_norm`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology Matrix

/-- **GLUE (computational).** For `τ ∈ ℍ`, `Ω(τ)` lies in the Siegel upper half-space `𝔥₂`
(pkg-I1's `SiegelH2`: symmetric with positive definite imaginary part).

VERIFIED symbolically (`py/omega_sym.py`, sympy; output `omega_sym_out.txt`): `Ω(τ)` is symmetric,
and with `τ = x + iy`, `det Im Ω = 12y²/(|τ − 3|²|τ + 1|²)` and
`(Im Ω)₁₁ = 2y((4 − √2)|τ|² − 6√2x + 12 + 3√2)/(|τ − 3|²|τ + 1|²)`, positive for `y > 0` (the
quadratic in `x` has discriminant `72 − 168 < 0`). Conceptually: `Ω(τ)` is the period matrix of
the principally polarized QM surface `ℂ²/Λ_τ` in a symplectic basis (Riemann's relations). A Lean
proof is a finite computation with the explicit rational entries. Size: small-medium. -/
def OmegaSiegel : Prop := ∀ τ : ℂ, 0 < τ.im → PkgI1.Omega τ ∈ PkgI1.SiegelH2

theorem latVec_apply (x : PkgI1.B) (τ : ℂ) (r : Fin 2) :
    PkgI1.latVec x τ r = (PkgI1.iota x r 0 : ℂ) * τ + (PkgI1.iota x r 1 : ℂ) := by
  simp [PkgI1.latVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem differentiable_F0P (i j : Fin 2) :
    Differentiable ℂ (fun τ => (PkgI1.F0mat τ * PkgI1.Pinv) i j) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [latVec_apply] <;> fun_prop

theorem differentiable_E (i j : Fin 2) : Differentiable ℂ (fun τ => PkgI1.Emat τ i j) := by
  simp only [PkgI1.Emat, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [latVec_apply] <;> fun_prop

theorem det_F0P (τ : ℂ) :
    (PkgI1.F0mat τ * PkgI1.Pinv).det = -(√2 : ℂ) * (τ - 3) * (τ + 1) / 2 := by
  rw [Matrix.det_mul, Matrix.det_fin_two, Matrix.det_fin_two]
  simp [PkgI1.F0mat, PkgI1.Pinv, latVec_apply, PkgI1.iota, PkgI1.Mi, PkgI1.Mj, PkgI1.oBasis,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem det_F0P_ne {τ : ℂ} (hτ : τ.im ≠ 0) : (PkgI1.F0mat τ * PkgI1.Pinv).det ≠ 0 := by
  rw [det_F0P]
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have hs : (√2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact Real.sqrt_ne_zero'.mpr two_pos
  have : -(√2 : ℂ) * (τ - 3) * (τ + 1) ≠ 0 := mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs) h3) h1
  exact div_ne_zero this two_ne_zero

theorem differentiableAt_inv_mul {A E : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {τ : ℂ}
    (hA : ∀ i j, DifferentiableAt ℂ (fun σ => A σ i j) τ)
    (hE : ∀ i j, DifferentiableAt ℂ (fun σ => E σ i j) τ) (hd : (A τ).det ≠ 0) (i j : Fin 2) :
    DifferentiableAt ℂ (fun σ => ((A σ)⁻¹ * E σ) i j) τ := by
  have h1 : ∀ σ, ((A σ)⁻¹ * E σ) i j =
      ((A σ).det)⁻¹ * ∑ k, adjugate (A σ) i k * E σ k j := by
    intro σ
    rw [Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
      Matrix.mul_apply]
  simp_rw [h1]
  have hdet : DifferentiableAt ℂ (fun σ => (A σ).det) τ := by
    simp_rw [Matrix.det_fin_two]
    exact ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  refine (hdet.inv hd).mul ?_
  have hadj : ∀ i k, DifferentiableAt ℂ (fun σ => adjugate (A σ) i k) τ := by
    intro i k
    simp_rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases k <;> simp <;> first | exact hA _ _ | exact (hA _ _).neg
  exact DifferentiableAt.fun_sum (fun k _ => (hadj i k).mul (hE k j))

theorem differentiableAt_omega {τ : ℂ} (hτ : τ.im ≠ 0) (i j : Fin 2) :
    DifferentiableAt ℂ (fun σ => PkgI1.Omega σ i j) τ :=
  differentiableAt_inv_mul (A := fun σ => PkgI1.F0mat σ * PkgI1.Pinv) (E := PkgI1.Emat)
    (fun i j => (differentiable_F0P i j) τ) (fun i j => (differentiable_E i j) τ)
    (det_F0P_ne hτ) i j

/-- The summand of `thetaConst m (Ω τ)`. -/
def thTerm (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ) : ℂ :=
  let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
  Complex.exp (Real.pi * I * (v ⬝ᵥ (PkgI1.Omega τ *ᵥ v)) +
    Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

theorem thetaConst_omega (m : PkgI1.Char2) (τ : ℂ) :
    PkgI1.thetaConst m (PkgI1.Omega τ) = ∑' n, thTerm m n τ := rfl

/-- The real vector `n + a/2`. -/
def wv (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) : ℝ := (n k : ℝ) + ((m.1 k : ℕ) : ℝ) / 2

/-- `wᵀ Im Ω(τ) w`. -/
def qf (τ : ℂ) (w : Fin 2 → ℝ) : ℝ :=
  w 0 ^ 2 * (PkgI1.Omega τ 0 0).im +
    w 0 * w 1 * ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) +
    w 1 ^ 2 * (PkgI1.Omega τ 1 1).im

theorem norm_thTerm (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ) :
    ‖thTerm m n τ‖ = Real.exp (-Real.pi * qf τ (wv m n)) := by
  rw [thTerm, Complex.norm_exp]
  congr 1
  simp [qf, wv, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

theorem quad_lower (p q r w0 w1 : ℝ) (h : 0 < p + r) :
    (p * r - q ^ 2) / (p + r) * (w0 ^ 2 + w1 ^ 2) ≤
      w0 ^ 2 * p + w0 * w1 * (2 * q) + w1 ^ 2 * r := by
  rw [div_mul_eq_mul_div, div_le_iff₀ h]
  nlinarith [sq_nonneg (p * w0 + q * w1), sq_nonneg (q * w0 + r * w1)]

theorem wv_sq_ge (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) :
    (n k : ℝ) ^ 2 - |(n k : ℝ)| ≤ wv m n k ^ 2 := by
  have h0 : (0 : ℝ) ≤ ((m.1 k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((m.1 k : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp (m.1 k).isLt
  rw [wv]
  have ha : -|(n k : ℝ)| ≤ (n k : ℝ) * ((m.1 k : ℕ) : ℝ) := by
    rcases le_total 0 (n k : ℝ) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; nlinarith
  nlinarith [sq_nonneg (((m.1 k : ℕ) : ℝ) / 2)]

/-- The Gaussian bound (Mathlib's Jacobi-theta bound with `T = c`, `S = c/2`). -/
def gb (c : ℝ) (k : ℤ) : ℝ := Real.exp (-Real.pi * (c * (k : ℝ) ^ 2 - 2 * (c / 2) * |(k : ℝ)|))

theorem summable_gb2 {c : ℝ} (hc : 0 < c) :
    Summable (fun n : Fin 2 → ℤ => gb c (n 0) * gb c (n 1)) := by
  have h1 : Summable (gb c) := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound (c / 2) hc 0).congr fun k => ?_
    simp only [gb, pow_zero, one_mul, Int.cast_abs]
  have h2 : Summable (fun p : ℤ × ℤ => gb c p.1 * gb c p.2) :=
    h1.mul_of_nonneg h1 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  exact (finTwoArrowEquiv ℤ).summable_iff.mpr h2

theorem norm_thTerm_le {c : ℝ} (hc : 0 < c) (m : PkgI1.Char2) (n : Fin 2 → ℤ) (τ : ℂ)
    (hq : ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w) :
    ‖thTerm m n τ‖ ≤ gb c (n 0) * gb c (n 1) := by
  rw [norm_thTerm, gb, gb, ← Real.exp_add, Real.exp_le_exp]
  have h := hq (wv m n)
  have h0 := wv_sq_ge m n 0
  have h1 := wv_sq_ge m n 1
  have hp := Real.pi_pos
  have h2 : c * (((n 0 : ℝ) ^ 2 - |(n 0 : ℝ)|) + ((n 1 : ℝ) ^ 2 - |(n 1 : ℝ)|)) ≤ qf τ (wv m n) :=
    le_trans (mul_le_mul_of_nonneg_left (add_le_add h0 h1) hc.le) h
  have h3 := mul_le_mul_of_nonneg_left h2 hp.le
  nlinarith [h3]

/-- **`ThetaOmegaAnalytic` from `OmegaSiegel` (proved).** -/
theorem thetaOmegaAnalytic_of (hS : OmegaSiegel) : ThetaOmegaAnalytic := by
  -- each theta constant along `Ω` is analytic at every `τ₀ ∈ ℍ`
  have hθ : ∀ τ₀ ∈ U, ∀ m : PkgI1.Char2,
      AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
    intro τ₀ hτ₀ m
    have hτ₀' : (0 : ℝ) < τ₀.im := hτ₀
    obtain ⟨hsym, hpd⟩ := hS τ₀ hτ₀'
    set p : ℂ → ℝ := fun τ => (PkgI1.Omega τ 0 0).im with hp
    set q : ℂ → ℝ := fun τ => ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) / 2 with hq
    set r : ℂ → ℝ := fun τ => (PkgI1.Omega τ 1 1).im with hr
    have hcont : ∀ i j, ContinuousAt (fun τ => (PkgI1.Omega τ i j).im) τ₀ := fun i j =>
      Complex.continuous_im.continuousAt.comp (differentiableAt_omega hτ₀'.ne' i j).continuousAt
    have hp0 : 0 < p τ₀ := by
      have := hpd.diag_pos (i := 0); simpa [hp] using this
    have hr0 : 0 < r τ₀ := by
      have := hpd.diag_pos (i := 1); simpa [hr] using this
    have hsym01 : PkgI1.Omega τ₀ 1 0 = PkgI1.Omega τ₀ 0 1 := by
      have := congrFun (congrFun hsym 0) 1; simpa using this
    have hdet0 : 0 < p τ₀ * r τ₀ - q τ₀ ^ 2 := by
      have := hpd.det_pos
      rw [Matrix.det_fin_two] at this
      simp only [Matrix.map_apply] at this
      rw [hsym01] at this
      simp only [hp, hq, hr, hsym01]
      nlinarith [this]
    set g : ℂ → ℝ := fun τ => (p τ * r τ - q τ ^ 2) / (p τ + r τ) with hg
    have hg0 : 0 < g τ₀ := div_pos hdet0 (add_pos hp0 hr0)
    have hpc : ContinuousAt p τ₀ := hcont 0 0
    have hrc : ContinuousAt r τ₀ := hcont 1 1
    have hqc : ContinuousAt q τ₀ := ((hcont 0 1).add (hcont 1 0)).div_const 2
    have hgc : ContinuousAt g τ₀ :=
      ((hpc.mul hrc).sub (hqc.pow 2)).div (hpc.add hrc) (add_pos hp0 hr0).ne'
    have hev : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U ∧ 0 < p τ + r τ ∧ g τ₀ / 2 < g τ := by
      refine (show ∀ᶠ τ in 𝓝 τ₀, τ ∈ U from isOpen_U.mem_nhds hτ₀).and ((?_ : ∀ᶠ τ in 𝓝 τ₀, 0 < p τ + r τ).and ?_)
      · exact (hpc.add hrc).eventually (lt_mem_nhds (add_pos hp0 hr0))
      · exact hgc.eventually (lt_mem_nhds (half_lt_self hg0))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
    set c := g τ₀ / 2 with hcdef
    have hc : 0 < c := half_pos hg0
    have hq_ball : ∀ τ ∈ Metric.ball τ₀ ε, ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w := by
      intro τ hτ w
      obtain ⟨-, hpr, hgt⟩ := hball τ hτ
      have hl := quad_lower (p τ) (q τ) (r τ) (w 0) (w 1) hpr
      have hw : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
      calc c * (w 0 ^ 2 + w 1 ^ 2) ≤ g τ * (w 0 ^ 2 + w 1 ^ 2) :=
            mul_le_mul_of_nonneg_right hgt.le hw
        _ ≤ _ := by
          refine hl.trans (le_of_eq ?_)
          simp only [qf, hp, hq, hr]
          ring
    have hdiff : ∀ n, DifferentiableOn ℂ (thTerm m n) (Metric.ball τ₀ ε) := by
      intro n σ hσ
      have hσU : (0 : ℝ) < σ.im := (hball σ hσ).1
      have hΩ := fun i j => differentiableAt_omega hσU.ne' i j
      apply DifferentiableAt.differentiableWithinAt
      set V : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2 with hV
      set Bv : Fin 2 → ℂ := fun k => ((m.2 k : ℕ) : ℂ) with hBv
      have key : thTerm m n = fun τ => Complex.exp (Real.pi * I * (V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) +
          Real.pi * I * (V ⬝ᵥ Bv)) := rfl
      have hq : DifferentiableAt ℂ (fun τ => V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) σ := by
        simp only [dotProduct, Matrix.mulVec]
        refine DifferentiableAt.fun_sum fun i _ => ?_
        refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j _ => ?_) _
        exact (hΩ i j).mul_const _
      rw [key]
      exact ((hq.const_mul _).add_const _).cexp
    have hdon : DifferentiableOn ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ))
        (Metric.ball τ₀ ε) :=
      differentiableOn_tsum_of_summable_norm (summable_gb2 hc) hdiff Metric.isOpen_ball
        (fun n τ hτ => norm_thTerm_le hc m n τ (hq_ball τ hτ))
    exact hdon.analyticAt (Metric.ball_mem_nhds τ₀ hε)
  refine ⟨fun τ₀ hτ₀ => ?_, fun τ₀ hτ₀ => ?_⟩
  · show AnalyticAt ℂ (fun τ => ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) τ₀
    exact Finset.analyticAt_fun_sum _ (fun m _ => (hθ τ₀ hτ₀ m).pow 8)
  · show AnalyticAt ℂ (fun τ => ∏ m ∈ PkgI1.evenChars, PkgI1.thetaConst m (PkgI1.Omega τ) ^ 2) τ₀
    exact Finset.analyticAt_fun_prod _ (fun m _ => (hθ τ₀ hτ₀ m).pow 2)

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.thetaOmegaAnalytic_of

/-! ## period-map: `OmegaSiegel` proved (closed form of `Ω(τ)`)

`Ω(τ) = adj(F₀P⁻¹)E / det(F₀P⁻¹)` with `det(F₀P⁻¹) = −√2(τ−3)(τ+1)/2` and the adjugate product `Nf`
computed by `py/omega_lean.py` (entries reduced mod `√2² = 2`; the `linear_combination` coefficients
are the quotients printed there). With `τ = x + iy`, `Im Ω_ij = A_ij/|d|²` where
`A₀₀ = (y/2)((4−√2)(x²+y²) − 6√2x + 12 + 3√2)`, `A₁₁ = 2A₀₀`, and
`A₀₀A₁₁ − A₀₁² = 3y²|τ−3|²|τ+1|²`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Matrix

/-- `det(F₀(τ)P⁻¹)`. -/
def dF (τ : ℂ) : ℂ := -(√2 : ℂ) * (τ - 3) * (τ + 1) / 2

/-- `adj(F₀(τ)P⁻¹)·E(τ)`, entries reduced mod `√2² = 2`. -/
def Nf (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(√2 : ℂ) * (τ ^ 2 / 2 + τ - 3 / 2) - τ ^ 2 / 2 - 3 / 2,
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3;
     (√2 : ℂ) * (-τ ^ 2 / 2 - τ + 3 / 2) + τ ^ 2 + 3,
     (√2 : ℂ) * (τ ^ 2 + 2 * τ - 3) - τ ^ 2 - 3]

theorem adjE_eq (τ : ℂ) : adjugate (PkgI1.F0mat τ * PkgI1.Pinv) * PkgI1.Emat τ = Nf τ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, PkgI1.Pinv,
      PkgI1.Emat, latVec_apply, PkgI1.iota, PkgI1.Mi, PkgI1.Mj, PkgI1.oBasis, Nf]
  · ring
  · linear_combination (τ ^ 2 / 2 + 3 / 2) * sqrt2_sq
  · ring
  · linear_combination (-τ ^ 2 / 2 - 3 / 2) * sqrt2_sq

theorem omega_eq (τ : ℂ) (i j : Fin 2) : PkgI1.Omega τ i j = Nf τ i j / dF τ := by
  have h : PkgI1.Omega τ = (PkgI1.F0mat τ * PkgI1.Pinv)⁻¹ * PkgI1.Emat τ := rfl
  rw [h, Matrix.inv_def, Matrix.smul_mul, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul,
    adjE_eq, det_F0P, dF]
  ring

/-- `A₀₀/(y/2)`. -/
def Qf (x y : ℝ) : ℝ := (4 - √2) * (x ^ 2 + y ^ 2) - 6 * √2 * x + 12 + 3 * √2

theorem Qf_pos (x y : ℝ) : 0 < Qf x y := by
  have hs := sqrt2_sq'
  have h4 : 0 < 4 - √2 := by
    have : √2 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hid : (4 - √2) * Qf x y = ((4 - √2) * x - 3 * √2) ^ 2 + ((4 - √2) * y) ^ 2 + 24 := by
    unfold Qf; linear_combination (-12 : ℝ) * hs
  have : 0 < (4 - √2) * Qf x y := by rw [hid]; positivity
  exact pos_of_mul_pos_right this h4.le

theorem A00_eq (τ : ℂ) :
    (Nf τ 0 0).im * (dF τ).re - (Nf τ 0 0).re * (dF τ).im = τ.im / 2 * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (τ.re ^ 2 * τ.im + τ.im ^ 3 + 3 * τ.im) * sqrt2_sq'

theorem A01_eq (τ : ℂ) : (Nf τ 0 1).im * (dF τ).re - (Nf τ 0 1).re * (dF τ).im =
    τ.im * (√2 * τ.re ^ 2 + 6 * √2 * τ.re + √2 * τ.im ^ 2 - 3 * √2 - 2 * τ.re ^ 2 -
      2 * τ.im ^ 2 - 6) := by
  simp [Nf, dF, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (-τ.re ^ 2 * τ.im - τ.im ^ 3 - 3 * τ.im) * sqrt2_sq'

theorem A11_eq (τ : ℂ) :
    (Nf τ 1 1).im * (dF τ).re - (Nf τ 1 1).re * (dF τ).im = τ.im * Qf τ.re τ.im := by
  simp [Nf, dF, Qf, Complex.mul_re, Complex.mul_im, pow_two]
  linear_combination (2 * τ.re ^ 2 * τ.im + 2 * τ.im ^ 3 + 6 * τ.im) * sqrt2_sq'

theorem det_A (x y : ℝ) :
    y / 2 * Qf x y * (y * Qf x y) - y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6) * (y * (√2 * x ^ 2 + 6 * √2 * x + √2 * y ^ 2 - 3 * √2 -
      2 * x ^ 2 - 2 * y ^ 2 - 6)) =
      3 * y ^ 2 * ((x - 3) ^ 2 + y ^ 2) * ((x + 1) ^ 2 + y ^ 2) := by
  unfold Qf
  linear_combination (-x ^ 4 * y ^ 2 / 2 - 6 * x ^ 3 * y ^ 2 - x ^ 2 * y ^ 4 - 15 * x ^ 2 * y ^ 2 -
    6 * x * y ^ 4 + 18 * x * y ^ 2 - y ^ 6 / 2 + 3 * y ^ 4 - 9 * y ^ 2 / 2) * sqrt2_sq'

/-- A real symmetric `2 × 2` matrix with `M₀₀ > 0` and `det M > 0` is positive definite. -/
theorem posDef_fin_two {M : Matrix (Fin 2) (Fin 2) ℝ} (hs : M 1 0 = M 0 1) (h0 : 0 < M 0 0)
    (hd : 0 < M 0 0 * M 1 1 - M 0 1 * M 1 0) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply, hs]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    rw [hs] at hd ⊢
    by_cases h1 : v 1 = 0
    · have h0' : v 0 ≠ 0 := by
        intro h; apply hv; funext i; fin_cases i <;> simp [h, h1]
      rw [h1]
      have : 0 < v 0 * v 0 := mul_self_pos.mpr h0'
      nlinarith
    · have : 0 < v 1 * v 1 := mul_self_pos.mpr h1
      have key : M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) =
          (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 0 1) * (v 1 * v 1) := by ring
      have hpos : 0 < M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) +
          v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) := by
        rw [key]; positivity
      exact pos_of_mul_pos_right hpos h0.le

/-- **`OmegaSiegel` (proved).** -/
theorem omegaSiegel_proof : OmegaSiegel := by
  intro τ hτ
  have hne : dF τ ≠ 0 := by
    have := det_F0P_ne hτ.ne'
    rwa [det_F0P] at this
  have hn : 0 < Complex.normSq (dF τ) := Complex.normSq_pos.mpr hne
  have him : ∀ i j, (PkgI1.Omega τ i j).im =
      ((Nf τ i j).im * (dF τ).re - (Nf τ i j).re * (dF τ).im) / Complex.normSq (dF τ) := by
    intro i j
    rw [omega_eq, Complex.div_im]
    ring
  have hsym : PkgI1.Omega τ 1 0 = PkgI1.Omega τ 0 1 := by
    rw [omega_eq, omega_eq]; rfl
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hsym]
  · apply posDef_fin_two
    · simp only [Matrix.map_apply, hsym]
    · simp only [Matrix.map_apply]
      rw [him, A00_eq]
      exact div_pos (mul_pos (half_pos hτ) (Qf_pos _ _)) hn
    · simp only [Matrix.map_apply]
      rw [hsym, him 0 0, him 1 1, him 0 1, A00_eq, A11_eq, A01_eq]
      rw [div_mul_div_comm, div_mul_div_comm, ← sub_div, det_A]
      apply div_pos _ (mul_pos hn hn)
      have h3 : 0 < (τ.re - 3) ^ 2 + τ.im ^ 2 := by positivity
      have h1 : 0 < (τ.re + 1) ^ 2 + τ.im ^ 2 := by positivity
      positivity

/-- **`ThetaOmegaAnalytic` (proved).** -/
theorem thetaOmegaAnalytic_proof : ThetaOmegaAnalytic := thetaOmegaAnalytic_of omegaSiegel_proof

/-- **`HauptmodulUnique` from `S8Nonzero` and `SphereFactorAffine` (proved).** -/
theorem hauptmodulUnique_of' (hS : S8Nonzero) (hSF : SphereFactorAffine) : HauptmodulUnique :=
  hauptmodulUnique_of thetaOmegaAnalytic_proof hS hSF

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8Weight8`, `S8OrderCM3` and `ValenceBoundGammaStar`
(proved).** -/
theorem qmDenZeroCM3_of' (hS : S8Nonzero) (hW : S8Weight8) (hO : S8OrderCM3)
    (hV : ValenceBoundGammaStar) : QMDenZeroCM3 :=
  qmDenZeroCM3_of thetaOmegaAnalytic_proof hS hW hO hV

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMap.thetaOmegaAnalytic_proof
#print axioms HSyn.G0Split.FibreQM.PeriodMap.hauptmodulUnique_of'
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of'

/-! ## period-map: `S8Weight8` and `S8OrderCM3` from the exact automorphy `S8WeightExact`

`S8WeightExact` (`G8(γτ)·det γ⁴ = (cτ + d)⁸ G8(τ)` on `Γ*`, trivial multiplier; VERIFIED
numerically, `py/multiplier.py`) implies the absolute-value form `S8Weight8` (`s8Weight8_of`) and,
at the elliptic element `γ₃ = ι((1+j)/2)` fixing `i√3` with `cτ₃ + d = w = e^{iπ/3}`, the vanishing
order `S8OrderCM3` (`s8OrderCM3_of`): `G8(τ₃) = w⁸G8(τ₃)` with `w⁸ ≠ 1` gives `G8(τ₃) = 0`;
differentiating `G8 ∘ γ₃ = (cτ + d)⁸ G8` at `τ₃` gives `G8'(τ₃)(1 − w¹⁰) = 0` with `w¹⁰ = −w ≠ 1`;
so `ord_{τ₃} G8 ≥ 2`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodMap

open Complex Filter Topology
open UpperHalfPlane (num denom denom_ne_zero)

/-- **GLUE (exact automorphy of `G8 = Σθ⁸∘Ω/((τ−3)(τ+1))⁴` under `Γ*`, trivial multiplier).**
For `γ ∈ Γ*` and `τ ∈ ℍ`, `G8(γτ)·det(γ)⁴ = (cτ + d)⁸ G8(τ)`.

VERIFIED numerically (`py/multiplier.py`, `multiplier_out.txt`, mpmath 40 digits): the ratio
`G8(γτ) det γ⁴/((cτ+d)⁸ G8(τ))` is `1` (to 9-40 digits) for `γ = ι(x)`, `x = (1+j)/2, j, i+j, 3+2i,
2j+ij, 1+i+j, 2+i`, at two points each; these include the elliptic generators of orders 2, 4, 6
(`py/gen_check.py`) and the Atkin–Lehner elements of norms 2, 3, 6. Why true: for `γ ∈ Γ*` the
principally polarized QM surfaces at `τ` and `γτ` are isomorphic, so `Ω(γτ) = M_γ·Ω(τ)` with
`M_γ ∈ Sp₄(ℤ)`; Igusa's `ThetaModularity` (pkg-I1 leaf) gives
`Σθ⁸(Ω(γτ)) = det(CΩ + D)⁴ Σθ⁸(Ω(τ))`, and `det(CΩ(τ) + D) = ±(cτ + d)² dF(γτ)/(det γ · dF(τ))`
from the explicit `Ω` (finite computation per generator of `Γ*`; that the tested elements generate
`Γ*` is the presentation of the `(2,4,6)` triangle group, not checked here). Size: medium. -/
def S8WeightExact : Prop :=
  ∀ γ ∈ PkgI1.GammaStar, ∀ z : UpperHalfPlane,
    G8 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ z ^ 8 * G8 (z : ℂ)

/-- **`S8Weight8` from `S8WeightExact` (proved).** -/
theorem s8Weight8_of (h : S8WeightExact) : S8Weight8 := by
  intro γ hγ z
  have ⟨_, _, _, hdet⟩ := hγ
  have e := congrArg norm (h γ hγ z)
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hdet.le] at e
  exact e

theorem G8_analytic (hT : ThetaOmegaAnalytic) : AnalyticOnNhd ℂ G8 U := by
  intro z hz
  have hz' : (0 : ℝ) < z.im := hz
  have hdF : ((z - 3) * (z + 1)) ^ 4 ≠ 0 := by
    apply pow_ne_zero
    apply mul_ne_zero <;> intro h0 <;> have := congrArg Complex.im h0 <;> simp at this <;>
      exact hz'.ne' this
  exact (hT.1 z hz).div ((((analyticAt_id.sub analyticAt_const).mul
    (analyticAt_id.add analyticAt_const))).pow 4) hdF

/-- `𝒪` is closed under multiplication (pkg-I1's membership; the coordinates of a product are
LeafQM's `mulCoord`). -/
theorem inO_mul {a b : PkgI1.B} (ha : PkgI1.InO a) (hb : PkgI1.InO b) : PkgI1.InO (a * b) := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  refine ⟨![m 0 * n 0 + 2 * m 1 * n 1 + 2 * m 1 * n 3 - m 2 * n 2 + 2 * m 3 * n 3,
    m 0 * n 1 + m 1 * n 0 + m 1 * n 2 - m 2 * n 3 + m 3 * n 2,
    m 0 * n 2 - 2 * m 1 * n 3 + m 2 * n 0 + m 2 * n 2 + 2 * m 3 * n 1,
    m 0 * n 3 - m 1 * n 2 + m 2 * n 1 + m 2 * n 3 + m 3 * n 0], ?_⟩
  ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- `(1 − j)/2 = x₃⁻¹`. -/
def x3inv : PkgI1.B := ⟨1/2, 0, -1/2, 0⟩

theorem inO_x3inv : PkgI1.InO x3inv :=
  ⟨![1, 0, -1, 0], by ext <;> simp [x3inv, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

theorem x3_mem_gammaStar :
    glOf x3 (by rw [det_x3]; norm_num) ∈ PkgI1.GammaStar := by
  refine ⟨x3, ⟨x3inv, ?_, ?_, fun z hz => ⟨inO_mul (inO_mul inO_x3 hz) inO_x3inv,
    inO_mul (inO_mul inO_x3inv hz) inO_x3⟩⟩, rfl, ?_⟩
  · ext <;> simp [x3, x3inv] <;> norm_num
  · ext <;> simp [x3, x3inv] <;> norm_num
  · rw [coe_glOf, det_x3]; norm_num

/-- **`S8OrderCM3` from the holomorphy of the theta constants and `S8WeightExact` (proved).** -/
theorem s8OrderCM3_of (hT : ThetaOmegaAnalytic) (h : S8WeightExact) : S8OrderCM3 := by
  have hGa := G8_analytic hT
  set g := glOf x3 (by rw [det_x3]; norm_num) with hg
  have hgm : (g : Matrix (Fin 2) (Fin 2) ℝ) = !![1/2, -3/2; 1/2, 1/2] := by
    rw [hg, coe_glOf, iota_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [x3] <;> norm_num
  have hdetg : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by rw [hg, coe_glOf, det_x3]
  set dz : ℂ → ℂ := fun z => z / 2 + 1 / 2 with hdz
  set mz : ℂ → ℂ := fun z => (z / 2 - 3 / 2) / (z / 2 + 1 / 2) with hmz
  have hden : ∀ z : UpperHalfPlane, denom g z = dz z := by
    intro z; simp only [UpperHalfPlane.denom, hgm, hdz]; simp; ring
  have hsmul : ∀ z : UpperHalfPlane, ((g • z : UpperHalfPlane) : ℂ) = mz z := by
    intro z
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply, hdetg]; norm_num)]
    simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hgm, hmz]
    simp
    ring_nf
  -- the functional equation on `ℍ`
  have hFE : ∀ z : ℂ, 0 < z.im → G8 (mz z) = dz z ^ 8 * G8 z := by
    intro z hz
    have e := h g x3_mem_gammaStar ⟨z, hz⟩
    rw [hsmul, hden, hdetg] at e
    simpa using e
  set τ₃ : ℂ := (tau3 : ℂ) with hτ₃
  have hτ₃U : τ₃ ∈ U := tau3.im_pos
  have hτ₃im : (0 : ℝ) < τ₃.im := tau3.im_pos
  have hmτ : mz τ₃ = τ₃ := by
    have := hsmul tau3
    rw [cm3_tau3] at this
    exact this.symm
  set w : ℂ := dz τ₃ with hw
  have h3 : (√3 : ℂ) ^ 2 = 3 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hwv : w = 1 / 2 + (√3 : ℂ) / 2 * I := by
    simp only [hw, hdz, hτ₃, tau3]; push_cast; ring
  have hw3 : w ^ 3 = -1 := by
    rw [hwv]
    linear_combination ((√3 : ℂ) ^ 2 * (I * √3 + 3) / 8) * I_sq + (-(I * √3 + 3) / 8) * h3
  have hw2 : w ^ 2 = -1 / 2 + (√3 : ℂ) / 2 * I := by
    rw [hwv]; linear_combination ((√3 : ℂ) ^ 2 / 4) * I_sq + (-1 / 4 : ℂ) * h3
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0] at hw3; norm_num at hw3
  -- `G8(τ₃) = 0`
  have hG0 : G8 τ₃ = 0 := by
    have e := hFE τ₃ hτ₃im
    rw [hmτ] at e
    have hw8 : w ^ 8 = w ^ 2 := by
      rw [show w ^ 8 = w ^ 2 * (w ^ 3) ^ 2 by ring, hw3]; ring
    have hne : w ^ 8 - 1 ≠ 0 := by
      rw [hw8, hw2]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    have : (w ^ 8 - 1) * G8 τ₃ = 0 := by
      simp only [hw] at e ⊢; linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left hne
  -- `G8'(τ₃) = 0`
  have hGd : DifferentiableAt ℂ G8 τ₃ := (hGa τ₃ hτ₃U).differentiableAt
  have hdzd : ∀ z, HasDerivAt dz (1 / 2) z := by
    intro z
    show HasDerivAt (fun z : ℂ => z / 2 + 1 / 2) (1 / 2) z
    exact ((hasDerivAt_id' z).div_const 2).add_const (1 / 2 : ℂ)
  have hnumd : HasDerivAt (fun z : ℂ => z / 2 - 3 / 2) (1 / 2) τ₃ := by
    exact ((hasDerivAt_id' τ₃).div_const 2).sub_const (3 / 2 : ℂ)
  have hmzd : HasDerivAt mz ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) / dz τ₃ ^ 2) τ₃ :=
    hnumd.div (hdzd τ₃) hw0
  have hL : HasDerivAt (G8 ∘ mz) (deriv G8 τ₃ * ((1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) /
      dz τ₃ ^ 2)) τ₃ := by
    have hG' : HasDerivAt G8 (deriv G8 τ₃) (mz τ₃) := by rw [hmτ]; exact hGd.hasDerivAt
    exact hG'.comp τ₃ hmzd
  have hR : HasDerivAt (fun z => dz z ^ 8 * G8 z)
      ((8 : ℕ) * dz τ₃ ^ (8 - 1) * (1 / 2) * G8 τ₃ + dz τ₃ ^ 8 * deriv G8 τ₃) τ₃ :=
    ((hdzd τ₃).pow 8).mul hGd.hasDerivAt
  have hEq : (G8 ∘ mz) =ᶠ[𝓝 τ₃] (fun z => dz z ^ 8 * G8 z) := by
    filter_upwards [isOpen_U.mem_nhds hτ₃U] with z hz
    exact hFE z hz
  have hL' := hL.congr_of_eventuallyEq hEq.symm
  have huniq := hL'.unique hR
  rw [hG0, mul_zero, zero_add] at huniq
  have hnum1 : (1 / 2 * dz τ₃ - (τ₃ / 2 - 3 / 2) * (1 / 2)) = 1 := by simp only [hdz]; ring
  rw [hnum1] at huniq
  have hD0 : deriv G8 τ₃ = 0 := by
    have hw10 : w ^ 10 = -w := by
      rw [show w ^ 10 = w * (w ^ 3) ^ 3 by ring, hw3]; ring
    have e2 : deriv G8 τ₃ * (1 - w ^ 10) = 0 := by
      have : deriv G8 τ₃ = w ^ 10 * deriv G8 τ₃ := by
        have hw2ne : dz τ₃ ^ 2 ≠ 0 := pow_ne_zero 2 hw0
        calc deriv G8 τ₃
            = deriv G8 τ₃ * (1 / dz τ₃ ^ 2) * dz τ₃ ^ 2 := by
              rw [mul_assoc, one_div_mul_cancel hw2ne, mul_one]
          _ = dz τ₃ ^ 8 * deriv G8 τ₃ * dz τ₃ ^ 2 := by rw [huniq]
          _ = w ^ 10 * deriv G8 τ₃ := by simp only [hw]; ring
      linear_combination this
    rw [hw10] at e2
    have hne : (1 - -w) ≠ 0 := by
      rw [hwv]; intro h0
      have := congrArg Complex.re h0
      simp at this
      norm_num at this
    exact (mul_eq_zero.mp e2).resolve_right hne
  -- order at least 2
  show 2 ≤ analyticOrderAt G8 τ₃
  by_contra hlt
  push Not at hlt
  have hA := hGa τ₃ hτ₃U
  have hne0 : analyticOrderAt G8 τ₃ ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hA, hG0⟩
  have h1 : analyticOrderAt G8 τ₃ = 1 := by
    have h1' : analyticOrderAt G8 τ₃ ≤ 1 := by simpa using hlt
    exact le_antisymm h1' (Order.one_le_iff_ne_zero.mpr hne0)
  obtain ⟨φ, hφ, hφ0, hφe⟩ := (hA.analyticOrderAt_eq_natCast (n := 1)).mp (by exact_mod_cast h1)
  have hd1 : HasDerivAt (fun z => (z - τ₃) ^ 1 • φ z) (φ τ₃) τ₃ := by
    have := ((hasDerivAt_id' τ₃).sub_const τ₃).mul hφ.differentiableAt.hasDerivAt
    simp only [pow_one, smul_eq_mul]
    convert this using 1
    ring
  have hd2 : HasDerivAt G8 (φ τ₃) τ₃ := hd1.congr_of_eventuallyEq hφe
  exact hφ0 (hd2.deriv.symm.trans hD0)

/-- **`QMDenZeroCM3` from `S8Nonzero`, `S8WeightExact` and `ValenceBoundGammaStar` (proved).** -/
theorem qmDenZeroCM3_of'' (hS : S8Nonzero) (hW : S8WeightExact) (hV : ValenceBoundGammaStar) :
    QMDenZeroCM3 :=
  qmDenZeroCM3_of' hS (s8Weight8_of hW) (s8OrderCM3_of thetaOmegaAnalytic_proof hW) hV

end HSyn.G0Split.FibreQM.PeriodMap

end

#print axioms HSyn.G0Split.FibreQM.PeriodMap.s8Weight8_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.s8OrderCM3_of
#print axioms HSyn.G0Split.FibreQM.PeriodMap.qmDenZeroCM3_of''
/-! ## period-glue: `SphereFactorAffine` (generic complex analysis, Mathlib only)

Task period-glue, 2026-11-13. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Filter Topology Set

/-- **Descent of holomorphy along a non-locally-constant analytic map (proved).** Let `F, H` be
analytic on an open `O ⊆ ℂ`, `F` nowhere locally constant on `O`, and `G (F z) = H z` on `O`.
Then `F '' O` is open and `G` is complex differentiable on it. Proof: `F` is locally open
(open mapping), so `G` is continuous on `F '' O`; off the countable set `F '' {F' = 0}` the
inverse function theorem writes `G = H ∘ F⁻¹` locally; a function continuous on a disc and
differentiable off a countable set is analytic (`hasFPowerSeriesOnBall_of_differentiable_off_countable`). -/
theorem descent {O : Set ℂ} (hO : IsOpen O) {F H G : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F O) (hH : AnalyticOnNhd ℂ H O)
    (hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, F w = F z) (hGF : ∀ z ∈ O, G (F z) = H z) :
    IsOpen (F '' O) ∧ DifferentiableOn ℂ G (F '' O) := by
  have hloc : ∀ z ∈ O, 𝓝 (F z) ≤ map F (𝓝 z) := fun z hz =>
    (hF z hz).eventually_constant_or_nhds_le_map_nhds.resolve_left (hnc z hz)
  have hopen : IsOpen (F '' O) := by
    refine isOpen_iff_mem_nhds.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hloc z hz (image_mem_map (hO.mem_nhds hz))
  refine ⟨hopen, ?_⟩
  -- continuity of `G` on `F '' O`
  have hcont : ∀ z ∈ O, ContinuousAt G (F z) := by
    intro z hz
    have h1 : Tendsto (G ∘ F) (𝓝 z) (𝓝 (H z)) := by
      refine ((hH z hz).continuousAt.tendsto).congr' ?_
      filter_upwards [hO.mem_nhds hz] with w hw using (hGF w hw).symm
    have h2 : Tendsto G (map F (𝓝 z)) (𝓝 (H z)) := h1
    rw [ContinuousAt, hGF z hz]
    exact h2.mono_left (hloc z hz)
  -- the critical set is countable
  set Crit : Set ℂ := {z | z ∈ O ∧ deriv F z = 0} with hCrit
  have hdisc : DiscreteTopology Crit := by
    rw [discreteTopology_subtype_iff]
    intro z ⟨hzO, hz0⟩
    rw [inf_principal_eq_bot]
    rcases ((hF z hzO).deriv).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hnc z hzO
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem h (hO.mem_nhds hzO))
      have hdiff : DifferentiableOn ℂ F (Metric.ball z r) := fun w hw =>
        ((hF w (hball hw).2).differentiableAt).differentiableWithinAt
      filter_upwards [Metric.ball_mem_nhds z hr] with w hw
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected hdiff
        (fun v hv => (hball hv).1) hw (Metric.mem_ball_self hr)
    · filter_upwards [h] with w hw
      exact fun hc => hw hc.2
  have hcount : Crit.Countable :=
    (HereditarilyLindelofSpace.isLindelof Crit).countable hdisc
  -- differentiability off `F '' Crit`
  have hdiffAt : ∀ z ∈ O, deriv F z ≠ 0 → DifferentiableAt ℂ G (F z) := by
    intro z hz hne
    have hs := (hF z hz).hasStrictDerivAt
    set L := hs.localInverse F (deriv F z) z hne with hL
    have hLc : HasStrictDerivAt L (deriv F z)⁻¹ (F z) := hs.to_localInverse hne
    have hLz : L (F z) = z := (hs.eventually_left_inverse hne).self_of_nhds
    have hLt : Tendsto L (𝓝 (F z)) (𝓝 z) := by
      have := hLc.hasDerivAt.continuousAt.tendsto
      rwa [hLz] at this
    have hHL : DifferentiableAt ℂ (H ∘ L) (F z) := by
      refine DifferentiableAt.comp (F z) ?_ hLc.hasDerivAt.differentiableAt
      rw [hLz]; exact (hH z hz).differentiableAt
    refine hHL.congr_of_eventuallyEq ?_
    filter_upwards [hs.eventually_right_inverse hne, hLt (hO.mem_nhds hz)] with w hw hwO
    rw [Function.comp_apply, ← hGF _ hwO, hw]
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c hc
  set R : NNReal := ⟨ε / 2, by positivity⟩ with hR
  have hRε : (R : ℝ) < ε := show ε / 2 < ε by linarith
  have hsub : Metric.closedBall c R ⊆ F '' O := (Metric.closedBall_subset_ball hRε).trans hball
  have hps := Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable (R := R) (c := c) (hcount.image F)
    (fun w hw => by
      obtain ⟨z, hz, rfl⟩ := hsub hw
      exact (hcont z hz).continuousWithinAt)
    (fun w ⟨hw, hwc⟩ => by
      obtain ⟨z, hz, rfl⟩ := hsub (Metric.ball_subset_closedBall hw)
      exact hdiffAt z hz fun h0 => hwc ⟨z, ⟨hz, h0⟩, rfl⟩)
    (NNReal.coe_pos.mp (show (0:ℝ) < ε / 2 by linarith))
  exact hps.analyticAt.differentiableAt.differentiableWithinAt

/-- **An injective analytic map has non-zero derivative (proved).** Via `descent` applied to the
inverse `g⁻¹ ∘ g = id` and the chain rule. -/
theorem deriv_ne_zero_of_injOn {g : ℂ → ℂ} {a : ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 a)
    (hg : AnalyticOnNhd ℂ g U) (hinj : InjOn g U) : deriv g a ≠ 0 := by
  set O := interior U with hOdef
  have hO : IsOpen O := isOpen_interior
  have haO : a ∈ O := mem_interior_iff_mem_nhds.mpr hU
  have hOU : O ⊆ U := interior_subset
  set G := Function.invFunOn g O with hG
  have hGg : ∀ z ∈ O, G (g z) = z := fun z hz => (hinj.mono hOU).leftInvOn_invFunOn hz
  have hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, g w = g z := by
    intro z hz h
    obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ :=
      ((h.and (hO.mem_nhds hz)).filter_mono nhdsWithin_le_nhds |>.and
        self_mem_nhdsWithin).exists (f := 𝓝[≠] z)
    exact hw3 (hinj (hOU hw2) (hOU hz) hw1)
  obtain ⟨hopen, hdiff⟩ := descent hO (fun z hz => hg z (hOU hz)) analyticOnNhd_id hnc hGg
  have hGd : DifferentiableAt ℂ G (g a) :=
    (hdiff (g a) ⟨a, haO, rfl⟩).differentiableAt (hopen.mem_nhds ⟨a, haO, rfl⟩)
  have h1 : HasDerivAt (G ∘ g) (deriv G (g a) * deriv g a) a :=
    hGd.hasDerivAt.comp a (hg a (hOU haO)).differentiableAt.hasDerivAt
  have h2 : HasDerivAt (G ∘ g) 1 a := by
    refine (hasDerivAt_id a).congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds haO] with z hz using hGg z hz
  intro h0
  have := h1.unique h2
  rw [h0, mul_zero] at this
  exact zero_ne_one this

/-- **Linear growth forces an entire function to be affine (proved; Liouville applied to
`dslope ψ 0`).** -/
theorem affine_of_growth {ψ : ℂ → ℂ} (hψ : Differentiable ℂ ψ) {C R : ℝ} (hR : 0 < R)
    (hb : ∀ z : ℂ, R ≤ ‖z‖ → ‖ψ z‖ ≤ C * ‖z‖) : ∃ a b : ℂ, ∀ z, ψ z = a * z + b := by
  set k := dslope ψ 0 with hk
  have hkd : Differentiable ℂ k := by
    have := (differentiableOn_dslope (c := (0 : ℂ)) (s := univ) univ_mem).mpr hψ.differentiableOn
    simpa [differentiableOn_univ] using this
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hkd.continuous.continuousOn
  have hbd : Bornology.IsBounded (range k) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max M (C + ‖ψ 0‖ / R), ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ R
    · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
      have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      rw [hk, dslope_of_ne _ hz0, slope_def_field, sub_zero, norm_div]
      refine le_trans ?_ (le_max_right _ _)
      rw [div_le_iff₀ hzpos]
      calc ‖ψ z - ψ 0‖ ≤ ‖ψ z‖ + ‖ψ 0‖ := norm_sub_le _ _
        _ ≤ C * ‖z‖ + ‖ψ 0‖ * (‖z‖ / R) := by
          gcongr
          · exact hb z hz.le
          · exact le_mul_of_one_le_right (norm_nonneg _) (by rw [le_div_iff₀ hR]; linarith)
        _ = (C + ‖ψ 0‖ / R) * ‖z‖ := by ring
  refine ⟨k 0, ψ 0, fun z => ?_⟩
  have h1 := sub_smul_dslope ψ 0 z
  rw [sub_zero, smul_eq_mul, ← hk, hkd.apply_eq_apply_of_bounded hbd z 0] at h1
  linear_combination -h1

end HSyn.G0Split.FibreQM.PeriodGlue

end
/-! ## period-glue: `SphereFactorAffine` proved (Mathlib only)

Task period-glue, 2026-11-13. `PeriodMap.SphereFactorAffine` (period-map's `part_light.lean`,
unchanged) is proved outright: `sphereFactorAffine_proof`. Hence `HauptmodulUnique` follows from
`S8Nonzero` alone (`hauptmodulUnique_of_S8`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Filter Topology Set
open HSyn.G0Split.FibreQM

/-- The value in `ℂ` of a point of `P¹` (`∞ ↦ 0`). -/
def toC (p : OnePoint ℂ) : ℂ := p.elim 0 id

@[simp] theorem toC_coe (c : ℂ) : toC (c : OnePoint ℂ) = c := rfl

theorem coe_toC {p : OnePoint ℂ} (hp : p ≠ OnePoint.infty) : ((toC p : ℂ) : OnePoint ℂ) = p := by
  induction p using OnePoint.rec with
  | infty => exact absurd rfl hp
  | coe c => rfl

/-- The inversion `w ↦ 1/w` of `P¹`. -/
def pinv (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ) (fun c => if c = 0 then OnePoint.infty else ((c⁻¹ : ℂ) : OnePoint ℂ))

theorem pinv_coe (c : ℂ) :
    pinv (c : OnePoint ℂ) = if c = 0 then OnePoint.infty else ((c⁻¹ : ℂ) : OnePoint ℂ) := rfl

theorem pinv_infty : pinv OnePoint.infty = ((0 : ℂ) : OnePoint ℂ) := rfl

theorem pinv_pinv (p : OnePoint ℂ) : pinv (pinv p) = p := by
  induction p using OnePoint.rec with
  | infty => rw [pinv_infty, pinv_coe, if_pos rfl]
  | coe c =>
    by_cases hc : c = 0
    · subst hc; rw [pinv_coe, if_pos rfl, pinv_infty]
    · rw [pinv_coe, if_neg hc, pinv_coe, if_neg (inv_ne_zero hc), inv_inv]

theorem pinv_injective : Function.Injective pinv := fun p q h => by
  rw [← pinv_pinv p, h, pinv_pinv]

/-- At a point with a finite value, the analytic chart of `IsHolP1At`. -/
theorem hol_fin {f : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane} (hf : IsHolP1At f τ)
    (hτ : f τ ≠ OnePoint.infty) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = (g z : OnePoint ℂ) := by
  rcases hf with h | ⟨g, -, hg0, hg⟩
  · exact h
  · exfalso; apply hτ
    have := hg.self_of_nhds τ.im_pos
    rw [hg0, if_pos rfl] at this
    exact this

/-- At a pole, the chart `f = 1/g` of `IsHolP1At`, written with `pinv`. -/
theorem hol_pole {f : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane} (hf : IsHolP1At f τ)
    (hτ : f τ = OnePoint.infty) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = pinv (g z : OnePoint ℂ) := by
  rcases hf with ⟨g, -, hg⟩ | ⟨g, hga, hg0, hg⟩
  · exfalso
    have := hg.self_of_nhds τ.im_pos
    rw [show (⟨(τ : ℂ), τ.im_pos⟩ : UpperHalfPlane) = τ from rfl, hτ] at this
    exact OnePoint.infty_ne_coe _ this
  · exact ⟨g, hga, hg0, hg.mono fun z hz hz' => by rw [hz hz', pinv_coe]⟩

/-- **A holomorphic map `ℍ → P¹` that is onto is nowhere locally constant (proved).** The set of
points near which `f ≡ c` is open, and closed in `ℍ` by the identity theorem in both charts. -/
theorem not_locally_const {f : UpperHalfPlane → OnePoint ℂ} (hf : ∀ τ, IsHolP1At f τ)
    (hs : Function.Surjective f) (τ₀ : UpperHalfPlane) :
    ¬ ∀ᶠ z in 𝓝 (τ₀ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = f τ₀ := by
  intro h0
  set c := f τ₀ with hc
  set P : ℂ → Prop := fun w => ∀ hw : 0 < w.im, f ⟨w, hw⟩ = c with hP
  set u : Set ℂ := {z | ∀ᶠ w in 𝓝 z, P w} with hu
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hcl : closure u ∩ PeriodMap.U ⊆ u := by
    rintro z₀ ⟨hz₀c, hz₀⟩
    by_contra hnot
    have hfreq : ∃ᶠ w in 𝓝[≠] z₀, P w := by
      rw [frequently_nhdsWithin_iff]
      refine (mem_closure_iff_frequently.mp hz₀c).mono fun x hx => ⟨hx.self_of_nhds, ?_⟩
      rintro rfl; exact hnot hx
    have him : ∀ᶠ w in 𝓝[≠] z₀, 0 < w.im :=
      nhdsWithin_le_nhds ((PeriodMap.isOpen_U).mem_nhds hz₀)
    set τ₁ : UpperHalfPlane := ⟨z₀, hz₀⟩
    rcases hf τ₁ with ⟨g, hga, hg⟩ | ⟨g, hga, hg0, hg⟩
    · have hg' : ∀ᶠ w in 𝓝[≠] z₀, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ) :=
        nhdsWithin_le_nhds hg
      by_cases hci : c = OnePoint.infty
      · obtain ⟨w, hPw, hgw, hw⟩ := (hfreq.and_eventually (hg'.and him)).exists
        exact OnePoint.coe_ne_infty _ ((hgw hw).symm.trans ((hPw hw).trans hci))
      · obtain ⟨c', hc'⟩ : ∃ c' : ℂ, c = (c' : OnePoint ℂ) := ⟨toC c, (coe_toC hci).symm⟩
        have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w = c' := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          exact OnePoint.coe_injective ((hgw hw).symm.trans ((hPw hw).trans hc'))
        have hev := (hga.frequently_eq_iff_eventually_eq analyticAt_const).mp hfr
        apply hnot
        show ∀ᶠ w in 𝓝 z₀, P w
        filter_upwards [hev, hg] with w hw1 hw2 hw
        rw [hw2 hw, hw1, hc']
    · have hg' : ∀ᶠ w in 𝓝[≠] z₀, ∀ hw : 0 < w.im, f ⟨w, hw⟩ =
          if g w = 0 then OnePoint.infty else (((g w)⁻¹ : ℂ) : OnePoint ℂ) := nhdsWithin_le_nhds hg
      by_cases hci : c = OnePoint.infty
      · have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w = 0 := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          by_contra hne
          have := (hgw hw).symm.trans ((hPw hw).trans hci)
          rw [if_neg hne] at this
          exact OnePoint.coe_ne_infty _ this
        have hev := hga.frequently_zero_iff_eventually_zero.mp hfr
        apply hnot
        show ∀ᶠ w in 𝓝 z₀, P w
        filter_upwards [hev, hg] with w hw1 hw2 hw
        rw [hw2 hw, if_pos hw1, hci]
      · obtain ⟨c', hc'⟩ : ∃ c' : ℂ, c = (c' : OnePoint ℂ) := ⟨toC c, (coe_toC hci).symm⟩
        have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w ≠ 0 ∧ (g w)⁻¹ = c' := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          have := (hgw hw).symm.trans ((hPw hw).trans hc')
          by_cases hne : g w = 0
          · rw [if_pos hne] at this; exact absurd this (OnePoint.infty_ne_coe _)
          · rw [if_neg hne] at this; exact ⟨hne, OnePoint.coe_injective this⟩
        obtain ⟨w, hw0, hwc⟩ := hfr.exists
        have hc' : c' ≠ 0 := by rw [← hwc]; exact inv_ne_zero hw0
        have hfr' : ∃ᶠ w in 𝓝[≠] z₀, g w = c'⁻¹ :=
          hfr.mono fun w ⟨_, hw⟩ => by rw [← hw, inv_inv]
        have hev := (hga.frequently_eq_iff_eventually_eq analyticAt_const).mp hfr'
        have : g z₀ = c'⁻¹ := hev.self_of_nhds
        rw [show z₀ = (τ₁ : ℂ) from rfl, hg0] at this
        exact inv_ne_zero hc' this.symm
  have hsub := PeriodMap.isPreconnected_U.subset_of_closure_inter_subset huo
    ⟨τ₀, τ₀.im_pos, h0⟩ hcl
  have hall : ∀ τ : UpperHalfPlane, f τ = c := fun τ =>
    (hsub τ.im_pos).self_of_nhds τ.im_pos
  by_cases hci : c = OnePoint.infty
  · obtain ⟨τ, hτ⟩ := hs ((0 : ℂ) : OnePoint ℂ)
    exact OnePoint.coe_ne_infty _ (hτ.symm.trans ((hall τ).trans hci))
  · obtain ⟨τ, hτ⟩ := hs OnePoint.infty
    exact hci (hτ.symm.trans (hall τ)).symm

/-- `f` extended by `∞` off `ℍ`. -/
def extH (f : UpperHalfPlane → OnePoint ℂ) (z : ℂ) : OnePoint ℂ :=
  if hz : 0 < z.im then f ⟨z, hz⟩ else OnePoint.infty

theorem extH_of {f : UpperHalfPlane → OnePoint ℂ} {z : ℂ} (hz : 0 < z.im) :
    extH f z = f ⟨z, hz⟩ := dif_pos hz

/-- **`SphereFactorAffine` holds (proved).** `φ(f(τ)) := h(τ)` is a well-defined injection of `P¹`
fixing `∞`. Its finite part `ψ` is entire (`descent` in the chart of `f` at finite values), its
chart `χ(w) = 1/ψ(1/w)` at `∞` is analytic and injective near `0` (`descent` in the pole charts),
so `χ'(0) ≠ 0`, `ψ` has linear growth and is affine (`affine_of_growth`). -/
theorem sphereFactorAffine_proof : PeriodMap.SphereFactorAffine := by
  intro f h hf hh hsurj hfib ⟨τi, hfi, hhi⟩
  -- the induced map `φ` of `P¹`
  set s := Function.surjInv hsurj with hsdef
  have hfs : ∀ c, f (s c) = c := Function.surjInv_eq hsurj
  set φ : OnePoint ℂ → OnePoint ℂ := fun c => h (s c) with hφdef
  have hφ : ∀ τ, h τ = φ (f τ) := fun τ => ((hfib _ _).mp (hfs (f τ))).symm
  have hφinj : Function.Injective φ := fun c c' hcc => by
    rw [← hfs c, ← hfs c']; exact (hfib _ _).mpr hcc
  have hφi : φ OnePoint.infty = OnePoint.infty := by
    have := hφ τi; rw [hfi, hhi] at this; exact this.symm
  have hφfin : ∀ c : ℂ, φ (c : OnePoint ℂ) ≠ OnePoint.infty := fun c hc =>
    OnePoint.coe_ne_infty c (hφinj (hc.trans hφi.symm))
  set ψ : ℂ → ℂ := fun c => toC (φ c) with hψdef
  have hψφ : ∀ c : ℂ, ((ψ c : ℂ) : OnePoint ℂ) = φ c := fun c => coe_toC (hφfin c)
  have hnlc := not_locally_const hf hsurj
  -- Step 1: `ψ` is entire
  have hψd : Differentiable ℂ ψ := by
    set O : Set ℂ := {z | ∃ hz : 0 < z.im, f ⟨z, hz⟩ ≠ OnePoint.infty} with hOdef
    set F : ℂ → ℂ := fun z => toC (extH f z) with hFdef
    set H : ℂ → ℂ := fun z => toC (extH h z) with hHdef
    have hrep : ∀ z ∈ O, ∃ hz : 0 < z.im, ∃ g gh : ℂ → ℂ, AnalyticAt ℂ g z ∧ AnalyticAt ℂ gh z ∧
        (∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ)) ∧
        (∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, h ⟨w, hw⟩ = (gh w : OnePoint ℂ)) := by
      rintro z ⟨hz, hfz⟩
      obtain ⟨g, hga, hg⟩ := hol_fin (hf ⟨z, hz⟩) hfz
      have hhz : h ⟨z, hz⟩ ≠ OnePoint.infty := by
        rw [hφ, ← coe_toC hfz]; exact hφfin _
      obtain ⟨gh, hgha, hgh⟩ := hol_fin (hh ⟨z, hz⟩) hhz
      exact ⟨hz, g, gh, hga, hgha, hg, hgh⟩
    have himev : ∀ z : ℂ, 0 < z.im → ∀ᶠ w in 𝓝 z, 0 < w.im := fun z hz =>
      PeriodMap.isOpen_U.mem_nhds hz
    have hFeq : ∀ z ∈ O, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ F =ᶠ[𝓝 z] g ∧
        ∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ) := by
      intro z hzO
      obtain ⟨hz, g, -, hga, -, hg, -⟩ := hrep z hzO
      refine ⟨g, hga, ?_, hg⟩
      filter_upwards [hg, himev z hz] with w hw1 hw2
      simp only [hFdef, extH_of hw2, hw1 hw2, toC_coe]
    have hOo : IsOpen O := by
      refine isOpen_iff_mem_nhds.mpr fun z hzO => ?_
      obtain ⟨hz, g, -, -, -, hg, -⟩ := hrep z hzO
      filter_upwards [hg, himev z hz] with w hw1 hw2
      exact ⟨hw2, by rw [hw1 hw2]; exact OnePoint.coe_ne_infty _⟩
    have hFa : AnalyticOnNhd ℂ F O := fun z hzO => by
      obtain ⟨g, hga, hFg, -⟩ := hFeq z hzO
      exact hga.congr hFg.symm
    have hHa : AnalyticOnNhd ℂ H O := fun z hzO => by
      obtain ⟨hz, -, gh, -, hgha, -, hgh⟩ := hrep z hzO
      refine hgha.congr ?_
      filter_upwards [hgh, himev z hz] with w hw1 hw2
      simp only [hHdef, extH_of hw2, hw1 hw2, toC_coe]
    have hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, F w = F z := by
      intro z hzO hc
      obtain ⟨g, -, hFg, hg⟩ := hFeq z hzO
      obtain ⟨hz, -⟩ := hzO
      apply hnlc ⟨z, hz⟩
      filter_upwards [hc, hFg, hg, himev z hz] with w hw1 hw2 hw3 hw4 hw
      rw [hw3 hw, ← hw2, hw1, hFg.self_of_nhds, ← (hg.self_of_nhds hz)]
    have hGF : ∀ z ∈ O, ψ (F z) = H z := by
      rintro z ⟨hz, hfz⟩
      simp only [hψdef, hFdef, hHdef, extH_of hz, coe_toC hfz, ← hφ]
    obtain ⟨-, hd⟩ := descent hOo hFa hHa hnc hGF
    have himg : F '' O = univ := by
      refine eq_univ_of_forall fun c => ⟨s c, ⟨(s c).im_pos, ?_⟩, ?_⟩
      · rw [show (⟨((s c : UpperHalfPlane) : ℂ), (s c).im_pos⟩ : UpperHalfPlane) = s c from rfl,
          hfs]
        exact OnePoint.coe_ne_infty _
      · simp only [hFdef, extH_of (s c).im_pos]
        rw [show (⟨((s c : UpperHalfPlane) : ℂ), (s c).im_pos⟩ : UpperHalfPlane) = s c from rfl,
          hfs, toC_coe]
    rw [himg] at hd
    exact differentiableOn_univ.mp hd
  -- Step 2: the chart `χ` at `∞`
  obtain ⟨gf, hgfa, hgf0, hgf⟩ := hol_pole (hf τi) hfi
  obtain ⟨gh, hgha, hgh0, hgh⟩ := hol_pole (hh τi) hhi
  set χ : ℂ → ℂ := fun w => toC (pinv (φ (pinv (w : OnePoint ℂ)))) with hχdef
  set Q : ℂ → Prop := fun z => (0 < z.im ∧ AnalyticAt ℂ gf z ∧ AnalyticAt ℂ gh z) ∧
    (∀ hz : 0 < z.im, f ⟨z, hz⟩ = pinv (gf z : OnePoint ℂ)) ∧
    (∀ hz : 0 < z.im, h ⟨z, hz⟩ = pinv (gh z : OnePoint ℂ)) with hQ
  have hQev : ∀ᶠ z in 𝓝 (τi : ℂ), Q z := by
    filter_upwards [PeriodMap.isOpen_U.mem_nhds τi.im_pos, hgfa.eventually_analyticAt,
      hgha.eventually_analyticAt, hgf, hgh] with z h1 h2 h3 h4 h5 using ⟨⟨h1, h2, h3⟩, h4, h5⟩
  set O' : Set ℂ := interior {z | Q z} with hO'def
  have hO'o : IsOpen O' := isOpen_interior
  have hτO' : (τi : ℂ) ∈ O' := mem_interior_iff_mem_nhds.mpr hQev
  have hQO' : ∀ z ∈ O', Q z := fun z hz => interior_subset (s := {z | Q z}) hz
  have hχgf : ∀ z ∈ O', χ (gf z) = gh z := by
    intro z hz
    obtain ⟨⟨hzi, -, -⟩, h1, h2⟩ := hQO' z hz
    simp only [hχdef, ← h1 hzi, ← hφ, h2 hzi, pinv_pinv, toC_coe]
  have hnc' : ∀ z ∈ O', ¬ ∀ᶠ w in 𝓝 z, gf w = gf z := by
    intro z hz hc
    obtain ⟨⟨hzi, -, -⟩, h1, -⟩ := hQO' z hz
    apply hnlc ⟨z, hzi⟩
    filter_upwards [hc, hO'o.mem_nhds hz] with w hw1 hw2 hw
    rw [(hQO' w hw2).2.1 hw, hw1, ← h1 hzi]
  obtain ⟨hVo, hχd⟩ := descent hO'o (fun z hz => (hQO' z hz).1.2.1)
    (fun z hz => (hQO' z hz).1.2.2) hnc' hχgf
  set V := gf '' O' with hVdef
  have h0V : (0 : ℂ) ∈ V := ⟨τi, hτO', hgf0⟩
  have hχinj : InjOn χ V := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ hzz
    rw [hχgf z hz, hχgf z' hz'] at hzz
    obtain ⟨⟨hzi, -, -⟩, h1, h2⟩ := hQO' z hz
    obtain ⟨⟨hzi', -, -⟩, h1', h2'⟩ := hQO' z' hz'
    have hhz : h ⟨z, hzi⟩ = h ⟨z', hzi'⟩ := by rw [h2, h2', hzz]
    have hfz := (hfib _ _).mpr hhz
    rw [h1, h1'] at hfz
    exact OnePoint.coe_injective (pinv_injective hfz)
  have hχ0 : χ 0 = 0 := by
    have := hχgf _ hτO'; rw [hgf0, hgh0] at this; exact this
  have hd0 : deriv χ 0 ≠ 0 :=
    deriv_ne_zero_of_injOn (hVo.mem_nhds h0V) (hχd.analyticOnNhd hVo) hχinj
  have hχψ : ∀ w ∈ V, w ≠ 0 → ψ w⁻¹ ≠ 0 ∧ χ w = (ψ w⁻¹)⁻¹ := by
    intro w hw hw0
    have hχw : χ w = toC (pinv (ψ w⁻¹ : OnePoint ℂ)) := by
      simp only [hχdef, pinv_coe, if_neg hw0, hψφ]
    by_cases hψ0 : ψ w⁻¹ = 0
    · exfalso
      rw [hψ0, pinv_coe, if_pos rfl] at hχw
      exact hw0 (hχinj hw h0V (hχw.trans hχ0.symm))
    · refine ⟨hψ0, ?_⟩
      rw [hχw, pinv_coe, if_neg hψ0, toC_coe]
  -- Step 3: linear growth of `ψ`
  set d := deriv χ 0 with hd
  have hder : HasDerivAt χ d 0 :=
    ((hχd 0 h0V).differentiableAt (hVo.mem_nhds h0V)).hasDerivAt
  have hsl := hasDerivAt_iff_tendsto_slope.mp hder
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ V ∧ ‖slope χ 0 w - d‖ < ‖d‖ / 2 :=
    (show ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ V from nhdsWithin_le_nhds (hVo.mem_nhds h0V)).and
      ((hsl.eventually (Metric.ball_mem_nhds d (half_pos hdpos))).mono fun w hw => by
        rwa [dist_eq_norm] at hw)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεP⟩ := hev
  have hlow : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε → w ∈ V ∧ ‖d‖ / 2 * ‖w‖ ≤ ‖χ w‖ := by
    intro w hw0 hwε
    obtain ⟨hwV, hws⟩ := hεP (by simpa using hwε) hw0
    refine ⟨hwV, ?_⟩
    rw [slope_def_field, hχ0, sub_zero, sub_zero] at hws
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have h1 : ‖d‖ - ‖d‖ / 2 ≤ ‖χ w / w‖ := by
      have := norm_sub_norm_le d (χ w / w)
      rw [norm_sub_rev] at this
      linarith
    rw [norm_div, le_div_iff₀ hwpos] at h1
    linarith
  obtain ⟨a, b, hab⟩ := affine_of_growth hψd (C := 2 / ‖d‖) (R := 2 / ε) (by positivity)
    (fun z hz => by
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
      have hwε : ‖z⁻¹‖ < ε := by
        rw [norm_inv]
        have : 2 / ε ≤ ‖z‖ := hz
        rw [div_le_iff₀ hε] at this
        rw [inv_lt_iff_one_lt_mul₀ hzpos]
        nlinarith
      obtain ⟨hwV, hwl⟩ := hlow z⁻¹ (inv_ne_zero hz0) hwε
      obtain ⟨-, hχw⟩ := hχψ z⁻¹ hwV (inv_ne_zero hz0)
      rw [inv_inv] at hχw
      rw [hχw, norm_inv, norm_inv] at hwl
      have hψpos : 0 < ‖ψ z‖ := by
        rcases (norm_nonneg (ψ z)).lt_or_eq with h' | h'
        · exact h'
        · rw [← h', inv_zero] at hwl
          have : 0 < ‖d‖ / 2 * ‖z‖⁻¹ := by positivity
          linarith
      rw [le_inv_comm₀ (by positivity) hψpos] at hwl
      calc ‖ψ z‖ ≤ (‖d‖ / 2 * ‖z‖⁻¹)⁻¹ := hwl
        _ = 2 / ‖d‖ * ‖z‖ := by field_simp)
  -- Step 4: conclusion
  have ha : a ≠ 0 := by
    rintro rfl
    have h01 : φ ((0 : ℂ) : OnePoint ℂ) = φ ((1 : ℂ) : OnePoint ℂ) := by
      rw [← hψφ, ← hψφ, hab, hab]; simp
    exact one_ne_zero (OnePoint.coe_injective (hφinj h01)).symm
  refine ⟨a, b, ha, fun τ => ?_⟩
  rw [hφ τ]
  induction f τ using OnePoint.rec with
  | infty => rw [hφi]; rfl
  | coe c => rw [← hψφ, hab]; rfl

/-- **`HauptmodulUnique` from `S8Nonzero` alone (proved).** -/
theorem hauptmodulUnique_of_S8 (hS : PeriodMap.S8Nonzero) : HauptmodulUnique :=
  PeriodMap.hauptmodulUnique_of' hS sphereFactorAffine_proof

end HSyn.G0Split.FibreQM.PeriodGlue

end

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.descent
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.deriv_ne_zero_of_injOn
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.affine_of_growth
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.hauptmodulUnique_of_S8
