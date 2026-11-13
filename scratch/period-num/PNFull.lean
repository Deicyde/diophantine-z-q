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

/-! ## period-num: `S8Nonzero` proved

`Ω(√2 + i) = [[(−1+i)/2, 1], [1, −1+i]]` (exact; `omega_s2I`). Because the off-diagonal entry is `1`,
each genus-2 theta constant splits as a product of two genus-1 theta constants with characteristics
(`thetaConst_split`), and
`Σ_{m even} θ_m⁸(Ω(√2+i)) = (Z₀⁸ + Z₁⁸ + T⁸)(P₀⁸ + P₁⁸ + Q⁸)` (`thetaSum8_s2I`), with
`Z_b = ϑ[0,b]((−1+i)/2)`, `T = ϑ[1,0]((−1+i)/2)`, `P_b = ϑ[0,b](−1+i)`, `Q = ϑ[1,0](−1+i)`.
* `P₀, P₁` are real and `Q = e^{−iπ/4}R` with `R > 0`, so the second factor is a positive real.
* `T = e^{−iπ/8}C` with `C` real, so `Re T⁸ = −C⁸ ≤ 0`; `Z₀ = 1 − 2ie^{−π/2} + O(e^{−2π})` and
  `Z₁ = 1 + 2ie^{−π/2} + O(e^{−2π})`, so `Re Z_b⁸ < 0` (certified with `e^{π/2} ∈ (4.41, 7.39)`,
  `e^{−π} < 1/20`, tail `≤ e^{−2π}/(1−e^{−π}) < 1/380`). Hence `Re` of the first factor is `< 0`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodNum

open Complex
open scoped Real
open HSyn.G0Split.FibreQM.PeriodMap

/-! ### `Ω(√2 + i)` -/

/-- The period matrix at `√2 + i`. -/
def Om0 : Matrix (Fin 2) (Fin 2) ℂ := !![(-1 + I) / 2, 1; 1, -1 + I]

theorem dF_s2I_ne : dF ((√2 : ℂ) + I) ≠ 0 := by
  have h2 : (√2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  have ha : (√2 : ℂ) + I - 3 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  have hb : (√2 : ℂ) + I + 1 ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  simp only [dF]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) ha) hb) two_ne_zero

theorem omega_s2I : PkgI1.Omega ((√2 : ℂ) + I) = Om0 := by
  ext i j
  rw [omega_eq, div_eq_iff dF_s2I_ne]
  fin_cases i <;> fin_cases j <;> simp only [Nf, Om0, dF, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  · linear_combination (1 + 1 / 2 * I * I + 1 / 4 * (√2 : ℂ) + 1 / 4 * (√2 : ℂ) * I) * sqrt2_sq +
      (1 / 2 - 1 / 4 * (√2 : ℂ) + 1 / 4 * (√2 : ℂ) * I) * I_sq
  · linear_combination (-1 : ℂ) * sqrt2_sq + (1 : ℂ) * I_sq
  · linear_combination (-1 : ℂ) * sqrt2_sq + (1 : ℂ) * I_sq
  · linear_combination (2 + I * I + 1 / 2 * (√2 : ℂ) + 1 / 2 * (√2 : ℂ) * I) * sqrt2_sq +
      (1 - 1 / 2 * (√2 : ℂ) + 1 / 2 * (√2 : ℂ) * I) * I_sq

/-! ### Genus-one theta constants with characteristics -/

/-- The term `exp(πi(n + a/2)²w + πi(n + a/2)b)`. -/
def thT (a b w : ℂ) (n : ℤ) : ℂ :=
  cexp (π * I * ((n : ℂ) + a / 2) ^ 2 * w + π * I * ((n : ℂ) + a / 2) * b)

/-- `ϑ[a, b](w) = Σ_n exp(πi(n + a/2)²w + πi(n + a/2)b)`. -/
def th1 (a b w : ℂ) : ℂ := ∑' n : ℤ, thT a b w n

theorem thT_eq (a b w : ℂ) (n : ℤ) :
    thT a b w n = cexp (π * I * a ^ 2 * w / 4 + π * I * a * b / 2) *
      jacobiTheta₂_term n (a * w / 2 + b / 2) w := by
  rw [thT, jacobiTheta₂_term, ← Complex.exp_add]; congr 1; ring

theorem summable_norm_thT (a b : ℂ) {w : ℂ} (hw : 0 < w.im) :
    Summable (fun n => ‖thT a b w n‖) := by
  have h := (summable_jacobiTheta₂_term_iff (a * w / 2 + b / 2) w).mpr hw
  have h2 : Summable (fun n => thT a b w n) := by
    simp_rw [thT_eq]; exact h.mul_left _
  exact summable_norm_iff.mpr h2

theorem exp_add_int_mul (z : ℂ) (k : ℤ) : cexp (z + k * (2 * π * I)) = cexp z := by
  rw [Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]

/-! ### Splitting the genus-2 theta constants at `[[w₁, 1], [1, w₂]]` -/

theorem thetaConst_split (m : PkgI1.Char2) (w1 w2 : ℂ) (h1 : 0 < w1.im) (h2 : 0 < w2.im) :
    PkgI1.thetaConst m !![w1, 1; 1, w2] =
      cexp (-(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) *
        (th1 ((m.1 0 : ℕ) : ℂ) (((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ)) w1 *
         th1 ((m.1 1 : ℕ) : ℂ) (((m.2 1 : ℕ) : ℂ) + ((m.1 0 : ℕ) : ℂ)) w2) := by
  set a0 : ℂ := ((m.1 0 : ℕ) : ℂ)
  set a1 : ℂ := ((m.1 1 : ℕ) : ℂ)
  set b0 : ℂ := ((m.2 0 : ℕ) : ℂ)
  set b1 : ℂ := ((m.2 1 : ℕ) : ℂ)
  set c : ℂ := cexp (-(π * I * a0 * a1 / 2))
  set f1 : ℤ → ℂ := thT a0 (b0 + a1) w1
  set f2 : ℤ → ℂ := thT a1 (b1 + a0) w2
  have e1 : PkgI1.thetaConst m !![w1, 1; 1, w2] = ∑' n : Fin 2 → ℤ, c * (f1 (n 0) * f2 (n 1)) := by
    unfold PkgI1.thetaConst
    refine tsum_congr fun n => ?_
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      f1, f2, c, thT, ← Complex.exp_add]
    conv_rhs => rw [← exp_add_int_mul _ (n 0 * n 1)]
    congr 1
    simp only [a0, a1, b0, b1]
    push_cast
    ring
  have e2 : ∑' n : Fin 2 → ℤ, f1 (n 0) * f2 (n 1) = ∑' p : ℤ × ℤ, f1 p.1 * f2 p.2 := by
    rw [← (finTwoArrowEquiv ℤ).symm.tsum_eq]
    rfl
  rw [e1, tsum_mul_left, e2,
    ← tsum_mul_tsum_of_summable_norm (summable_norm_thT _ _ h1) (summable_norm_thT _ _ h2)]
  rfl

/-! ### Elementary identities -/

theorem th1_zero_two (w : ℂ) : th1 0 2 w = th1 0 0 w := by
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [thT]
  conv_rhs => rw [← exp_add_int_mul _ n]
  congr 1
  ring

theorem th1_one_two (w : ℂ) : th1 1 2 w = -th1 1 0 w := by
  unfold th1
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  simp only [thT]
  have : π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 2 =
      (π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 0 + π * I) +
        (n : ℂ) * (2 * π * I) := by ring
  rw [this, exp_add_int_mul, Complex.exp_add, exp_pi_mul_I]
  ring

theorem th1_one_one (w : ℂ) : th1 1 1 w = 0 := by
  have h : th1 1 1 w = -th1 1 1 w := by
    unfold th1
    rw [← tsum_neg, ← (Equiv.subLeft (-1 : ℤ)).tsum_eq]
    refine tsum_congr fun n => ?_
    simp only [thT, Equiv.subLeft_apply]
    have : π * I * ((((-1 - n : ℤ)) : ℂ) + 1 / 2) ^ 2 * w + π * I * ((((-1 - n : ℤ)) : ℂ) + 1 / 2) * 1
        = (π * I * ((n : ℂ) + 1 / 2) ^ 2 * w + π * I * ((n : ℂ) + 1 / 2) * 1 + π * I) +
          ((-n - 1 : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
    rw [this, exp_add_int_mul, Complex.exp_add, exp_pi_mul_I]
    ring
  have : (2 : ℂ) * th1 1 1 w = 0 := by linear_combination h
  simpa using this

/-! ### Real and positive parts -/

theorem tsum_ofReal_of_im {f : ℤ → ℂ} (h : ∀ n, (f n).im = 0) :
    ∑' n, f n = ((∑' n, (f n).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  exact Complex.ext (by simp) (by simp [h n])

theorem exp_real_add_int_pi (r : ℝ) (k : ℤ) :
    cexp ((r : ℂ) + k * (π * I)) = ((Real.exp r * (-1 : ℝ) ^ k : ℝ) : ℂ) := by
  rw [Complex.exp_add, Complex.exp_int_mul, exp_pi_mul_I, ← Complex.ofReal_exp]
  push_cast
  rfl

theorem im_exp_real_add_int_pi (r : ℝ) (k : ℤ) : (cexp ((r : ℂ) + k * (π * I))).im = 0 := by
  rw [exp_real_add_int_pi, Complex.ofReal_im]

theorem norm_exp_pi_I_div (c : ℕ) : ‖cexp (π * I / c)‖ = 1 := by
  rw [show (π * I / c : ℂ) = ((π / c : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `ϑ[0, b](−1 + i)` is real. -/
theorem P_real (b : ℤ) : ∃ p : ℝ, th1 0 b (-1 + I) = p := by
  refine ⟨_, tsum_ofReal_of_im fun n => ?_⟩
  have : thT 0 b (-1 + I) n = cexp (((-π * (n : ℝ) ^ 2 : ℝ) : ℂ) + ((n * b - n ^ 2 : ℤ) : ℂ) * (π * I)) := by
    rw [thT]; congr 1; push_cast; ring_nf; rw [I_sq]; ring
  rw [this]
  exact im_exp_real_add_int_pi _ _

/-- `ϑ[1, 0](−1 + i) = e^{−iπ/4} R` with `R > 0`. -/
theorem Q_eq : ∃ R : ℝ, 0 < R ∧ th1 1 0 (-1 + I) = cexp (-(π * I / 4)) * R := by
  set g : ℤ → ℂ := fun n => cexp (π * I / 4) * thT 1 0 (-1 + I) n with hg
  have hk : ∀ n : ℤ, ∃ k : ℤ, g n =
      cexp (((-π * ((n : ℝ) + 1 / 2) ^ 2 : ℝ) : ℂ) + ((-(2 * k)) : ℤ) * (π * I)) := by
    intro n
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    refine ⟨k, ?_⟩
    have hk' : ((n : ℂ) * ((n : ℂ) + 1)) = (k : ℂ) + k := by exact_mod_cast hk
    simp only [hg, thT, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(π : ℂ) * I) * hk' + ((π : ℂ) * ((n : ℂ) + 1 / 2) ^ 2) * I_sq
  have him : ∀ n, (g n).im = 0 := fun n => by
    obtain ⟨k, hk⟩ := hk n; rw [hk]; exact im_exp_real_add_int_pi _ _
  have hre : ∀ n, 0 < (g n).re := fun n => by
    obtain ⟨k, hk⟩ := hk n
    rw [hk, exp_real_add_int_pi, Complex.ofReal_re]
    have : ((-1 : ℝ) ^ (-(2 * k))) = 1 := by
      rw [zpow_neg, zpow_mul]; simp
    rw [this, mul_one]; exact Real.exp_pos _
  have hsum : Summable fun n => (g n).re := by
    refine Summable.of_norm_bounded (summable_norm_thT 1 0 (w := -1 + I) (by simp)) fun n => ?_
    rw [Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [hg, norm_mul]
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, norm_exp_pi_I_div, one_mul]
  refine ⟨∑' n, (g n).re, hsum.tsum_pos (fun n => (hre n).le) 0 (hre 0), ?_⟩
  rw [← tsum_ofReal_of_im him, ← tsum_mul_left]
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [hg, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- `ϑ[1, 0]((−1 + i)/2) = e^{−iπ/8} C` with `C` real. -/
theorem T_eq : ∃ C : ℝ, th1 1 0 ((-1 + I) / 2) = cexp (-(π * I / 8)) * C := by
  set g : ℤ → ℂ := fun n => cexp (π * I / 8) * thT 1 0 ((-1 + I) / 2) n with hg
  have hk : ∀ n : ℤ, ∃ k : ℤ, g n =
      cexp (((-π * ((n : ℝ) + 1 / 2) ^ 2 / 2 : ℝ) : ℂ) + ((-k) : ℤ) * (π * I)) := by
    intro n
    obtain ⟨k, hk⟩ := Int.even_mul_succ_self n
    refine ⟨k, ?_⟩
    have hk' : ((n : ℂ) * ((n : ℂ) + 1)) = (k : ℂ) + k := by exact_mod_cast hk
    simp only [hg, thT, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(π : ℂ) * I / 2) * hk' + ((π : ℂ) * ((n : ℂ) + 1 / 2) ^ 2 / 2) * I_sq
  have him : ∀ n, (g n).im = 0 := fun n => by
    obtain ⟨k, hk⟩ := hk n; rw [hk]; exact im_exp_real_add_int_pi _ _
  refine ⟨∑' n, (g n).re, ?_⟩
  rw [← tsum_ofReal_of_im him, ← tsum_mul_left]
  unfold th1
  refine tsum_congr fun n => ?_
  simp only [hg, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-! ### `Z_b` via `jacobiTheta`, and the certified numerics -/

theorem th1_zero_zero (w : ℂ) : th1 0 0 w = jacobiTheta w := by
  unfold th1 jacobiTheta
  refine tsum_congr fun n => ?_
  simp [thT]

theorem th1_zero_one (w : ℂ) : th1 0 1 w = jacobiTheta (w + 1) := by
  unfold th1 jacobiTheta
  refine tsum_congr fun n => ?_
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self n
  have hk' : ((n : ℂ) * ((n : ℂ) - 1)) = (k : ℂ) + k := by exact_mod_cast hk
  simp only [thT]
  rw [← exp_add_int_mul _ k]
  congr 1
  linear_combination (-(π : ℂ) * I) * hk'

theorem jt_approx {τ : ℂ} (hτ : τ.im = 1 / 2) : ∃ R : ℂ,
    jacobiTheta τ = 1 + 2 * cexp (π * I * τ) + 2 * R ∧
      ‖R‖ ≤ Real.exp (-π) ^ 2 / (1 - Real.exp (-π)) := by
  have hτ' : 0 < τ.im := by rw [hτ]; norm_num
  set f : ℕ → ℂ := fun n => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) with hf
  set r := Real.exp (-π) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hb : ∀ n : ℕ, ‖f (n + 1)‖ ≤ r ^ 2 * r ^ n := by
    intro n
    simp only [hf]
    rw [Complex.norm_exp]
    have hre : (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * τ).re = -π * ((n : ℝ) + 2) ^ 2 * τ.im := by
      rw [show (π * I * (((n + 1 : ℕ) : ℂ) + 1) ^ 2 * τ : ℂ) =
          ((π * ((n : ℝ) + 2) ^ 2 : ℝ) : ℂ) * (τ * I) by push_cast; ring,
        Complex.re_ofReal_mul, Complex.mul_I_re]
      ring
    rw [hre, hτ, ← pow_add, hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    push_cast
    have : 0 ≤ π * (((n : ℝ) + 2) * n) := by positivity
    nlinarith [Real.pi_pos]
  have hgeo : Summable (fun n : ℕ => r ^ 2 * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hs : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hgeo
  have hsf : Summable f := (summable_nat_add_iff 1).mp hs.of_norm
  refine ⟨∑' n : ℕ, f (n + 1), ?_, ?_⟩
  · rw [jacobiTheta_eq_tsum_nat hτ', hsf.tsum_eq_zero_add]
    simp only [hf, Nat.cast_zero, zero_add, one_pow, mul_one]
    push_cast
    ring
  · calc ‖∑' n : ℕ, f (n + 1)‖ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ, r ^ 2 * r ^ n := hs.tsum_le_tsum hb hgeo
      _ = r ^ 2 / (1 - r) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

theorem exp_bounds : 0.135 < Real.exp (-π / 2) ∧ Real.exp (-π / 2) < 0.227 ∧
    Real.exp (-π) ^ 2 / (1 - Real.exp (-π)) ≤ 1 / 380 := by
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hp1 := Real.pi_gt_three
  have hp2 := Real.pi_lt_four
  have h2 : Real.exp (π / 2) < Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  have hhalf : (1.625 : ℝ) ≤ Real.exp (1 / 2) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 1 / 2) (by norm_num)
    norm_num at this ⊢; linarith
  have h3 : Real.exp 1 * Real.exp (1 / 2) < Real.exp (π / 2) := by
    rw [← Real.exp_add]; exact Real.exp_lt_exp.mpr (by linarith)
  have h4 : Real.exp 1 ^ 3 < Real.exp π := by
    rw [← Real.exp_nat_mul]; exact Real.exp_lt_exp.mpr (by push_cast; linarith)
  have hpos := Real.exp_pos (π / 2)
  have hpos' := Real.exp_pos π
  rw [show -π / 2 = -(π / 2) by ring, Real.exp_neg]
  refine ⟨?_, ?_, ?_⟩
  · rw [lt_inv_comm₀ (by norm_num) hpos]; nlinarith
  · rw [inv_lt_comm₀ hpos (by norm_num)]; nlinarith
  · rw [Real.exp_neg]
    have h20 : 20 < Real.exp π := by nlinarith
    have hi : (Real.exp π)⁻¹ < 1 / 20 := by rw [inv_lt_comm₀ hpos' (by norm_num)]; linarith
    have hi0 : 0 < (Real.exp π)⁻¹ := inv_pos.mpr hpos'
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith

theorem re_pow8 (x y : ℝ) : (((x : ℂ) + y * I) ^ 8).re =
    x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 := by
  simp [pow_succ, Complex.mul_re, Complex.mul_im]
  ring

theorem re_pow8_neg (x y : ℝ) (hx : |x - 1| ≤ 1 / 150) (hy1 : 0.26 ≤ |y|) (hy2 : |y| ≤ 0.46) :
    (((x : ℂ) + y * I) ^ 8).re < 0 := by
  rw [re_pow8]
  have hx' := abs_le.mp hx
  have hy0 : 0 ≤ |y| := abs_nonneg y
  set s := x ^ 2 with hs
  set t := y ^ 2 with ht
  have ht' : t = |y| ^ 2 := by rw [ht, sq_abs]
  have hs0 : 0.9867 ≤ s := by rw [hs]; nlinarith
  have hs1 : s ≤ 1.0134 := by rw [hs]; nlinarith
  have ht0 : 0.0676 ≤ t := by rw [ht']; nlinarith
  have ht1 : t ≤ 0.2116 := by rw [ht']; nlinarith
  have hE : s ^ 2 - 28 * s * t + 70 * t ^ 2 < 0 := by
    have h1 : 0 ≤ (t - 0.0676) * (0.2116 - t) := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (t - 0.0676) * (s - 0.9867) := mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (s - 0.9867) * (1.0134 - s) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hF : t ^ 3 * (t - 28 * s) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos (by linarith) 3) (by linarith)
  have hG : s ^ 2 * (s ^ 2 - 28 * s * t + 70 * t ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (pow_pos (by linarith) 2) hE
  have : x ^ 8 - 28 * x ^ 6 * y ^ 2 + 70 * x ^ 4 * y ^ 4 - 28 * x ^ 2 * y ^ 6 + y ^ 8 =
      s ^ 2 * (s ^ 2 - 28 * s * t + 70 * t ^ 2) + t ^ 3 * (t - 28 * s) := by
    rw [hs, ht]; ring
  rw [this]; linarith

theorem exp_w1 : cexp (π * I * ((-1 + I) / 2)) = -((Real.exp (-π / 2) : ℂ) * I) := by
  have hz : (π * I * ((-1 + I) / 2) : ℂ) = ((-π / 2 : ℝ) : ℂ) + ((-π / 2 : ℝ) : ℂ) * I := by
    push_cast; linear_combination ((π : ℂ) / 2) * I_sq
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, show -π / 2 = -(π / 2) by ring, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem exp_w1' : cexp (π * I * ((-1 + I) / 2 + 1)) = (Real.exp (-π / 2) : ℂ) * I := by
  have hz : (π * I * ((-1 + I) / 2 + 1) : ℂ) = ((-π / 2 : ℝ) : ℂ) + ((π / 2 : ℝ) : ℂ) * I := by
    push_cast; linear_combination ((π : ℂ) / 2) * I_sq
  rw [hz, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

/-- `Re ϑ(τ)⁸ < 0` for `jacobiTheta τ = 1 + 2(±iq) + 2R`. -/
theorem re_jt_pow8_neg {τ : ℂ} (hτ : τ.im = 1 / 2) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hc : cexp (π * I * τ) = σ * ((Real.exp (-π / 2) : ℂ) * I)) : (jacobiTheta τ ^ 8).re < 0 := by
  obtain ⟨R, hR, hRb⟩ := jt_approx hτ
  obtain ⟨hq1, hq2, hε⟩ := exp_bounds
  set q := Real.exp (-π / 2)
  have hRn : ‖R‖ ≤ 1 / 380 := hRb.trans hε
  have hre := (abs_re_le_norm R).trans hRn
  have him := (abs_im_le_norm R).trans hRn
  have hZ : jacobiTheta τ = ((1 + 2 * R.re : ℝ) : ℂ) + ((2 * σ * q + 2 * R.im : ℝ) : ℂ) * I := by
    rw [hR, hc]
    apply Complex.ext <;> simp
    ring
  rw [hZ]
  apply re_pow8_neg
  · rw [abs_le] at hre ⊢; constructor <;> linarith
  · rw [abs_le] at him
    rcases hσ with h | h <;> subst h
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_le] at him ⊢
    rcases hσ with h | h <;> subst h <;> constructor <;> linarith

theorem re_Z0 : (th1 0 0 ((-1 + I) / 2) ^ 8).re < 0 := by
  rw [th1_zero_zero]
  exact re_jt_pow8_neg (by simp) (-1) (Or.inr rfl) (by rw [exp_w1]; push_cast; ring)

theorem re_Z1 : (th1 0 1 ((-1 + I) / 2) ^ 8).re < 0 := by
  rw [th1_zero_one]
  exact re_jt_pow8_neg (by simp) 1 (Or.inl rfl) (by rw [exp_w1']; push_cast; ring)

/-! ### Assembly -/

theorem evenChars_eq : PkgI1.evenChars =
    {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 0], ![1, 1]),
     (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]),
     (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by
  decide

theorem c8_eq_one (m : PkgI1.Char2) :
    cexp (-(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2)) ^ 8 = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show ((8 : ℕ) : ℂ) * -(π * I * ((m.1 0 : ℕ) : ℂ) * ((m.1 1 : ℕ) : ℂ) / 2) =
      ((-2 * ((m.1 0 : ℕ) : ℤ) * ((m.1 1 : ℕ) : ℤ) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
  exact exp_int_mul_two_pi_mul_I _

theorem thetaSum8_s2I : PkgI1.thetaSum8 Om0 =
    (th1 0 0 ((-1 + I) / 2) ^ 8 + th1 0 1 ((-1 + I) / 2) ^ 8 + th1 1 0 ((-1 + I) / 2) ^ 8) *
      (th1 0 0 (-1 + I) ^ 8 + th1 0 1 (-1 + I) ^ 8 + th1 1 0 (-1 + I) ^ 8) := by
  have h1 : 0 < ((-1 + I) / 2 : ℂ).im := by simp
  have h2 : 0 < ((-1 + I) : ℂ).im := by simp
  have hs : ∀ m : PkgI1.Char2, PkgI1.thetaConst m Om0 ^ 8 =
      th1 ((m.1 0 : ℕ) : ℂ) (((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ)) ((-1 + I) / 2) ^ 8 *
        th1 ((m.1 1 : ℕ) : ℂ) (((m.2 1 : ℕ) : ℂ) + ((m.1 0 : ℕ) : ℂ)) (-1 + I) ^ 8 := by
    intro m
    rw [Om0, thetaConst_split m _ _ h1 h2, mul_pow, mul_pow, c8_eq_one, one_mul]
  unfold PkgI1.thetaSum8
  rw [Finset.sum_congr rfl fun m _ => hs m, evenChars_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, add_zero, zero_add,
    one_add_one_eq_two, th1_zero_two, th1_one_two, th1_one_one]
  ring

/-- **`S8Nonzero`, proved.** -/
theorem s8Nonzero_proof : S8Nonzero := by
  unfold S8Nonzero
  rw [omega_s2I, thetaSum8_s2I]
  apply mul_ne_zero
  · intro h
    have hre := congrArg Complex.re h
    obtain ⟨C, hC⟩ := T_eq
    have hT : (th1 1 0 ((-1 + I) / 2) ^ 8).re = -C ^ 8 := by
      rw [hC, mul_pow, ← Complex.exp_nat_mul,
        show ((8 : ℕ) : ℂ) * -(π * I / 8) = ((-1 : ℤ) : ℂ) * (π * I) by push_cast; ring,
        Complex.exp_int_mul, exp_pi_mul_I]
      norm_num
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    simp only [Complex.add_re, Complex.zero_re, hT] at hre
    have := re_Z0
    have := re_Z1
    have : 0 ≤ C ^ 8 := by positivity
    linarith
  · obtain ⟨p0, hp0⟩ := P_real 0
    obtain ⟨p1, hp1⟩ := P_real 1
    obtain ⟨R, hR, hQ⟩ := Q_eq
    push_cast at hp0 hp1
    rw [hp0, hp1, hQ, mul_pow, ← Complex.exp_nat_mul,
      show ((8 : ℕ) : ℂ) * -(π * I / 4) = ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I, one_mul]
    have : (0 : ℝ) < p0 ^ 8 + p1 ^ 8 + R ^ 8 := by positivity
    exact_mod_cast this.ne'

end HSyn.G0Split.FibreQM.PeriodNum

end

#print axioms HSyn.G0Split.FibreQM.PeriodNum.s8Nonzero_proof

/-! ## period-num: `S8WeightExact` from `ThetaModularity` and `NormalizerDecomp`

For `γ = ι(x) ∈ Γ*` write `x = r·w·u` (`NormalizerDecomp`: `r ∈ ℚ^×`, `w ∈ {1, i, j + ij, μ}`,
`u ∈ 𝒪^×`) and put `z = r⁻¹w⁻¹`. The map `b ↦ z b x = w⁻¹ b w u` preserves `𝒪` and the Riemann form
`E(a, b) = Trd(μ⁻¹ a b̄)` (`Bf`). The `ℂ`-linear map `Ψ = j(γ, τ)·ι(z)` carries `Λ_{γτ}` onto `Λ_τ`
(`ι(z)ι(b)ι(x)(τ, 1)ᵀ = j(γ, τ)ι(z)ι(b)(γτ, 1)ᵀ`), so in the symplectic basis `sB` of `𝒪` its matrix
`N ∈ M₄(ℤ)` satisfies `NᵀGN = G` and `Ω(γτ) = Nᵀ·Ω(τ)` (`omega_transform`), with
`det(CΩ + D) = j(γ, τ)² nrd(z) dF(γτ)/dF(τ)`. Igusa's `ThetaModularity` then gives
`G8(γτ)·det(γ)⁴ = j(γ, τ)⁸ G8(τ)` (`s8WeightExact_of`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodNum

open Complex Matrix
open HSyn.G0Split.FibreQM.PeriodMap
open UpperHalfPlane (num denom denom_ne_zero)

/-! ### Reduced norm and the Riemann form -/

/-- The reduced norm of `B = (2, −3)`. -/
def nrd (a : PkgI1.B) : ℚ := a.re ^ 2 - 2 * a.imI ^ 2 + 3 * a.imJ ^ 2 - 6 * a.imK ^ 2

theorem nrd_mul (a b : PkgI1.B) : nrd (a * b) = nrd a * nrd b := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem nrd_one : nrd 1 = 1 := by simp [nrd]

theorem det_iota_eq (a : PkgI1.B) : (PkgI1.iota a).det = (nrd a : ℝ) := by
  rw [det_iota, nrd]; push_cast; ring

/-- The Riemann form `E(a, b) = Trd(μ⁻¹ a b̄)` on `B`. -/
def Bf (a b : PkgI1.B) : ℚ := PkgI1.trd (PkgI1.muInv * a * star b)

theorem Bf_mul_right (a b u : PkgI1.B) : Bf (a * u) (b * u) = nrd u * Bf a b := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-! ### The symplectic basis `sB` of `𝒪` and coordinates -/

/-- `f₀ = −2·(1+j)/2 − (i+ij)/2`. -/
def sf0 : PkgI1.B := ⟨-1, -1/2, -1, -1/2⟩
/-- `f₁ = −(1+j)/2 − (i+ij)/2`. -/
def sf1 : PkgI1.B := ⟨-1/2, -1/2, -1/2, -1/2⟩

/-- The symplectic basis `(e₀, e₁, f₀, f₁) = (1, i, f₀, f₁)` of `𝒪` (`(f₀, f₁) = (b₂, b₃)P⁻¹`). -/
def sB : Fin 2 ⊕ Fin 2 → PkgI1.B := Sum.elim ![PkgI1.oBasis 0, PkgI1.oBasis 1] ![sf0, sf1]

/-- Coordinates in `sB`. -/
def kap (a : PkgI1.B) : Fin 2 ⊕ Fin 2 → ℚ :=
  Sum.elim ![a.re - a.imJ, a.imI - a.imK] ![2 * a.imK - 2 * a.imJ, 2 * a.imJ - 4 * a.imK]

theorem sum_kap (a : PkgI1.B) : ∑ k, kap a k • sB k = a := by
  ext <;> simp [Fintype.sum_sum_type, Fin.sum_univ_two, kap, sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem kap_int {a : PkgI1.B} (h : PkgI1.InO a) (k : Fin 2 ⊕ Fin 2) : ∃ n : ℤ, kap a k = n := by
  obtain ⟨n, rfl⟩ := h
  rcases k with k | k <;> fin_cases k
  · exact ⟨n 0, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨n 1, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨n 3 - n 2, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]; ring⟩
  · exact ⟨n 2 - 2 * n 3, by simp [kap, PkgI1.oBasis, Fin.sum_univ_four]; ring⟩

theorem kap_sB (k l : Fin 2 ⊕ Fin 2) : kap (sB k) l = if k = l then 1 else 0 := by
  rcases k with k | k <;> rcases l with l | l <;> fin_cases k <;> fin_cases l <;>
    simp [kap, sB, sf0, sf1, PkgI1.oBasis] <;> norm_num

/-- The Gram matrix of `E` in `sB`: `[[0, 1], [−1, 0]] = −J`. -/
def Gm : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ := fromBlocks 0 1 (-1) 0

theorem Bf_expand (a b : PkgI1.B) : Bf a b = ∑ l, ∑ m, kap a l * Gm l m * kap b m := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, kap, Gm, Fintype.sum_sum_type, Fin.sum_univ_two,
    QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply]
  simp
  ring

/-! ### Lattice vectors -/

theorem latVec_eq (a : PkgI1.B) (τ : ℂ) : PkgI1.latVec a τ =
    ![(((a.re : ℝ) + a.imI * √2 : ℝ) : ℂ) * τ + ((-3 * (a.imJ : ℝ) - 3 * √2 * a.imK : ℝ) : ℂ),
      (((a.imJ : ℝ) - √2 * a.imK : ℝ) : ℂ) * τ + (((a.re : ℝ) - a.imI * √2 : ℝ) : ℂ)] := by
  funext r
  rw [latVec_apply, iota_apply]
  fin_cases r <;> simp

theorem latVec_lin (c : Fin 2 ⊕ Fin 2 → ℚ) (τ : ℂ) :
    PkgI1.latVec (∑ k, c k • sB k) τ = ∑ k, ((c k : ℚ) : ℂ) • PkgI1.latVec (sB k) τ := by
  funext r
  simp only [latVec_eq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases r <;>
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem latVec_mul (a b : PkgI1.B) (τ : ℂ) :
    PkgI1.latVec (a * b) τ = (PkgI1.iota a).map (fun r : ℝ => (r : ℂ)) *ᵥ PkgI1.latVec b τ := by
  unfold PkgI1.latVec
  rw [iota_mul, Matrix.mulVec_mulVec]
  congr 1
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- `ι(x)(τ, 1)ᵀ = j(γ, τ)(γτ, 1)ᵀ`. -/
theorem iota_v {x : PkgI1.B} {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    (PkgI1.iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![(τ : ℂ), 1] =
      denom γ τ • ![((γ • τ : UpperHalfPlane) : ℂ), 1] := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet)]
  have hd := denom_ne_zero γ τ
  have hd' : ((τ : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℝ) +
      ((γ : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℝ)) ≠ 0 := by rw [mul_comm]; exact hd
  funext r
  fin_cases r <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, num, denom, ← hγ] <;>
    field_simp

theorem latVec_smul_tau {x : PkgI1.B} {γ : GL (Fin 2) ℝ}
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) (b : PkgI1.B) :
    PkgI1.latVec (b * x) τ = denom γ τ • PkgI1.latVec b ((γ • τ : UpperHalfPlane) : ℂ) := by
  rw [latVec_mul]
  unfold PkgI1.latVec
  rw [iota_v hγ hdet, Matrix.mulVec_smul]

theorem Emat_eq (τ : ℂ) : PkgI1.Emat τ = Matrix.of fun r c => PkgI1.latVec (sB (Sum.inl c)) τ r := by
  ext r c; fin_cases c <;> rfl

theorem Fm_eq (τ : ℂ) :
    PkgI1.F0mat τ * PkgI1.Pinv = Matrix.of fun r c => PkgI1.latVec (sB (Sum.inr c)) τ r := by
  ext r c
  simp only [Matrix.mul_apply, Fin.sum_univ_two, PkgI1.F0mat, PkgI1.Pinv, Matrix.of_apply, latVec_eq]
  fin_cases r <;> fin_cases c <;> simp [sB, sf0, sf1, PkgI1.oBasis] <;> ring

theorem sB_inO (k : Fin 2 ⊕ Fin 2) : PkgI1.InO (sB k) := by
  rcases k with k | k <;> fin_cases k
  · exact ⟨![1, 0, 0, 0], by ext <;> simp [sB, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨![0, 1, 0, 0], by ext <;> simp [sB, PkgI1.oBasis, Fin.sum_univ_four]⟩
  · exact ⟨![0, 0, -2, -1], by ext <;> simp [sB, sf0, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩
  · exact ⟨![0, 0, -1, -1], by ext <;> simp [sB, sf1, PkgI1.oBasis, Fin.sum_univ_four] <;> norm_num⟩

/-! ### The integer matrix `N` and the transformation of `Ω` -/

/-- The integer matrix of `b ↦ z b x` in the basis `sB` (column `k` = coordinates of `z·sB_k·x`). -/
def Nmat {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ :=
  fun l k => Classical.choose (kap_int (hO (sB k) (sB_inO k)) l)

theorem Nmat_spec {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (l k : Fin 2 ⊕ Fin 2) : ((Nmat hO l k : ℤ) : ℚ) = kap (z * sB k * x) l :=
  (Classical.choose_spec (kap_int (hO (sB k) (sB_inO k)) l)).symm

theorem J_cast (l m : Fin 2 ⊕ Fin 2) : ((Matrix.J (Fin 2) ℤ l m : ℤ) : ℚ) = -Gm l m := by
  rcases l with l | l <;> rcases m with m | m <;>
    simp [Matrix.J, Gm, Matrix.one_apply]

/-- `Nᵀ ∈ Sp₄(ℤ)` when `b ↦ z b x` preserves the Riemann form. -/
theorem Nmat_symp {x z : PkgI1.B} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hB : ∀ a b, Bf (z * a * x) (z * b * x) = Bf a b) :
    (Nmat hO)ᵀ ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff, Matrix.transpose_transpose]
  set N := Nmat hO
  have hG : ∀ k k', ∑ l, ∑ m, (N l k : ℚ) * Gm l m * (N m k' : ℚ) = Gm k k' := by
    intro k k'
    simp_rw [N, Nmat_spec]
    rw [← Bf_expand, hB, Bf_expand]
    simp [kap_sB]
  ext k k'
  apply Int.cast_injective (α := ℚ)
  calc ((Nᵀ * Matrix.J (Fin 2) ℤ * N) k k' : ℚ)
      = ∑ m, ∑ l, (N l k : ℚ) * (Matrix.J (Fin 2) ℤ l m : ℚ) * (N m k' : ℚ) := by
        simp [Matrix.mul_apply]; ring
    _ = -∑ l, ∑ m, (N l k : ℚ) * Gm l m * (N m k' : ℚ) := by
        rw [Finset.sum_comm]; simp [J_cast, Finset.sum_neg_distrib]; ring
    _ = ((Matrix.J (Fin 2) ℤ k k' : ℤ) : ℚ) := by rw [hG, J_cast]

/-- `Ψ = j(γ, τ)·ι(z)`. -/
def Psi (z : PkgI1.B) (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) : Matrix (Fin 2) (Fin 2) ℂ :=
  denom γ τ • (PkgI1.iota z).map (fun r : ℝ => (r : ℂ))

theorem det_Psi (z : PkgI1.B) (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) :
    (Psi z γ τ).det = denom γ τ ^ 2 * ((PkgI1.iota z).det : ℂ) := by
  rw [Psi, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two, Matrix.det_fin_two]
  simp

theorem psi_latVec {x z : PkgI1.B} {γ : GL (Fin 2) ℝ} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) (k : Fin 2 ⊕ Fin 2) :
    Psi z γ τ *ᵥ PkgI1.latVec (sB k) ((γ • τ : UpperHalfPlane) : ℂ) =
      ∑ l, ((Nmat hO l k : ℤ) : ℂ) • PkgI1.latVec (sB l) τ := by
  have h1 : ∑ l, ((Nmat hO l k : ℤ) : ℂ) • PkgI1.latVec (sB l) τ =
      PkgI1.latVec (z * sB k * x) τ := by
    rw [← sum_kap (z * sB k * x), latVec_lin]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Nmat_spec hO l k]; push_cast; rfl
  rw [h1, mul_assoc, latVec_mul, latVec_smul_tau hγ hdet τ, Psi, Matrix.smul_mulVec,
    Matrix.mulVec_smul]

/-- The two block equations `Ψ E' = E N₁₁ + F N₂₁`, `Ψ F' = E N₁₂ + F N₂₂`. -/
theorem blocks {x z : PkgI1.B} {γ : GL (Fin 2) ℝ} (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    Psi z γ τ * PkgI1.Emat ((γ • τ : UpperHalfPlane) : ℂ) =
        PkgI1.Emat τ * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₁₁ +
          (PkgI1.F0mat τ * PkgI1.Pinv) * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₂₁ ∧
    Psi z γ τ * (PkgI1.F0mat ((γ • τ : UpperHalfPlane) : ℂ) * PkgI1.Pinv) =
        PkgI1.Emat τ * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₁₂ +
          (PkgI1.F0mat τ * PkgI1.Pinv) * ((Nmat hO).map (Int.cast : ℤ → ℂ)).toBlocks₂₂ := by
  rw [Emat_eq, Emat_eq, Fm_eq, Fm_eq]
  constructor
  · ext r c
    have := congrFun (psi_latVec hO hγ hdet τ (Sum.inl c)) r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_sum_type] at this
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.map_apply]
    rw [this]; simp only [Fin.sum_univ_two]; ring
  · ext r c
    have := congrFun (psi_latVec hO hγ hdet τ (Sum.inr c)) r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Fintype.sum_sum_type] at this
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply, Matrix.toBlocks₁₂,
      Matrix.toBlocks₂₂, Matrix.map_apply]
    rw [this]; simp only [Fin.sum_univ_two]; ring

/-- Linear algebra: the block equations give `Ω' = Nᵀ·Ω` and the automorphy factor. -/
theorem spAct_of_blocks {Ω Ω' E F E' F' Ψ : Matrix (Fin 2) (Fin 2) ℂ}
    {N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hF : IsUnit F.det) (hF' : IsUnit F'.det) (hΨ : IsUnit Ψ.det) (hΩ : Ω = F⁻¹ * E)
    (hΩ' : Ω' = F'⁻¹ * E') (hs : Ωᵀ = Ω) (hs' : Ω'ᵀ = Ω')
    (h1 : Ψ * E' = E * (N.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ + F * (N.map (Int.cast : ℤ → ℂ)).toBlocks₂₁)
    (h2 : Ψ * F' = E * (N.map (Int.cast : ℤ → ℂ)).toBlocks₁₂ + F * (N.map (Int.cast : ℤ → ℂ)).toBlocks₂₂) :
    Ω' = PkgI1.spAct Nᵀ Ω ∧ PkgI1.spFactor Nᵀ Ω * F.det = Ψ.det * F'.det := by
  set Nc := N.map (Int.cast : ℤ → ℂ) with hNc
  set X := Ω * Nc.toBlocks₁₂ + Nc.toBlocks₂₂ with hXdef
  have hFΩ : F * Ω = E := by rw [hΩ, ← mul_assoc, mul_nonsing_inv _ hF, one_mul]
  have hF'Ω : F' * Ω' = E' := by rw [hΩ', ← mul_assoc, mul_nonsing_inv _ hF', one_mul]
  have hFX : F * X = Ψ * F' := by rw [h2, hXdef, mul_add, ← mul_assoc, hFΩ]
  have hdetX : F.det * X.det = Ψ.det * F'.det := by rw [← det_mul, hFX, det_mul]
  have hX : IsUnit X.det := by
    have : IsUnit (F.det * X.det) := by rw [hdetX]; exact hΨ.mul hF'
    exact isUnit_of_mul_isUnit_right this
  have hXΩ : X * Ω' = Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁ := by
    have e : F * (X * Ω') = F * (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁) := by
      rw [← mul_assoc, hFX, mul_assoc, hF'Ω, h1, mul_add, ← mul_assoc, hFΩ]
    have e2 := congrArg (F⁻¹ * ·) e
    simp only [← mul_assoc, nonsing_inv_mul _ hF, one_mul] at e2
    exact e2
  have hΩ'X : Ω' = X⁻¹ * (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁) := by
    rw [← hXΩ, ← mul_assoc, nonsing_inv_mul _ hX, one_mul]
  have hb11 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ = Nc.toBlocks₁₁ᵀ := by ext; rfl
  have hb12 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₂ = Nc.toBlocks₂₁ᵀ := by ext; rfl
  have hb21 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ = Nc.toBlocks₁₂ᵀ := by ext; rfl
  have hb22 : (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂ = Nc.toBlocks₂₂ᵀ := by ext; rfl
  have hXT : Xᵀ = Nc.toBlocks₁₂ᵀ * Ω + Nc.toBlocks₂₂ᵀ := by
    rw [hXdef, transpose_add, transpose_mul, hs]
  constructor
  · show Ω' = (((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₁₂) *
      ((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂)⁻¹)
    rw [hb11, hb12, hb21, hb22, ← hXT]
    calc Ω' = Ω'ᵀ := hs'.symm
      _ = (Ω * Nc.toBlocks₁₁ + Nc.toBlocks₂₁)ᵀ * X⁻¹ᵀ := by rw [hΩ'X, transpose_mul]
      _ = (Nc.toBlocks₁₁ᵀ * Ω + Nc.toBlocks₂₁ᵀ) * Xᵀ⁻¹ := by
        rw [transpose_nonsing_inv, transpose_add, transpose_mul, hs]
  · show ((Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₁ * Ω + (Nᵀ.map (Int.cast : ℤ → ℂ)).toBlocks₂₂).det * F.det = _
    rw [hb21, hb22, ← hXT, det_transpose, mul_comm]
    exact hdetX

/-! ### Weight 8 for one element -/

theorem dF_ne_aux {t : ℂ} (ht : 0 < t.im) : (t - 3) * (t + 1) ≠ 0 := by
  apply mul_ne_zero <;> intro h <;> have := congrArg Complex.im h <;> simp at this <;>
    exact ht.ne' this

/-- **Exact weight 8 under `γ = ι(x)`**, given `z` with `z𝒪x ⊆ 𝒪`, `E(zax, zbx) = E(a, b)` and
`nrd(z)nrd(x) = ±1`, from Igusa's theta modularity. -/
theorem weight_of_z (hT : PkgI1.ThetaModularity) {x z : PkgI1.B} {γ : GL (Fin 2) ℝ}
    (hO : ∀ b, PkgI1.InO b → PkgI1.InO (z * b * x))
    (hB : ∀ a b, Bf (z * a * x) (z * b * x) = Bf a b)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x)
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hz4 : ((PkgI1.iota z).det * (PkgI1.iota x).det) ^ 4 = 1) (τ : UpperHalfPlane) :
    G8 ((γ • τ : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ τ ^ 8 * G8 (τ : ℂ) := by
  have htim : 0 < (τ : ℂ).im := τ.im_pos
  have ht'im : 0 < ((γ • τ : UpperHalfPlane) : ℂ).im := (γ • τ).im_pos
  have hdz : (PkgI1.iota z).det ≠ 0 := by
    intro h; rw [h, zero_mul, zero_pow (by norm_num)] at hz4; exact zero_ne_one hz4
  have hF : IsUnit (PkgI1.F0mat (τ : ℂ) * PkgI1.Pinv).det := (det_F0P_ne htim.ne').isUnit
  have hF' : IsUnit (PkgI1.F0mat ((γ • τ : UpperHalfPlane) : ℂ) * PkgI1.Pinv).det :=
    (det_F0P_ne ht'im.ne').isUnit
  have hΨ : IsUnit (Psi z γ τ).det := by
    rw [det_Psi]
    exact (mul_ne_zero (pow_ne_zero 2 (denom_ne_zero γ τ)) (by exact_mod_cast hdz)).isUnit
  have hS := omegaSiegel_proof (τ : ℂ) htim
  have hS' := omegaSiegel_proof ((γ • τ : UpperHalfPlane) : ℂ) ht'im
  obtain ⟨hb1, hb2⟩ := blocks hO hγ hdet τ
  obtain ⟨hact, hfac⟩ := spAct_of_blocks (Ω := PkgI1.Omega (τ : ℂ))
    (Ω' := PkgI1.Omega ((γ • τ : UpperHalfPlane) : ℂ)) hF hF' hΨ rfl rfl hS.1 hS'.1 hb1 hb2
  have hθ := (hT _ (Nmat_symp hO hB) _ hS).1
  rw [← hact] at hθ
  set φ := PkgI1.spFactor (Nmat hO)ᵀ (PkgI1.Omega (τ : ℂ))
  rw [det_Psi, det_F0P, det_F0P] at hfac
  have hs2 : -(√2 : ℂ) / 2 ≠ 0 := by
    have : (√2 : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; positivity
    exact div_ne_zero (neg_ne_zero.mpr this) two_ne_zero
  have hq : φ * (((τ : ℂ) - 3) * ((τ : ℂ) + 1)) = denom γ τ ^ 2 * ((PkgI1.iota z).det : ℂ) *
      ((((γ • τ : UpperHalfPlane) : ℂ) - 3) * (((γ • τ : UpperHalfPlane) : ℂ) + 1)) := by
    apply mul_left_cancel₀ hs2
    linear_combination hfac
  have hz4c : (((PkgI1.iota z).det : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ)) ^ 4 = 1 := by
    rw [hγ]; exact_mod_cast hz4
  have e : (φ * (((τ : ℂ) - 3) * ((τ : ℂ) + 1))) ^ 4 = (denom γ τ ^ 2 * ((PkgI1.iota z).det : ℂ) *
      ((((γ • τ : UpperHalfPlane) : ℂ) - 3) * (((γ • τ : UpperHalfPlane) : ℂ) + 1))) ^ 4 := by
    rw [hq]
  unfold G8
  rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff (pow_ne_zero 4 (dF_ne_aux ht'im))
    (pow_ne_zero 4 (dF_ne_aux htim)), hθ]
  linear_combination (PkgI1.thetaSum8 (PkgI1.Omega (τ : ℂ)) *
      (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4) * e +
    (denom γ τ ^ 8 * PkgI1.thetaSum8 (PkgI1.Omega (τ : ℂ)) *
      ((((γ • τ : UpperHalfPlane) : ℂ) - 3) * (((γ • τ : UpperHalfPlane) : ℂ) + 1)) ^ 4) * hz4c

/-! ### The normalizer of `𝒪` -/

/-- **LEAF (published; structure of the normalizer of a maximal order).** Every `x ∈ B^×`
normalizing `𝒪` is `x = r·w·u` with `r ∈ ℚ^×`, `u ∈ 𝒪^×` and `w ∈ {1, i, j + ij, μ = 2j + ij}`.

Source: for a maximal order `𝒪` of an indefinite quaternion algebra over `ℚ` of discriminant `D`,
`N_{B^×}(𝒪)/ℚ^×𝒪^×` is the Atkin–Lehner group `≅ (ℤ/2ℤ)^{ω(D)}`, generated by elements whose
two-sided ideals are the prime ideals `𝔓_p` over `p ∣ D` (Vignéras, *Arithmétique des algèbres de
quaternions*, LNM 800, 1980, Ch. II §1 and Ch. III §5; Voight, *Quaternion Algebras*, GTM 288, 2021,
§18.5 and Ch. 23 (two-sided ideals of a maximal order; principal by Eichler's class number one
theorem); locators UNVERIFIED). Here `D = 6`: `i` (`nrd = −2`) and `j + ij` (`nrd = −3`) lie in
`𝒪`, normalize it (VERIFIED, `py/weight_check.py` and `conjO_*` below) and generate `𝔓₂`, `𝔓₃`;
`μ = i(j + ij)`. -/
def NormalizerDecomp : Prop :=
  ∀ x : PkgI1.B, PkgI1.NormalizesO x →
    ∃ r : ℚ, r ≠ 0 ∧ ∃ w : PkgI1.B,
      (w = 1 ∨ w = PkgI1.qi ∨ w = PkgI1.qj + PkgI1.qk ∨ w = PkgI1.mu) ∧
      ∃ u v : PkgI1.B, PkgI1.InO u ∧ PkgI1.InO v ∧ u * v = 1 ∧ x = r • (w * u)

theorem nrd_smul (r : ℚ) (a : PkgI1.B) : nrd (r • a) = r ^ 2 * nrd a := by
  simp [nrd]; ring

theorem nrd_int {a : PkgI1.B} (h : PkgI1.InO a) : ∃ m : ℤ, nrd a = m := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2, ?_⟩
  simp [nrd, PkgI1.oBasis, Fin.sum_univ_four]
  ring

theorem nrd_unit {u v : PkgI1.B} (hu : PkgI1.InO u) (hv : PkgI1.InO v) (huv : u * v = 1) :
    nrd u = 1 ∨ nrd u = -1 := by
  obtain ⟨m, hm⟩ := nrd_int hu
  obtain ⟨m', hm'⟩ := nrd_int hv
  have h : nrd u * nrd v = 1 := by rw [← nrd_mul, huv, nrd_one]
  rw [hm, hm'] at h
  have h' : m * m' = 1 := by exact_mod_cast h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h' with h1 | h1 <;> simp [hm, h1]

theorem weight_case (hT : PkgI1.ThetaModularity) {w winv : PkgI1.B} {σ : ℚ}
    (hwinv : winv * w = 1) (hcO : ∀ b, PkgI1.InO b → PkgI1.InO (winv * b * w))
    (hcB : ∀ a b, Bf (winv * a * w) (winv * b * w) = σ * Bf a b)
    (hsign : ∀ n : ℚ, (n = 1 ∨ n = -1) → 0 < nrd w * n → n * σ = 1)
    {r : ℚ} (hr : r ≠ 0) {u v : PkgI1.B} (hu : PkgI1.InO u) (hv : PkgI1.InO v) (huv : u * v = 1)
    {γ : GL (Fin 2) ℝ} (hγ : (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota (r • (w * u)))
    (hdet : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    G8 ((γ • τ : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 4 =
      denom γ τ ^ 8 * G8 (τ : ℂ) := by
  have hzbx : ∀ b, (r⁻¹ • winv) * b * (r • (w * u)) = winv * b * w * u := by
    intro b
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hr, one_smul]
    simp only [mul_assoc]
  have hzx : (r⁻¹ • winv) * (r • (w * u)) = u := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hr, one_smul, ← mul_assoc,
      hwinv, one_mul]
  have hO : ∀ b, PkgI1.InO b → PkgI1.InO ((r⁻¹ • winv) * b * (r • (w * u))) :=
    fun b hb => by rw [hzbx]; exact inO_mul (hcO b hb) hu
  have hnu := nrd_unit hu hv huv
  have hpos : 0 < nrd w * nrd u := by
    have h1 : (0 : ℝ) < (nrd (r • (w * u)) : ℝ) := by rw [← det_iota_eq, ← hγ]; exact hdet
    have h2 : 0 < nrd (r • (w * u)) := by exact_mod_cast h1
    rw [nrd_smul, nrd_mul] at h2
    have hr2 : 0 < r ^ 2 := by positivity
    exact pos_of_mul_pos_right h2 hr2.le
  have hσ := hsign _ hnu hpos
  have hB : ∀ a b, Bf ((r⁻¹ • winv) * a * (r • (w * u))) ((r⁻¹ • winv) * b * (r • (w * u))) =
      Bf a b := by
    intro a b
    rw [hzbx, hzbx, Bf_mul_right, hcB, ← mul_assoc, hσ, one_mul]
  have hz4 : ((PkgI1.iota (r⁻¹ • winv)).det * (PkgI1.iota (r • (w * u))).det) ^ 4 = 1 := by
    rw [det_iota_eq, det_iota_eq, ← Rat.cast_mul, ← nrd_mul, hzx]
    rcases hnu with h | h <;> simp [h] <;> norm_num
  exact weight_of_z hT hO hB hγ hdet hz4 τ

/-! ### The four representatives `w` -/

theorem qjk_eq : PkgI1.qj + PkgI1.qk = (⟨0, 0, 1, 1⟩ : PkgI1.B) := by
  ext <;> simp [PkgI1.qj, PkgI1.qk]

theorem conjO_one {b : PkgI1.B} (hb : PkgI1.InO b) : PkgI1.InO (1 * b * 1) := by simpa using hb

theorem conjO_i {b : PkgI1.B} (hb : PkgI1.InO b) :
    PkgI1.InO ((⟨0, 1/2, 0, 0⟩ : PkgI1.B) * b * PkgI1.qi) := by
  obtain ⟨n, rfl⟩ := hb
  refine ⟨![n 0 + n 2, n 1 + n 3, -n 2, -n 3], ?_⟩
  ext <;> simp [PkgI1.qi, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem conjO_jk {b : PkgI1.B} (hb : PkgI1.InO b) :
    PkgI1.InO ((⟨0, 0, 1/3, 1/3⟩ : PkgI1.B) * b * (PkgI1.qj + PkgI1.qk)) := by
  obtain ⟨n, rfl⟩ := hb
  refine ⟨![n 0 + 2 * n 2 - 2 * n 3, -n 1 + n 2 - 2 * n 3, -3 * n 2 + 4 * n 3, -2 * n 2 + 3 * n 3], ?_⟩
  rw [qjk_eq]
  ext <;> simp [PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem conjO_mu {b : PkgI1.B} (hb : PkgI1.InO b) :
    PkgI1.InO (PkgI1.muInv * b * PkgI1.mu) := by
  obtain ⟨n, rfl⟩ := hb
  refine ⟨![n 0 - n 2 + 2 * n 3, -n 1 - n 2 + n 3, 3 * n 2 - 4 * n 3, 2 * n 2 - 3 * n 3], ?_⟩
  ext <;> simp [PkgI1.mu, PkgI1.muInv, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem Bf_conj_i (a b : PkgI1.B) :
    Bf ((⟨0, 1/2, 0, 0⟩ : PkgI1.B) * a * PkgI1.qi) ((⟨0, 1/2, 0, 0⟩ : PkgI1.B) * b * PkgI1.qi) =
      -1 * Bf a b := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, PkgI1.qi, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

theorem Bf_conj_jk (a b : PkgI1.B) :
    Bf ((⟨0, 0, 1/3, 1/3⟩ : PkgI1.B) * a * (PkgI1.qj + PkgI1.qk))
      ((⟨0, 0, 1/3, 1/3⟩ : PkgI1.B) * b * (PkgI1.qj + PkgI1.qk)) = -1 * Bf a b := by
  rw [qjk_eq]
  simp only [Bf, PkgI1.trd, PkgI1.muInv, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

theorem Bf_conj_mu (a b : PkgI1.B) :
    Bf (PkgI1.muInv * a * PkgI1.mu) (PkgI1.muInv * b * PkgI1.mu) = 1 * Bf a b := by
  simp only [Bf, PkgI1.trd, PkgI1.muInv, PkgI1.mu, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul,
    QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star,
    QuaternionAlgebra.imK_star]
  ring

/-- **`S8WeightExact` from Igusa's `ThetaModularity` and `NormalizerDecomp` (proved).** -/
theorem s8WeightExact_of (hT : PkgI1.ThetaModularity) (hN : NormalizerDecomp) : S8WeightExact := by
  intro γ hγ τ
  obtain ⟨x, hxN, hγx, hdet⟩ := hγ
  obtain ⟨r, hr, w, hw, u, v, hu, hv, huv, rfl⟩ := hN x hxN
  rcases hw with rfl | rfl | rfl | rfl
  · refine weight_case hT (winv := 1) (σ := 1) (by simp) (fun b hb => conjO_one hb)
      (fun a b => by simp) ?_ hr hu hv huv hγx hdet τ
    rintro n (rfl | rfl) h <;> simp [nrd_one] at h ⊢ <;> linarith
  · refine weight_case hT (winv := ⟨0, 1/2, 0, 0⟩) (σ := -1)
      (by ext <;> simp [PkgI1.qi]) (fun b hb => conjO_i hb) Bf_conj_i ?_ hr hu hv huv hγx hdet τ
    rintro n (rfl | rfl) h <;> (try norm_num) <;> norm_num [nrd, PkgI1.qi] at h
  · refine weight_case hT (winv := ⟨0, 0, 1/3, 1/3⟩) (σ := -1)
      (by rw [qjk_eq]; ext <;> simp <;> norm_num) (fun b hb => conjO_jk hb) Bf_conj_jk ?_
      hr hu hv huv hγx hdet τ
    rintro n (rfl | rfl) h <;> (try norm_num) <;> rw [qjk_eq] at h <;> norm_num [nrd] at h
  · refine weight_case hT (winv := PkgI1.muInv) (σ := 1)
      (by ext <;> simp [PkgI1.mu, PkgI1.muInv] <;> norm_num) (fun b hb => conjO_mu hb) Bf_conj_mu ?_
      hr hu hv huv hγx hdet τ
    rintro n (rfl | rfl) h <;> (try norm_num) <;> norm_num [nrd, PkgI1.mu] at h

end HSyn.G0Split.FibreQM.PeriodNum

end

#print axioms HSyn.G0Split.FibreQM.PeriodNum.s8WeightExact_of
