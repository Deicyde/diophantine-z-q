import Mathlib
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.Compiler.Precision.HeightConstant

/-!
# H = `ZInQ.SixContactMin` decomposed into literature leaves and glue (synthesis)

Companion of `docs/research/h-decomposition.md`. Check with
`lake env lean scratch/h-decomposition/Leaves.lean`.

Layout (each block copied verbatim from a report's compiled draft, inside its own section).
* `PkgI1` (pkg-I1): the quaternion order, genus-2 theta constants, Igusa invariants; the leaves
  `ThetaModularity` (R4), `QMHauptmodul` (a consequence of R2-R4, not counted as a leaf),
  `IgusaClebschSeparation` (T28); proved glue for A1, A5, A7, A10, F1.
* `PkgI2` (pkg-I2): abelian varieties as `Grp (Over (Spec K))`, good reduction as abelian schemes,
  torsion points with Galois/inertia action; the reduction-theory leaves; two proved consequences.
* `PkgI3` (pkg-I3): bundled abelian varieties `AbVar` with `Hom`, Tate modules `T_ℓ`, `V_ℓ` and the
  Galois representation; Faltings 1983 (R9) and Mumford's theorems; proved E1 and C2 glue.
* `PkgI6` (pkg-I6): continuous Galois cohomology leaves for B2, local Kronecker–Weber, local
  reciprocity with upper numbering, ramification leaves; the proved Brauer step of B2.
* `GlueConductor` (glue-conductor): the elementary core of D1-D5, proved; two different-ideal
  leaves stated over Mathlib.
* `GlueAssembly` (glue-assembly): F2 on Mathlib's Weil heights, E2-E4/F3 arithmetic, the final
  constant and F4: `GlueOutputs S → SixContactMinAt S`, proved; C8, E1, E2, F3 glue.
* `HSyn` §0-§1 (from the hdec-faithful draft): the absolute Galois group of `ℚ`, places,
  Frobenius, continuous `GL_n(ℚ̄_ℓ)`-representations, cusp forms with nebentypus, normalized
  eigenforms, and the leaves statable over them.
* `HSyn` §2: every other leaf as a **placeholder** `opaque … : Prop`. **A placeholder carries no
  content**: it is an uninterpreted proposition whose docstring records the exact statement and
  reference. A theorem with a placeholder among its hypotheses says nothing until the placeholder
  is replaced by a genuine statement.
* `HSyn` §3: the leaves bundled (`ResearchLeaves`, `TextbookLeaves`) and the top-level theorem
  `sixContactMin_of_leaves : ResearchLeaves → TextbookLeaves → ZInQ.SixContactMin`, which is
  `glueOutputs_of_leaves` (glue G1-G17, G19, `sorry`) followed by glue-assembly's proved
  `GlueOutputs Mult.S_mul → SixContactMin` (G18-G20, checked against the real
  `ZInQ.SixContactMin`). `GlueOutputs` is a numerical interface, not a leaf.

Other `sorry`s, all glue statements of the reports: `PkgI2.goodReduction_of_QM_rational3` (A6),
`PkgI6.artinConductor_le_of_upper` (D4), `PkgI6.sq_principalUnits` (D3; proved in another form
as `GlueConductor.exists_sq_eq_one_add`).

No `axiom` declarations. Leaf numbering (R1-R22 research-level, T1-T29 textbook) is that of the
note's §2.
-/

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


end
end PkgI1Sec

section PkgI2Sec
/-! ### Copied from `scratch/pkg-I2/I2.lean` (compiled there). -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

namespace PkgI2

/-! ## 1. Purity of the branch locus (SGA 1 X 3.4; Stacks 0BMB), ring form -/

/-- **Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-! ## 2. Abelian varieties, points, Galois action, inertia, good reduction -/

section AV

variable {K : Type u} [Field K]

/-- `Spec L` as a scheme over `Spec K`. -/
noncomputable def specOver (K L : Type u) [Field K] [CommRing L] [Algebra K L] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- An abelian variety over `K`: a group object of `Over (Spec K)` whose structure morphism is
proper, smooth and geometrically integral (Mathlib's notions). Mathlib proves that such a group
object is commutative (`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
class IsAbelianVariety (A : Grp (Over (Spec (.of K)))) : Prop where
  proper : IsProper A.X.hom
  smooth : Smooth A.X.hom
  geomIntegral : GeometricallyIntegral A.X.hom

/-- An abelian scheme over a ring `O`: a group object of `Over (Spec O)`, proper, smooth, with
geometrically connected fibres (Mumford, GIT, Def. 6.1). -/
class IsAbelianScheme {O : Type u} [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) : Prop where
  proper : IsProper 𝒜.X.hom
  smooth : Smooth 𝒜.X.hom
  geomConnected : GeometricallyConnected 𝒜.X.hom

/-- The `L`-points `A(L)` of a scheme over `K`, for a `K`-algebra `L`; for a group object this
is a group (`MonObj.Hom.group`). -/
abbrev Pts (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] :=
  specOver K L ⟶ A.X

/-- The `m`-torsion `A(L)[m]`. -/
def torsion (A : Grp (Over (Spec (.of K)))) (L : Type u) [CommRing L] [Algebra K L] (m : ℕ) :
    Set (Pts A L) :=
  {x | x ^ m = 1}

/-- The automorphism of `Spec L` over `Spec K` induced by `σ ∈ Aut(L/K)`. -/
noncomputable def galHom (L : Type u) [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) :
    specOver K L ⟶ specOver K L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [specOver, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- The Galois action on points: `(σ • x)` has coordinates `σ ∘ x^*`. -/
noncomputable def galAct (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Pts A L :=
  galHom L σ ≫ x

/-- `σ` lies in the inertia group of the valuation subring `w` of `L` (Mathlib's
`ValuationSubring.inertiaSubgroup`). -/
def IsInertia {L : Type u} [Field L] [Algebra K L] (w : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    Prop :=
  ∃ h : σ ∈ w.decompositionSubgroup K,
    (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K

/-- `A` has good reduction at the valuation subring `O` of `K`: there is an abelian scheme over
`O` whose generic fibre is isomorphic to `A` as a group object over `K` (Serre–Tate 1968, §1). -/
def HasGoodReduction (A : Grp (Over (Spec (.of K)))) (O : ValuationSubring K) : Prop :=
  ∃ 𝒜 : Grp (Over (Spec (.of O))), IsAbelianScheme 𝒜 ∧
    Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)

/-- The inertia group of `w` acts trivially on `A(L)[m]`. -/
def InertiaTrivialOn (A : Grp (Over (Spec (.of K)))) {L : Type u} [Field L] [Algebra K L]
    (w : ValuationSubring L) (m : ℕ) : Prop :=
  ∀ σ : L ≃ₐ[K] L, IsInertia w σ → ∀ x ∈ torsion A L m, galAct A σ x = x

/-- `(σ - 1)² x = 0`, written multiplicatively (the group of points is commutative). -/
def UnipSq (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : Prop :=
  galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ * (galAct A σ x)⁻¹ * x = 1

end AV

/-! ## 3. Néron–Ogg–Shafarevich and potential good reduction (Serre–Tate 1968) -/

/-- **Leaf I2-NOS (Serre–Tate 1968, Thm 1; criterion of Néron–Ogg–Shafarevich).**
`K` a field with a discrete valuation ring `O`, `w` a valuation ring of `K̄` over `O`, `A/K` an
abelian variety. Then (a) ⟺ (b) ⟺ (c), where (a) good reduction at `O`, (b) for every `m ≥ 1`
invertible in `O`, inertia at `w` fixes `A(K̄)[m]`, (c) the same for infinitely many such `m`. -/
def NeronOggShafarevich : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      (HasGoodReduction A O ↔
        ∀ m : ℕ, 0 < m → IsUnit (m : O) → InertiaTrivialOn A w m) ∧
      (HasGoodReduction A O ↔
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ InertiaTrivialOn A w m}.Infinite)


/-- Base change `A_{K'}` of a group object along a field extension `K → K'`. -/
noncomputable def baseChange {K : Type u} [Field K] (A : Grp (Over (Spec (.of K))))
    (K' : Type u) [Field K'] [Algebra K K'] : Grp (Over (Spec (.of K'))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K K')))).mapGrp.obj A

/-- **Leaf I2-ST2 (Serre–Tate 1968, Thm 2; potential good reduction).** For a prime `ℓ`
invertible in `O`: `A` acquires good reduction over a finite extension `K' ⊆ K̄` (at `w ∩ K'`) iff
an open subgroup `I ∩ G_{K'}` of inertia acts trivially on every `A(K̄)[ℓⁿ]`, i.e. the image of
inertia in `Aut(T_ℓ A)` is finite. Used only on the h-b1 route for A6 (not on the route of §5 of
docs/research/pkg-I2.md). -/
def SerreTatePotentialGood : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (ℓ : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      ((∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          HasGoodReduction (baseChange A K') (w.comap (algebraMap K' (AlgebraicClosure K)))) ↔
       (∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
          ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
            (∀ x ∈ K', σ x = x) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), galAct A σ x = x))

/-! ## 4. Semistable reduction: Grothendieck (SGA 7 IX 3.5, 3.6) and Raynaud (SGA 7 IX 4.7) -/

/-- **Leaf I2-SS (Grothendieck's semistable reduction theorem, monodromy form).** Consequence of
SGA 7 I, Exp. IX, Thm 3.6 (`A` acquires semistable reduction over a finite extension `K'`) and
the direction "semistable ⇒ inertia acts unipotently of echelon ≤ 2" of Prop. 3.5 (numbers
UNVERIFIED): there is a finite `K' ⊆ K̄` such that every `σ` in the inertia group of `w` fixing
`K'` satisfies `(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`.
The finite-level form is equivalent to `(σ-1)² = 0` on `T_ℓ A`, since `T_ℓ A → A[ℓⁿ]` is onto. -/
def GrothendieckMonodromy : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A],
      ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
        ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
          (∀ x ∈ K', σ x = x) →
          ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
            ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-- **Leaf I2-Ray (Raynaud's criterion, Galois form).** Consequence of SGA 7 I, Exp. IX,
Prop. 4.7 (Raynaud: if `m ≥ 3` is invertible in `O` and the points of `A[m]` are rational over
`K`, then `A` has semistable reduction; also Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995),
Thm 3.5 per h-trust, ASTRA-READ there) and the direction "semistable ⇒ unipotent of echelon ≤ 2"
of SGA 7 IX Prop. 3.5 (numbers UNVERIFIED): every `σ` in the inertia group of `w` satisfies
`(σ - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ` invertible in `O` and every `n`. -/
def RaynaudCriterion : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∀ (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ), 3 ≤ m → IsUnit (m : O) →
      (∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
          ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, IsInertia w σ →
        ∀ ℓ : ℕ, ℓ.Prime → IsUnit (ℓ : O) →
          ∀ n : ℕ, ∀ x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n), UnipSq A σ x

/-! ## 5. Néron mapping property for abelian schemes, and reduction of torsion -/

/-- **Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base). -/
def NeronMappingAbelianScheme : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

section Reduction

variable {K : Type u} [Field K]

/-- The ring map `O → w` for a valuation ring `w` of `L` lying over `O`. -/
def toW {L : Type u} [Field L] [Algebra K L] (O : ValuationSubring K) (w : ValuationSubring L)
    (hw : w.comap (algebraMap K L) = O) : O →+* w :=
  ((algebraMap K L).comp O.subtype).codRestrict w.toSubring (fun x => by
    have : (x : K) ∈ w.comap (algebraMap K L) := by rw [hw]; exact x.2
    exact this)

/-- `y ∈ 𝒜(κ(w))` is the reduction of `x ∈ A(L)`: some `x̃ ∈ 𝒜(w)` restricts to `x` on the
generic point (through `e : 𝒜_K ≅ A`) and to `y` on the closed point. -/
def IsReductionOf {L : Type u} [Field L] [Algebra K L] {O : ValuationSubring K}
    {A : Grp (Over (Spec (.of K)))} (𝒜 : Grp (Over (Spec (.of O))))
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (w : ValuationSubring L) (hw : w.comap (algebraMap K L) = O) (x : Pts A L)
    (y : Over.mk (Spec.map (CommRingCat.ofHom
      ((IsLocalRing.residue w).comp (toW O w hw)))) ⟶ 𝒜.X) : Prop :=
  ∃ x' : Over.mk (Spec.map (CommRingCat.ofHom (toW O w hw))) ⟶ 𝒜.X,
    (x ≫ (e.inv.hom.hom : A.X ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).obj 𝒜.X)).left ≫
        pullback.fst 𝒜.X.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
        Spec.map (CommRingCat.ofHom w.subtype) ≫ x'.left ∧
    y.left = Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫ x'.left

end Reduction

/-- **Leaf I2-Red (reduction of prime-to-`p` torsion at good reduction).** Serre–Tate 1968, §1
(proof of Thm 1, (a) ⇒ (b); locator UNVERIFIED): if `A` has good reduction with abelian scheme
`𝒜` and `m ≥ 1` is invertible in `O`, reduction is a bijection
`A(K̄)[m] → 𝒜(κ(w))[m]`. -/
def ReductionTorsionBijective : Prop :=
  ∀ (K : Type u) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜]
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj 𝒜 ≅ A)
    (m : ℕ), 0 < m → IsUnit (m : O) →
      (∀ x ∈ torsion A (AlgebraicClosure K) m,
        ∃! y, y ^ m = 1 ∧ IsReductionOf 𝒜 e w hw x y) ∧
      (∀ y, y ^ m = 1 → ∃! x, x ∈ torsion A (AlgebraicClosure K) m ∧ IsReductionOf 𝒜 e w hw x y)

/-! ## 6. Structure of torsion (Mumford, *Abelian varieties*, §4) -/

/-- **Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space. -/
def TorsionStructure : Prop :=
  ∀ (K : Type u) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-! ## 7. Abhyankar's lemma for discrete valuation rings -/

/-- **Leaf I2-AbDVR (Abhyankar's lemma, DVR form).** SGA 1, Exp. X, Lemme 3.6 (number
UNVERIFIED); also Stichtenoth, *Algebraic function fields and codes*, Thm 3.9.1, and Cornell,
Gold (classical). `R` a DVR with fraction field `K`, uniformizer `π`; `L/K` finite separable, tamely
ramified over `R` (every prime `Q` of the integral closure `S` of `R` in `L` over the maximal
ideal has `e(Q)` invertible in `R` and separable residue extension); `n` invertible in `R` with every
`e(Q) ∣ n`. Let `M = L(t)` with `tⁿ = π`. Then every prime of the integral closure of `R` in `M`
over the maximal ideal has ramification index exactly `n` and separable residue extension
(equivalently: `M/K(t)` is unramified above `R`, as `K(t)/K` is totally ramified of degree `n`). -/
def AbhyankarDVR : Prop :=
  ∀ (R K L M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field M] [Algebra L M] [Algebra K M] [Algebra R M]
    [IsScalarTower K L M] [IsScalarTower R K M]
    (π : R), Irreducible π → ∀ (n : ℕ), 0 < n → IsUnit (n : R) →
    (∀ (Q : Ideal (integralClosure R L)) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal R)],
      IsUnit ((Q.ramificationIdx R : ℕ) : R) ∧ Q.ramificationIdx R ∣ n ∧
      Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R L ⧸ Q)) →
    ∀ t : M, t ^ n = algebraMap R M π → IntermediateField.adjoin L {t} = ⊤ →
      ∀ (Q : Ideal (integralClosure R M)) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal R)],
        Q.ramificationIdx R = n ∧
        Algebra.IsSeparable (R ⧸ IsLocalRing.maximalIdeal R) (integralClosure R M ⧸ Q)


/-! ## 8. Characteristic polynomial independent of `ℓ` (Mumford §19, Thm 4; boundary with I3) -/

/-- **Leaf I2-Char (Mumford, *Abelian varieties*, §19, Thm 4; locator UNVERIFIED).** For an
endomorphism `φ` of an abelian variety `B` of dimension `g` over a field `k` there is a monic
`P ∈ ℤ[X]` of degree `2g` which, for every prime `ℓ ≠ char k`, is the characteristic polynomial of
`φ` on `T_ℓ B`; finite-level form: reduced mod `ℓⁿ` it is the characteristic polynomial of the
matrix of `φ` on `B(k̄)[ℓⁿ]` in any `ℤ/ℓⁿ`-basis. Used in C10 (the trace of `Frob ∘ μ̄_σ` is one
integer for all `ℓ`). -/
def CharpolyIndependentOfEll : Prop :=
  ∀ (k : Type u) [Field k] (B : Grp (Over (Spec (.of k)))) [IsAbelianVariety B] (g : ℕ),
    topologicalKrullDim B.X.left = (g : WithBot ℕ∞) → ∀ φ : B ⟶ B,
    ∃ P : Polynomial ℤ, P.Monic ∧ P.natDegree = 2 * g ∧
      ∀ ℓ : ℕ, ℓ.Prime → (ℓ : k) ≠ 0 → ∀ n : ℕ, 0 < n →
        ∀ e : torsion B (AlgebraicClosure k) (ℓ ^ n) ≃ (Fin (2 * g) → ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n),
          ∀ h : x.1 * y.1 ∈ torsion B (AlgebraicClosure k) (ℓ ^ n),
            e ⟨x.1 * y.1, h⟩ = e x + e y) →
        ∀ M : Matrix (Fin (2 * g)) (Fin (2 * g)) (ZMod (ℓ ^ n)),
        (∀ x y : torsion B (AlgebraicClosure k) (ℓ ^ n), y.1 = x.1 ≫ φ.hom.hom →
          e y = M.mulVec (e x)) →
        M.charpoly = P.map (Int.castRingHom (ZMod (ℓ ^ n)))

/-- **Leaf I2-Rank (Mumford, *Abelian varieties*, §19, Thm 3, rank part; boundary with I3;
locator UNVERIFIED).** For abelian varieties `A, B` over `k` of dimensions `g, g'`, the group of
homomorphisms `A → B` has rank at most `4gg'`: any `4gg' + 1` homomorphisms are `ℤ`-linearly
dependent in the (commutative) group `A.X ⟶ B.X`. Used in A8 (`r ≤ 16F₀²`). The instance argument
`IsCommMonObj B.X` holds for every abelian variety (Mathlib,
`isCommMonObj_of_isProper_of_geometricallyIntegral`). -/
def HomRankBound : Prop :=
  ∀ (k : Type u) [Field k] (A B : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    [IsAbelianVariety B] [IsCommMonObj B.X] (g g' : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) →
    topologicalKrullDim B.X.left = (g' : WithBot ℕ∞) →
    ∀ f : Fin (4 * g * g' + 1) → (A ⟶ B),
      ∃ c : Fin (4 * g * g' + 1) → ℤ, c ≠ 0 ∧ ∏ i, (f i).hom.hom ^ c i = 1

/-! ## 9. Glue proved from the leaves -/

section Glue

variable {K : Type u} [Field K]

lemma galAct_mul (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x y : Pts A L) : galAct A σ (x * y) = galAct A σ x * galAct A σ y :=
  MonObj.comp_mul _ _ _

lemma galAct_inv (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) : galAct A σ x⁻¹ = (galAct A σ x)⁻¹ :=
  GrpObj.comp_inv _ _

lemma galAct_pow (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (x : Pts A L) (n : ℕ) : galAct A σ (x ^ n) = (galAct A σ x) ^ n :=
  MonObj.comp_pow _ _ _

lemma galAct_one (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L] [Algebra K L]
    (σ : L ≃ₐ[K] L) : galAct A σ 1 = 1 :=
  MonObj.comp_one _

/-- **Glue C6/A8 (proved).** Good reduction at `O` makes inertia act trivially on `A[ℓⁿ]` for
every prime `ℓ` invertible in `O` (NOS, (a) ⇒ (b)): `r_ℓ` is unramified at such places. -/
theorem inertiaTrivial_of_goodReduction (hNOS : NeronOggShafarevich.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (hA : HasGoodReduction A O)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n : ℕ) :
    InertiaTrivialOn A w (ℓ ^ n) :=
  ((hNOS K O w hw A).1.mp hA) (ℓ ^ n) (pow_pos hℓ.pos n) (by
    rw [Nat.cast_pow]; exact hℓO.pow n)

/-- Algebraic core of D2 (proved): in a commutative group of points, if `σ` satisfies
`(σ - 1)² x = 0`, `x` has order dividing `ℓⁿ`, and `σ^{pᵃ} x = x` with `p` prime to `ℓ`,
then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate (A : Grp (Over (Spec (.of K)))) [IsCommMonObj A.X]
    {L : Type u} [CommRing L] [Algebra K L] (σ : L ≃ₐ[K] L) (x : Pts A L) (ℓ n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n)) (hx : x ∈ torsion A L (ℓ ^ n))
    (hu : UnipSq A σ x) (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  set N := galAct A σ x * x⁻¹ with hN
  have hσN : galAct A σ N = N := by
    rw [hN, galAct_mul, galAct_inv]
    unfold UnipSq at hu
    have h2 : galAct A σ (galAct A σ x) * (galAct A σ x)⁻¹ =
        ((galAct A σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (galAct A σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, galAct_mul, galAct_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (p ^ a) = 1 := by
    have := hiter (p ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    have hx' : x ^ (ℓ ^ n) = 1 := hx
    rw [hN, mul_pow, ← galAct_pow, hx', galAct_one, inv_pow, hx']; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue D2 (proved from Raynaud).** At a place of residue characteristic `p` where `A[m]` is
rational (`m ≥ 3` prime to `p`), every inertia element `σ` that acts on a point `x ∈ A[ℓⁿ]`
(`ℓ ≠ p`) with `p`-power order fixes it. Applied to wild inertia (pro-`p`, and the action on the
finite set `A[ℓⁿ]` factors through a finite quotient), this is D2's "wild inertia acts
trivially on `V_ℓ(A)`". The two facts in parentheses are I6/glue. -/
theorem D2_fixed_of_raynaud (hRay : RaynaudCriterion.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (m : ℕ) (hm : 3 ≤ m)
    (hmO : IsUnit (m : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) m, galAct A σ x = x)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hσ : IsInertia w σ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) (n p a : ℕ)
    (hcop : Nat.Coprime (p ^ a) (ℓ ^ n))
    (x : Pts A (AlgebraicClosure K)) (hx : x ∈ torsion A (AlgebraicClosure K) (ℓ ^ n))
    (hit : (galAct A σ)^[p ^ a] x = x) : galAct A σ x = x := by
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  exact fixed_of_unipSq_of_iterate A σ x ℓ n p a hcop hx
    (hRay K O w hw A m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx) hit

/-- **Glue A6 (Lemma PR(ii), Raynaud route; statement, proof outlined).** Let `A/K` be an
abelian surface with `K`-endomorphisms `I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` on
`K̄`-points (an action of `ℤ⟨i, j⟩ ⊂ B = (2,-3)`, maximal at 3), and with `A[3]` rational over `K`.
Then `A` has good reduction at every DVR `O` in which `3` is invertible.
Outline. (1) `RaynaudCriterion` with `m = ℓ = 3`: `N = σ - 1` has `N² = 0` on `A[3ⁿ]` for `σ` in
inertia. (2) `TorsionStructure` (`g = 2`): `A[3ⁿ] ≅ (ℤ/3ⁿ)⁴`; with the action of `Λ = ℤ⟨i,j⟩`,
whose 3-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`
(uniformizer `Π`, `Π² ∈ 3Λ₃ˣ`, residue field `𝔽₉`), a cardinality count gives `A[3ⁿ] ≅ Λ/3ⁿ`
free of rank one. (3) `N` commutes with `I, J` (defined over `K`), so `N` is right
multiplication by some `c`, and `N² = 0` gives `c² ≡ 0 mod 3^{2k}`, hence `c ∈ 3ᵏΛ` (the norm
form `x² - 2y² + 3z² - 6w²` is anisotropic mod 3), hence `N` kills `3ᵏ A[3^{2k}] = A[3ᵏ]`.
(4) `NeronOggShafarevich` (c) with `m = 3ᵏ`. -/
theorem goodReduction_of_QM_rational3 (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]
    (hdim : topologicalKrullDim A.X.left = ((2 : ℕ) : WithBot ℕ∞))
    (I J : A ⟶ A)
    (hI : ∀ x : Pts A (AlgebraicClosure K), (x ≫ I.hom.hom) ≫ I.hom.hom = x ^ 2)
    (hJ : ∀ x : Pts A (AlgebraicClosure K), (x ≫ J.hom.hom) ≫ J.hom.hom * x ^ 3 = 1)
    (hIJ : ∀ x : Pts A (AlgebraicClosure K),
      (x ≫ I.hom.hom) ≫ J.hom.hom * (x ≫ J.hom.hom) ≫ I.hom.hom = 1)
    (h3 : IsUnit (3 : O))
    (hrat : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ x ∈ torsion A (AlgebraicClosure K) 3, galAct A σ x = x) :
    HasGoodReduction A O := by
  sorry

end Glue

end PkgI2

end PkgI2Sec

section PkgI3Sec
/-! ### Copied from `scratch/pkg-I3/I3.lean` (compiled there). -/

noncomputable section

/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI3.Tate

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (M : Type*) [AddCommGroup M]

/-- `T_ℓ(M) = lim_n M[ℓⁿ]` (transition maps: multiplication by `ℓ`), realized as the
sequences `(xₙ)` with `x₀ = 0` and `ℓ • xₙ₊₁ = xₙ`; then `xₙ ∈ M[ℓⁿ]`. -/
def T : AddSubgroup (ℕ → M) where
  carrier := {x | x 0 = 0 ∧ ∀ n, ℓ • x (n + 1) = x n}
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨by simp [hx0, hy0], fun n => ?_⟩
    simp [smul_add, hx n, hy n]
  zero_mem' := ⟨rfl, fun n => by simp⟩
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    refine ⟨by simp [hx0], fun n => ?_⟩
    simp [hx n]

variable {ℓ M}

omit hℓ in
lemma pow_smul_eq_zero {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) : (ℓ ^ n) • x n = 0 := by
  induction n with
  | zero => simpa using hx.1
  | succ n ih => rw [pow_succ, mul_smul, hx.2 n, ih]

omit hℓ in
lemma nsmul_congr {y : M} {n : ℕ} (hy : (ℓ ^ n) • y = 0) {c d : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = (d : ZMod (ℓ ^ n))) : c • y = d • y := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.mod_add_div' c (ℓ ^ n), ← Nat.mod_add_div' d (ℓ ^ n), add_smul, add_smul,
    mul_smul, mul_smul, hy, smul_zero, smul_zero, h]

instance (n : ℕ) : NeZero (ℓ ^ n) := ⟨pow_ne_zero n hℓ.out.ne_zero⟩

lemma val_cast (a : ℤ_[ℓ]) (n : ℕ) :
    (((PadicInt.toZModPow (n + 1) a).val : ℕ) : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a := by
  rw [← PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) a, ZMod.natCast_val]

/-- The `ℤ_ℓ`-action: `(a • x)ₙ = (a mod ℓⁿ) • xₙ`. -/
def smulSeq (a : ℤ_[ℓ]) (x : ℕ → M) : ℕ → M :=
  fun n => (PadicInt.toZModPow n a).val • x n

lemma smulSeq_mem (a : ℤ_[ℓ]) {x : ℕ → M} (hx : x ∈ T ℓ M) : smulSeq a x ∈ T ℓ M := by
  refine ⟨by simp [smulSeq, hx.1], fun n => ?_⟩
  simp only [smulSeq]
  rw [smul_comm, hx.2 n]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [val_cast, ZMod.natCast_zmod_val]

lemma smulSeq_congr {x : ℕ → M} (hx : x ∈ T ℓ M) (n : ℕ) {a : ℤ_[ℓ]} {c : ℕ}
    (h : (c : ZMod (ℓ ^ n)) = PadicInt.toZModPow n a) : smulSeq a x n = c • x n := by
  simp only [smulSeq]
  apply nsmul_congr (pow_smul_eq_zero hx n)
  rw [ZMod.natCast_zmod_val, h]

instance : Module ℤ_[ℓ] (T ℓ M) where
  smul a x := ⟨smulSeq a x.1, smulSeq_mem a x.2⟩
  one_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 1 x.1 n = x.1 n
    rw [smulSeq_congr x.2 n (c := 1) (by simp), one_smul]
  mul_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a * b) x.1 n = smulSeq a (smulSeq b x.1) n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val * (PadicInt.toZModPow n b).val)
      (by push_cast; simp), mul_smul]
    rfl
  smul_zero a := Subtype.ext <| funext fun n => by
    change smulSeq a 0 n = 0
    simp [smulSeq]
  smul_add a x y := Subtype.ext <| funext fun n => by
    change smulSeq a (x.1 + y.1) n = smulSeq a x.1 n + smulSeq a y.1 n
    simp [smulSeq, smul_add]
  add_smul a b x := Subtype.ext <| funext fun n => by
    change smulSeq (a + b) x.1 n = smulSeq a x.1 n + smulSeq b x.1 n
    rw [smulSeq_congr x.2 n (c := (PadicInt.toZModPow n a).val + (PadicInt.toZModPow n b).val)
      (by push_cast; simp), add_smul]
    rfl
  zero_smul x := Subtype.ext <| funext fun n => by
    change smulSeq 0 x.1 n = 0
    simp [smulSeq]

@[simp] lemma smul_apply (a : ℤ_[ℓ]) (x : T ℓ M) (n : ℕ) :
    (a • x).1 n = (PadicInt.toZModPow n a).val • x.1 n := rfl

variable {N : Type*} [AddCommGroup N]

/-- Functoriality: a group homomorphism `M → N` induces a `ℤ_ℓ`-linear map `T_ℓ M → T_ℓ N`. -/
def map (φ : M →+ N) : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ N where
  toFun x := ⟨fun n => φ (x.1 n), by simp [x.2.1], fun n => by rw [← map_nsmul, x.2.2 n]⟩
  map_add' x y := Subtype.ext <| funext fun n => by simp
  map_smul' a x := Subtype.ext <| funext fun n => by simp [map_nsmul]

@[simp] lemma map_apply (φ : M →+ N) (x : T ℓ M) (n : ℕ) : (map φ x).1 n = φ (x.1 n) := rfl

end PkgI3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- An abelian variety over a field `K`: a group object in schemes over `Spec K` whose structure
morphism is proper, smooth and geometrically integral (Mumford §4, Milne 1986 §1). -/
structure AbVar (K : Type u) [Field K] where
  /-- the underlying `K`-scheme -/
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

namespace AbVar

variable {K : Type u} [Field K]

/-- Commutativity is a Mathlib theorem (Stacks 0BFD), not an assumption. -/
instance (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

/-- The dimension of `A` (Krull dimension of the underlying space). -/
def dim (A : AbVar K) : WithBot ℕ∞ := topologicalKrullDim A.X.left

/-- The homomorphisms `A → B` of group schemes over `K`, as a subgroup of the commutative group
of all `K`-morphisms `A → B` (pointwise product, `Hom.commGroup`). -/
def homGroup (A B : AbVar K) : Subgroup (A.X ⟶ B.X) where
  carrier := {f | IsMonHom f}
  one_mem' := by
    change IsMonHom (toUnit A.X ≫ η[B.X])
    infer_instance
  mul_mem' := by
    rintro f g (hf : IsMonHom f) (hg : IsMonHom g)
    change IsMonHom (lift f g ≫ μ[B.X])
    infer_instance
  inv_mem' := by
    rintro f (hf : IsMonHom f)
    change IsMonHom f⁻¹
    infer_instance

/-- `Hom_K(A, B)`, written additively (a `ℤ`-module). -/
abbrev Hom (A B : AbVar K) : Type u := Additive (homGroup A B)

/-- The underlying morphism of schemes. -/
def Hom.hom {A B : AbVar K} (f : Hom A B) : A.X ⟶ B.X := (Additive.toMul f).1

instance {A B : AbVar K} (f : Hom A B) : IsMonHom f.hom := (Additive.toMul f).2

lemma Hom.ext' {A B : AbVar K} {f g : Hom A B} (h : f.hom = g.hom) : f = g :=
  Additive.toMul.injective (Subtype.ext h)

/-- Package a homomorphism. -/
def Hom.mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] : Hom A B :=
  Additive.ofMul ⟨f, ‹_›⟩

@[simp] lemma Hom.hom_mk' {A B : AbVar K} (f : A.X ⟶ B.X) [IsMonHom f] :
    (Hom.mk' f).hom = f := rfl
@[simp] lemma Hom.hom_add {A B : AbVar K} (f g : Hom A B) : (f + g).hom = f.hom * g.hom := rfl
@[simp] lemma Hom.hom_zero {A B : AbVar K} : (0 : Hom A B).hom = 1 := rfl

/-- The endomorphism ring `End_K(A)`, with multiplication `f * g = f ∘ g`. -/
abbrev End (A : AbVar K) : Type u := Hom A A

instance (A : AbVar K) : Ring (End A) :=
  { (inferInstance : AddCommGroup (End A)) with
    mul := fun f g => Hom.mk' (g.hom ≫ f.hom)
    one := Hom.mk' (𝟙 _)
    mul_assoc := fun f g h => Hom.ext' (by simp [HMul.hMul, Mul.mul])
    one_mul := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    mul_one := fun f => Hom.ext' (by simp [HMul.hMul, Mul.mul, OfNat.ofNat, One.one])
    left_distrib := fun f g h => Hom.ext' (by
      change (g + h).hom ≫ f.hom = g.hom ≫ f.hom * h.hom ≫ f.hom
      simp [MonObj.mul_comp])
    right_distrib := fun f g h => Hom.ext' (by
      change h.hom ≫ (f + g).hom = h.hom ≫ f.hom * h.hom ≫ g.hom
      simp [MonObj.comp_mul])
    zero_mul := fun f => Hom.ext' (by
      change f.hom ≫ (1 : A.X ⟶ A.X) = 1
      simp)
    mul_zero := fun f => Hom.ext' (by
      change (1 : A.X ⟶ A.X) ≫ f.hom = 1
      simp) }

/-- The endomorphism algebra `End⁰_K(A) = ℚ ⊗ End_K(A)`. -/
abbrev End0 (A : AbVar K) : Type u := TensorProduct ℤ ℚ (End A)

/-- A morphism of `K`-schemes is an isogeny-type map: finite and surjective. -/
def IsIsogenyMor {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) : Prop :=
  IsFinite f.left ∧ Surjective f.left

/-! ### Points over a field extension and the Galois action -/

variable (L : Type u) [Field L] [Algebra K L]

/-- `Spec L` as a `K`-scheme. -/
def ptObj : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The group `A(L)` of `L`-points: `K`-morphisms `Spec L → A`. -/
abbrev Pt (A : AbVar K) : Type u := ptObj (K := K) L ⟶ A.X

variable {L}

/-- `σ ∈ Aut_K(L)` acting on `Spec L` over `K`. -/
def galHom (σ : L ≃ₐ[K] L) : ptObj (K := K) L ⟶ ptObj L :=
  Over.homMk (Spec.map (CommRingCat.ofHom (σ : L →+* L))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

lemma galHom_one : galHom (1 : L ≃ₐ[K] L) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) = 𝟙 (Spec (CommRingCat.of L))
  rw [show CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

lemma galHom_mul (σ τ : L ≃ₐ[K] L) : galHom (σ * τ) = galHom σ ≫ galHom τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp]
  congr 1

/-- The Galois action on `A(L)`: `σ • P = P ∘ Spec(σ)`, i.e. `σ` applied to coordinates. -/
def galAct (A : AbVar K) (σ : L ≃ₐ[K] L) : A.Pt L →* A.Pt L where
  toFun P := galHom σ ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

/-- A homomorphism `f : A → B` acting on `L`-points. -/
def ptMap {A B : AbVar K} (f : Hom A B) : A.Pt L →* B.Pt L := IsMonHom.monoidHom f.hom _

/-! ### `T_ℓ(A)`, `V_ℓ(A)` and the Galois representation -/

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) = lim A(K̄)[ℓⁿ]`, a `ℤ_ℓ`-module. -/
abbrev T (A : AbVar K) : Type u := Tate.T ℓ (Additive (A.Pt (AlgebraicClosure K)))

/-- `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)`. -/
abbrev V (A : AbVar K) : Type u := TensorProduct ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ)

variable {ℓ}

/-- Galois action on `T_ℓ(A)`. -/
def galT (A : AbVar K) (σ : Field.absoluteGaloisGroup K) : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ :=
  Tate.map (MonoidHom.toAdditive (A.galAct σ))

/-- A homomorphism acting on Tate modules. -/
def homT {A B : AbVar K} (f : Hom A B) : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ :=
  Tate.map (MonoidHom.toAdditive (ptMap f))

/-- Galois-equivariance of a `ℤ_ℓ`-linear map of Tate modules. -/
def IsGalEquivariant {A B : AbVar K} (φ : A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) : Prop :=
  ∀ (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ), φ (A.galT σ x) = B.galT σ (φ x)

variable (ℓ)

/-- The Galois representation `ρ_ℓ : G_K → GL(V_ℓ(A))`. -/
def galRep (A : AbVar K) : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ) where
  toFun σ := (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ]
  map_one' := by
    have : A.galT (ℓ := ℓ) 1 = LinearMap.id := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      change Additive.ofMul (galHom (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = x.1 n
      rw [galHom_one, Category.id_comp]; rfl
    change (A.galT (ℓ := ℓ) 1).baseChange ℚ_[ℓ] = LinearMap.id
    rw [this, LinearMap.baseChange_id]
  map_mul' σ τ := by
    have : A.galT (ℓ := ℓ) (σ * τ) = A.galT σ ∘ₗ A.galT τ := by
      apply LinearMap.ext; intro x; apply Subtype.ext; funext n
      have h := galHom_mul (K := K) (L := AlgebraicClosure K) σ τ
      change Additive.ofMul (galHom (σ * τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) ≫
        Additive.toMul (x.1 n)) = Additive.ofMul (galHom σ ≫ galHom τ ≫ Additive.toMul (x.1 n))
      exact (congrArg (fun g => Additive.ofMul (g ≫ Additive.toMul (x.1 n))) h).trans
        (by rw [Category.assoc])
    change (A.galT (ℓ := ℓ) (σ * τ)).baseChange ℚ_[ℓ] =
      (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ (A.galT τ).baseChange ℚ_[ℓ]
    rw [this, LinearMap.baseChange_comp]

/-- The action of `Hom(A, B)` on Tate modules, as a group homomorphism. -/
def tateHom (A B : AbVar K) : Hom A B →+ (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) where
  toFun f := homT f
  map_zero' := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom]
  map_add' f g := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    simp [homT, ptMap, IsMonHom.monoidHom, MonObj.comp_mul]

/-- The `ℤ_ℓ`-linear extension `ℤ_ℓ ⊗_ℤ Hom(A, B) → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)`, `a ⊗ f ↦ a · T_ℓ(f)`. -/
def tateHomZl (A B : AbVar K) :
    TensorProduct ℤ ℤ_[ℓ] (Hom A B) →ₗ[ℤ] (A.T ℓ →ₗ[ℤ_[ℓ]] B.T ℓ) :=
  TensorProduct.lift
    (LinearMap.mk₂ ℤ (fun (a : ℤ_[ℓ]) (f : Hom A B) => a • tateHom ℓ A B f)
      (fun a b f => add_smul a b _)
      (fun n a f => by rw [smul_assoc])
      (fun a f g => by rw [map_add, smul_add])
      (fun n a f => by rw [map_zsmul, smul_comm]))

end AbVar

end PkgI3

/-! ### Base change -/

namespace PkgI3.AbVar

open CategoryTheory AlgebraicGeometry Limits

variable {K : Type} [Field K]

/-- Base change `A_L` along a field extension `L/K` (Mathlib's `Over.pullback`; the group
structure is transported by the monoidal functor `Over.pullback`). -/
def baseChange (A : AbVar K) (L : Type) [Field L] [Algebra K L] : AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

instance geometricallyIntegral_id_spec (K : Type) [Field K] :
    GeometricallyIntegral (𝟙 (Spec (CommRingCat.of K))) := by
  constructor
  intro L _ y Z fst snd h
  have : IsIso snd := h.isIso_snd_of_isIso
  have : Nonempty Z := ⟨(inv snd) (IsLocalRing.closedPoint L)⟩
  exact isIntegral_of_isOpenImmersion snd

open MonoidalCategory in
/-- Sanity check: `AbVar K` is inhabited (by `Spec K`, the zero abelian variety). No
nonzero abelian variety can be constructed in Mathlib v4.35.0: it has no projective group
scheme (Weierstrass curves exist only as point sets, not as `GrpObj`s in `Over (Spec K)`). -/
def zero (K : Type) [Field K] : AbVar K :=
  haveI : IsProper (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (𝟙_ (Over (Spec (CommRingCat.of K)))).hom := by
    dsimp; infer_instance
  { X := 𝟙_ (Over (Spec (CommRingCat.of K))) }

end PkgI3.AbVar

/-! ## 3. The leaves of package I3

Each leaf is a `Prop` quantified over all fields (resp. number fields) and all abelian varieties
in the sense of `AbVar`; universe `0`. Locators: see `docs/research/pkg-I3.md`. -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped Quaternion TensorProduct

/-- Every nonzero endomorphism is an isogeny (equivalently `End⁰(A)` is a division algebra);
in characteristic `0` this is equivalent to `A` being simple (Mumford §19, Thm 1 and Cor. 2). -/
def EndDivision {k : Type} [Field k] (A : AbVar k) : Prop :=
  ∀ f : End A, f ≠ 0 → IsIsogenyMor f.hom

/-- **I3.F1 — Faltings 1983, Satz 3 (semisimplicity).** For an abelian variety `A` over a number
field `K` and a prime `ℓ`, the representation of `G_K` on `V_ℓ(A)` is semisimple. -/
def FaltingsSemisimple : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    (A.galRep ℓ).IsSemisimpleRepresentation

/-- **I3.F2 — Faltings 1983, Satz 4 (`A = B`) and Korollar 1 (Tate's conjecture).** For abelian
varieties `A, B` over a number field `K` and a prime `ℓ`, the natural map
`Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective with image the `G_K`-equivariant maps. -/
def FaltingsTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    Function.Injective (tateHomZl ℓ A B) ∧
      Set.range (tateHomZl ℓ A B) = {φ | IsGalEquivariant φ}

/-- **I3.M0 — structure of the Tate module (Mumford §4, `A[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n`;
§18-19).** For `ℓ ≠ char k`, `T_ℓ(A)` is free of rank `2 dim A` over `ℤ_ℓ`. -/
def TateModuleFree : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    Module.Free ℤ_[ℓ] (A.T ℓ) ∧ Module.Finite ℤ_[ℓ] (A.T ℓ) ∧
      ((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ∞) : WithBot ℕ∞) = 2 * A.dim

/-- **I3.M1 — Mumford §19, Thm 3.** `Hom(A, B)` is a free `ℤ`-module of finite rank
`≤ 4 dim A dim B`, and for `ℓ ≠ char k` the map `Hom(A, B) ⊗ ℤ_ℓ → Hom(T_ℓ A, T_ℓ B)` is injective. -/
def HomFreeFinite : Prop :=
  ∀ (k : Type) [Field k] (A B : AbVar k),
    Module.Free ℤ (Hom A B) ∧ Module.Finite ℤ (Hom A B) ∧
      ((Module.finrank ℤ (Hom A B) : ℕ∞) : WithBot ℕ∞) ≤ 4 * A.dim * B.dim ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 → Function.Injective (tateHomZl ℓ A B)

/-- **I3.M2 — Mumford §19, Thm 4 (independence of `ℓ`).** For `φ ∈ End(A)` there is a monic
`P ∈ ℤ[X]` that is the characteristic polynomial of `V_ℓ(φ)` for every prime `ℓ ≠ char k`
(computed in any finite basis). -/
def CharPolyIndepOfEll : Prop :=
  ∀ (k : Type) [Field k] (A : AbVar k) (φ : End A), ∃ P : ℤ[X], P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

/-- **I3.M3 — Poincaré complete reducibility (Mumford §19, Thm 1), in the form used at E1.**
Over a field of characteristic `0`, if `End⁰(A)` is a division algebra and `f : A → J` is a
nonzero homomorphism, there are an abelian variety `Z` and a homomorphism `g : Z → J` such that
`(f, g) : A × Z → J`, `(a, z) ↦ f(a) + g(z)`, is an isogeny. -/
def PoincareReducibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : AbVar k), EndDivision A →
    ∀ f : Hom A J, f ≠ 0 → ∃ (Z : AbVar k) (g : Hom Z J),
      IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)

/-- **I3.Q — the QM dichotomy (step A9).** Over an algebraically closed field of characteristic
`0`, if a quaternion division algebra `B = (a, b)_ℚ` embeds in `End⁰(A)` for an abelian surface
`A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))` with `d < 0`. (Consequence of Mumford §19
Thm 1, Cor. 2, §21 (Albert, `[D:ℚ] ∣ 2g` in characteristic `0`) and §22; see the note.) -/
def QMDichotomy : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomy

end PkgI3

/-! ## 4. Glue checks: the leaves are usable with these definitions -/

namespace PkgI3

open CategoryTheory AlgebraicGeometry MonObj AbVar
open scoped TensorProduct

/-- The easy half of Faltings' statement holds outright: the image of `Hom(A, B) ⊗ ℤ_ℓ`
consists of Galois-equivariant maps. (So `FaltingsTate` asserts injectivity and the reverse
inclusion, as in the published statement.) -/
lemma homT_galT {K : Type} [Field K] {A B : AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (f : Hom A B)
    (σ : Field.absoluteGaloisGroup K) (x : A.T ℓ) :
    homT f (A.galT σ x) = B.galT σ (homT f x) := by
  apply Subtype.ext; funext n
  change Additive.ofMul ((galHom σ ≫ Additive.toMul (x.1 n)) ≫ f.hom) =
    Additive.ofMul (galHom σ ≫ (Additive.toMul (x.1 n) ≫ f.hom))
  rw [Category.assoc]

theorem range_tateHomZl_subset {K : Type} [Field K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Set.range (tateHomZl ℓ A B) ⊆ {φ | IsGalEquivariant φ} := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => intro σ x; simp
  | tmul a f =>
    intro σ x
    have e : tateHomZl ℓ A B (a ⊗ₜ f) = a • tateHom ℓ A B f := rfl
    rw [e, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    exact congrArg (a • ·) (homT_galT f σ x)
  | add y z hy hz =>
    intro σ x
    simp only [map_add, LinearMap.add_apply, hy σ x, hz σ x]

/-- **Glue for E1.** From Faltings' theorem and the structure of `T_ℓ`: a nonzero
`G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ(A) → V_ℓ(B)` forces a nonzero homomorphism `A → B`. -/
theorem exists_hom_ne_zero_of_equivariant (hF : FaltingsTate) (hT : TateModuleFree)
    {K : Type} [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (φ : A.V ℓ →ₗ[ℚ_[ℓ]] B.V ℓ) (hφ : φ ≠ 0)
    (heq : ∀ σ, φ ∘ₗ A.galRep ℓ σ = B.galRep ℓ σ ∘ₗ φ) : ∃ f : Hom A B, f ≠ 0 := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨hfreeB, -, -⟩ := hT K B ℓ hℓK
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let ιA : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  let ιB : B.T ℓ →ₗ[ℤ_[ℓ]] B.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (B.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) ιB := inferInstance
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (nonZeroDivisors ℤ_[ℓ]) ιB ((φ.restrictScalars ℤ_[ℓ]) ∘ₗ ιA)
  have hs0 : (s : ℤ_[ℓ]) ≠ 0 := nonZeroDivisors.ne_zero s.2
  -- `ιB` is injective (`T_ℓ B` is free, hence torsion-free).
  have hιB : Function.Injective ιB := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) ιB).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  -- the Galois actions commute with `ι`
  have hιAσ : ∀ σ x, ιA (A.galT σ x) = A.galRep ℓ σ (ιA x) := fun σ x => by
    simp [ιA, galRep, LinearMap.baseChange_tmul]
  have hιBσ : ∀ σ x, ιB (B.galT σ x) = B.galRep ℓ σ (ιB x) := fun σ x => by
    simp [ιB, galRep, LinearMap.baseChange_tmul]
  have hsφ : ∀ x, ιB (h x) = (s : ℤ_[ℓ]) • φ (ιA x) := fun x => by
    have := congrArg (fun g => g x) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
    exact this
  -- `h` is equivariant
  have hheq : IsGalEquivariant h := by
    intro σ x
    apply hιB
    rw [hsφ, hιAσ, hιBσ, hsφ]
    have := congrArg (fun g => g (ιA x)) (heq σ)
    simp only [LinearMap.coe_comp, Function.comp_apply] at this
    rw [this, LinearMap.map_smul_of_tower]
  -- `h ≠ 0`
  have hh0 : h ≠ 0 := by
    intro h0
    apply hφ
    have hφι : ∀ x, φ (ιA x) = 0 := fun x => by
      have h1 : (s : ℤ_[ℓ]) • φ (ιA x) = 0 := by rw [← hsφ, h0]; simp
      rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ])] at h1
      exact (smul_eq_zero.mp h1).resolve_left (by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne hs0)
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q x =>
      have : (q ⊗ₜ[ℤ_[ℓ]] x : A.V ℓ) = q • ιA x := by simp [ιA, TensorProduct.smul_tmul']
      rw [this, map_smul, hφι, smul_zero, LinearMap.zero_apply]
    | add v w hv hw => simp [map_add, hv, hw]
  -- conclude with Faltings
  obtain ⟨z, hz⟩ : h ∈ Set.range (tateHomZl ℓ A B) := by
    rw [(hF K A B ℓ).2]; exact hheq
  by_contra hall
  simp only [ne_eq, not_exists, not_not] at hall
  have : Subsingleton (Hom A B) := ⟨fun f g => (hall f).trans (hall g).symm⟩
  have : z = 0 := Subsingleton.elim _ _
  exact hh0 (by rw [← hz, this, map_zero])

/-- The `G_K`-equivariant `ℚ_ℓ`-linear endomorphisms of `V_ℓ(A)`. -/
def equivEnd {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Submodule ℚ_[ℓ] (Module.End ℚ_[ℓ] (A.V ℓ)) where
  carrier := {φ | ∀ σ, φ ∘ₗ A.galRep ℓ σ = A.galRep ℓ σ ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ σ, hψ σ]
  zero_mem' := by intro σ; simp
  smul_mem' := by
    intro c φ hφ σ
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ σ]

/-- **Glue for C2 (GLUE, proved).** The `ℚ_ℓ`-form of Satz 4:
`dim_{ℚ_ℓ} End_{G_K}(V_ℓ A) = rank_ℤ End_K(A)`. With `FaltingsSemisimple` and
`End⁰_K(A) ≅ B` (A9, A10, and `L'` defining every geometric endomorphism), the commutant
argument of N5 L731-734 then gives absolute irreducibility of `r_ℓ`.
Proof: `T_ℓ A` is free of finite rank (`TateModuleFree`), so every `φ ∈ End(V_ℓ A)`
has `ℓᵏφ(T_ℓ A) ⊆ T_ℓ A`; equivariance passes to `T_ℓ A` because `T_ℓ A → V_ℓ A` is injective
(as in `exists_hom_ne_zero_of_equivariant`); so `End_G(V) = ℚ_ℓ ⊗ End_G(T)`, and
`End_G(T) ≅ ℤ_ℓ ⊗ End(A)` (`FaltingsTate`) is free of rank `rank_ℤ End(A)` (`HomFreeFinite`). -/
theorem finrank_equivEnd (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.finrank ℚ_[ℓ] (equivEnd A ℓ) = Module.finrank ℤ (End A) := by
  classical
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, -⟩ := hT K A ℓ hℓK
  obtain ⟨hHfree, hHfin, -, -⟩ := hH K A A
  have : Module.FinitePresentation ℤ_[ℓ] (A.T ℓ) := Module.finitePresentation_of_finite _ _
  let jT : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) jT := inferInstance
  have hj : Function.Injective jT := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[ℓ]) jT).mp hy
    exact (smul_eq_zero.mp ht).resolve_left (nonZeroDivisors.ne_zero t.2)
  have hjσ : ∀ σ x, jT (A.galT σ x) = A.galRep ℓ σ (jT x) := fun σ x => by
    simp [jT, galRep, LinearMap.baseChange_tmul]
  have hjψ : ∀ (ψ : Module.End ℤ_[ℓ] (A.T ℓ)) x, jT (ψ x) = ψ.baseChange ℚ_[ℓ] (jT x) :=
    fun ψ x => by simp [jT, LinearMap.baseChange_tmul]
  -- the equivariant endomorphisms of `T_ℓ A`
  let ET : Submodule ℤ_[ℓ] (Module.End ℤ_[ℓ] (A.T ℓ)) :=
    { carrier := {ψ | IsGalEquivariant ψ}
      add_mem' := fun {ψ χ} hψ hχ σ x => by
        simp only [LinearMap.add_apply, map_add, hψ σ x, hχ σ x]
      zero_mem' := fun σ x => by simp
      smul_mem' := fun c ψ hψ σ x => by
        simp only [LinearMap.smul_apply, map_smul, hψ σ x] }
  -- Step 1: `ET ≅ ℤ_ℓ ⊗ End A` (Faltings), so `rank ET = rank End A`.
  have hsmul : ∀ (a : ℤ_[ℓ]) z, tateHomZl ℓ A A (a • z) = a • tateHomZl ℓ A A z := by
    intro a z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        show tateHomZl ℓ A A ((a * b) ⊗ₜ f) = (a * b) • tateHom ℓ A A f from rfl,
        show tateHomZl ℓ A A (b ⊗ₜ f) = b • tateHom ℓ A A f from rfl, mul_smul]
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  let L1 : TensorProduct ℤ ℤ_[ℓ] (End A) →ₗ[ℤ_[ℓ]] ET :=
    { toFun := fun z => ⟨tateHomZl ℓ A A z, range_tateHomZl_subset A A ℓ ⟨z, rfl⟩⟩
      map_add' := fun y z => Subtype.ext (map_add _ y z)
      map_smul' := fun a z => Subtype.ext (hsmul a z) }
  have hL1 : Function.Bijective L1 := by
    refine ⟨fun y z h => (hF K A A ℓ).1 (congrArg Subtype.val h), fun ψ => ?_⟩
    obtain ⟨z, hz⟩ : ψ.1 ∈ Set.range (tateHomZl ℓ A A) := by
      rw [(hF K A A ℓ).2]; exact ψ.2
    exact ⟨z, Subtype.ext hz⟩
  have h1 : Module.finrank ℤ_[ℓ] ET = Module.finrank ℤ (End A) := by
    rw [← (LinearEquiv.ofBijective L1 hL1).finrank_eq, Module.finrank_baseChange]
  -- Step 2: `equivEnd A ℓ` is the localization of `ET`.
  let Φ : ET →ₗ[ℤ_[ℓ]] equivEnd A ℓ :=
    { toFun := fun ψ => ⟨ψ.1.baseChange ℚ_[ℓ], fun σ => by
        change ψ.1.baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
          (A.galT σ).baseChange ℚ_[ℓ] ∘ₗ ψ.1.baseChange ℚ_[ℓ]
        rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
        congr 1
        exact LinearMap.ext fun x => ψ.2 σ x⟩
      map_add' := fun ψ χ => Subtype.ext (LinearMap.baseChange_add _ _)
      map_smul' := fun c ψ => Subtype.ext (LinearMap.baseChange_smul _ _) }
  have hΦ : IsLocalizedModule (nonZeroDivisors ℤ_[ℓ]) Φ := by
    constructor
    · intro s
      have hc : algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]) ≠ 0 := by
        simpa using (IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]).ne (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro x y hxy
        simp only [Module.algebraMap_end_apply] at hxy
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) x, ← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]) y] at hxy
        exact smul_right_injective _ hc hxy
      · intro y
        refine ⟨(algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ]))⁻¹ • y, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), smul_smul, mul_inv_cancel₀ hc, one_smul]
    · intro φ
      obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
        (nonZeroDivisors ℤ_[ℓ]) jT ((φ.1.restrictScalars ℤ_[ℓ]) ∘ₗ jT)
      have hsφ : ∀ x, jT (h x) = (s : ℤ_[ℓ]) • φ.1 (jT x) := fun x => by
        have := congrArg (fun g => g x) hs
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
          LinearMap.coe_restrictScalars, Submonoid.smul_def] at this
        exact this
      have hheq : IsGalEquivariant h := by
        intro σ x
        apply hj
        rw [hsφ, hjσ, hjσ, hsφ]
        have := congrArg (fun g => g (jT x)) (φ.2 σ)
        simp only [LinearMap.coe_comp, Function.comp_apply] at this
        rw [this, LinearMap.map_smul_of_tower]
      refine ⟨⟨⟨h, hheq⟩, s⟩, Subtype.ext ?_⟩
      apply TensorProduct.AlgebraTensorModule.curry_injective
      apply LinearMap.ext_ring
      apply LinearMap.ext
      intro x
      change (s : ℤ_[ℓ]) • φ.1 ((1 : ℚ_[ℓ]) ⊗ₜ x) = h.baseChange ℚ_[ℓ] ((1 : ℚ_[ℓ]) ⊗ₜ x)
      exact (hsφ x).symm.trans (hjψ h x)
    · intro ψ χ hψχ
      refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      apply hj
      rw [hjψ, hjψ]
      exact congrArg (fun g => g (jT x)) (congrArg Subtype.val hψχ)
  have e1 := IsLocalization.finrank_eq (R := ℤ_[ℓ]) (N := equivEnd A ℓ) ℚ_[ℓ]
    (nonZeroDivisors ℤ_[ℓ]) le_rfl
  have e2 := IsLocalizedModule.finrank_eq (M := ET) (N := equivEnd A ℓ) (p := nonZeroDivisors ℤ_[ℓ]) (f := Φ) le_rfl
  rw [e1, e2, h1]

end PkgI3

end
end PkgI3Sec

section PkgI6Sec
/-! ### Copied from `scratch/pkg-I6/I6.lean` (compiled there). -/

/-!
# pkg-I6: arithmetic of `ℚ` and of local fields (steps B1, B2, C10, D1, D3, D4 of h-trust)

Leaves are `def … : Prop` over genuine Mathlib objects.  Each carries its published locator
(locators from memory are UNVERIFIED; see `docs/research/pkg-I6.md`).  Definitions that Mathlib
lacks (lower and upper ramification groups, Herbrand's function, the Artin conductor of a
representation of a finite group) are given concretely in Part II.

Part I  (global):  Skolem–Noether, the 2-torsion of the Brauer sequence of `ℚ` in Galois-cohomology
                   form, local Kronecker–Weber, Chebotarev, Brauer–Nesbitt.
Part II (local):   ramification groups, Serre's bound for the different, Hilbert's formula,
                   Herbrand's theorem, transitivity of `φ`, the Artin conductor, local class field
                   theory with the upper numbering theorem.
-/

open CategoryTheory

namespace PkgI6

/-! ## Part I. Global inputs -/

section SkolemNoether

/-- **Leaf I6.1 (Skolem–Noether).** Let `A` be a finite-dimensional central simple algebra over a
field `K` and `B` a simple `K`-algebra.  Any two `K`-algebra maps `B → A` are conjugate by a unit
of `A`.  Reiner, *Maximal orders* (1975), Thm 7.21; Farb–Dennis, *Noncommutative algebra*,
Thm 3.14 (both UNVERIFIED).  B1 uses the special case `B = A` (`skolemNoether_aut`). -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ u : Aˣ, ∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A)

/-- The form used in B1: every `K`-algebra automorphism of a finite-dimensional central simple
algebra is inner.  GLUE (proved from the leaf). -/
theorem skolemNoether_aut (h : SkolemNoether) (K A : Type) [Field K] [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (σ : A ≃ₐ[K] A) :
    ∃ u : Aˣ, ∀ a : A, σ a = (u : A) * a * ((u⁻¹ : Aˣ) : A) := by
  obtain ⟨u, hu⟩ := h K A A (AlgHom.id K A) σ.toAlgHom
  exact ⟨u, fun a => by simpa using hu a⟩

end SkolemNoether

section Brauer

/-- The trivial `G_ℚ`-module `ℤ/2 = {±1}`, as a topological representation over `ℤ` (discrete
topology on `ZMod 2`). -/
noncomputable abbrev Z2 (K : Type) [Field K] : TopRep ℤ (Field.absoluteGaloisGroup K) :=
  TopRep.of (ContRepresentation.trivial ℤ (Field.absoluteGaloisGroup K) (ZMod 2))

/-- The localization map `H^n(G_ℚ, ℤ/2) → H^n(G_F, ℤ/2)` for a field `F` with a ring map
`ℚ → F` (Mathlib's `Field.absoluteGaloisGroup.map`, which depends on a choice of embedding of
algebraic closures; the induced map on cohomology does not, since conjugation acts trivially on
cohomology). -/
noncomputable abbrev loc (F : Type) [Field F] [Algebra ℚ F] (n : ℕ) :
    continuousCohomology n (Z2 ℚ) ⟶
      continuousCohomology n
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ F) :
          Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ)) :=
  ContinuousCohomology.map (Field.absoluteGaloisGroup.map (algebraMap ℚ F)) (𝟙 _) n

/-- `loc_p`: localization at the prime `p`. -/
noncomputable abbrev locP (p : ℕ) [Fact p.Prime] := loc ℚ_[p] 2

/-- `loc_∞`: localization at the real place. -/
noncomputable abbrev locInf := loc ℝ 2

/-- **Leaf I6.2a (Albert–Brauer–Hasse–Noether, 2-torsion, Galois-cohomology form).**
`H²(G_ℚ, ℤ/2) → ∏_v H²(G_{ℚ_v}, ℤ/2)` is injective: `Ш²(ℚ, ℤ/2) = 0` over all places.
This is the injectivity of `Br ℚ → ⊕_v Br ℚ_v` (Milne, ADT, Ch. I, Thm 4.? / Neukirch–Schmidt–
Wingberg (8.1.17); Tate in Cassels–Fröhlich VII §11.2: UNVERIFIED locators) composed with the
Kummer isomorphism `H²(G_K, μ₂) ≅ Br(K)[2]` (Hilbert 90; Serre, *Corps locaux* X §4–5), which is
natural in `K`. -/
def BrauerHasse2 : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    locInf.hom x = 0 → (∀ (p : ℕ) [Fact p.Prime], (locP p).hom x = 0) → x = 0

open Classical in
/-- **Leaf I6.2b (reciprocity, 2-torsion form).** For `x ∈ H²(G_ℚ, ℤ/2)` the set of places where
`x` is locally nonzero is finite and has even cardinality.  This is `∑_v inv_v = 0` together with
`inv_v(x) ∈ {0, 1/2}` and `inv_v` injective (Milne ADT Ch. I; Serre, *Corps locaux* XIII §3 for
`Br ℚ_p ≅ ℚ/ℤ`; UNVERIFIED locators). -/
def BrauerReciprocity2 : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.ncard
      + if locInf.hom x = 0 then 0 else 1)

/-- **Leaf I6.2c (local `H²`).** `H²(G_{ℚ_p}, ℤ/2) ≅ Br(ℚ_p)[2] ≅ ℤ/2` and
`H²(G_ℝ, ℤ/2) ≅ Br(ℝ) ≅ ℤ/2`: each has exactly two elements.  (Serre, *Corps locaux* XIII §3,
Prop. 6 and X §5; UNVERIFIED locators.) Stated for the restricted module that `loc` lands in. -/
def LocalH2Card : Prop :=
  (∀ (p : ℕ) [Fact p.Prime],
      Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
          Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2) ∧
    Nat.card (continuousCohomology 2
        (TopRep.res (Field.absoluteGaloisGroup.map (algebraMap ℚ ℝ) :
          Field.absoluteGaloisGroup ℝ →* Field.absoluteGaloisGroup ℚ) (Z2 ℚ))) = 2

lemma eq_of_ne_zero_of_card_two {G : Type*} [AddGroup G] (h : Nat.card G = 2) {a b : G}
    (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by
  obtain ⟨x, y, -, hu⟩ := Nat.card_eq_two_iff.mp h
  have mem : ∀ z : G, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set G) := hu ▸ Set.mem_univ z
    simpa using this
  rcases mem 0 with h0 | h0 <;> rcases mem a with h1 | h1 <;> rcases mem b with h2 | h2 <;>
    first
    | exact h1.trans h2.symm
    | exact absurd (h1.trans h0.symm) ha
    | exact absurd (h2.trans h0.symm) hb

/-- **The Brauer step of B2 (GLUE, proved from I6.2a-c).** Two classes in `H²(G_ℚ, ℤ/2)` that are
locally nonzero at exactly the same primes are equal (agreement at `∞` comes from reciprocity).
In N5 L683-692 the classes are `[ε]` and the boundary `δχ`. -/
theorem eq_of_same_finite_support (hH : BrauerHasse2) (hR : BrauerReciprocity2)
    (hC : LocalH2Card) (x y : continuousCohomology 2 (Z2 ℚ))
    (h : ∀ (p : ℕ) [Fact p.Prime], (locP p).hom x = 0 ↔ (locP p).hom y = 0) : x = y := by
  have hp : ∀ (p : ℕ) [Fact p.Prime], (locP p).hom (x - y) = 0 := by
    intro p _
    rw [map_sub, sub_eq_zero]
    by_cases hx : (locP p).hom x = 0
    · rw [hx, ((h p).mp hx)]
    · exact eq_of_ne_zero_of_card_two (hC.1 p) hx (fun hy => hx ((h p).mpr hy))
  have hinf : locInf.hom (x - y) = 0 := by
    obtain ⟨-, hev⟩ := hR (x - y)
    have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
        (locP (q : ℕ)).hom (x - y) ≠ 0} = ∅ := by
      ext q
      have : Fact (q : ℕ).Prime := ⟨q.2⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hp q
    rw [hempty, Set.ncard_empty, zero_add] at hev
    by_contra hne
    rw [if_neg hne] at hev
    exact Nat.not_even_one hev
  exact sub_eq_zero.mp (hH (x - y) hinf hp)

/-! ### The same three leaves at the level of continuous inhomogeneous cochains

Galois cohomology is classically *defined* by continuous inhomogeneous cochains (Serre,
*Cohomologie galoisienne*, I §2.2), and that is how N5 manipulates `ε` (a function
`G_ℚ × G_ℚ → {±1}`).  These forms need no comparison with Mathlib's resolution-defined
`continuousCohomology` (Mathlib describes only `H⁰` explicitly, `LowDegree.lean`). -/

/-- A continuous inhomogeneous 2-cocycle with values in the trivial module `ℤ/2`. -/
def IsCocycle2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  Continuous (fun x : G × G => ε x.1 x.2) ∧ ∀ a b c, ε b c - ε (a * b) c + ε a (b * c) - ε a b = 0

/-- `ε` is the coboundary of a continuous 1-cochain. -/
def IsCoboundary2 {G : Type*} [Group G] [TopologicalSpace G] (ε : G → G → ZMod 2) : Prop :=
  ∃ f : G → ZMod 2, Continuous f ∧ ∀ a b, ε a b = f b - f (a * b) + f a

/-- Restriction of a cochain on `G_ℚ` to `G_F` along Mathlib's map `G_F → G_ℚ`. -/
noncomputable def resC (F : Type) [Field F] [Algebra ℚ F] (ε : Field.absoluteGaloisGroup ℚ →
    Field.absoluteGaloisGroup ℚ → ZMod 2) :
    Field.absoluteGaloisGroup F → Field.absoluteGaloisGroup F → ZMod 2 :=
  fun a b => ε (Field.absoluteGaloisGroup.map (algebraMap ℚ F) a)
    (Field.absoluteGaloisGroup.map (algebraMap ℚ F) b)

/-- **Leaf I6.2a′** (= I6.2a on cochains). -/
def BrauerHasse2C : Prop :=
  ∀ ε, IsCocycle2 ε → IsCoboundary2 (resC ℝ ε) →
    (∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) → IsCoboundary2 ε

open Classical in
/-- **Leaf I6.2b′** (= I6.2b on cochains). -/
def BrauerReciprocity2C : Prop :=
  ∀ ε, IsCocycle2 ε →
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(p : ℕ)] ε)}.ncard
      + if IsCoboundary2 (resC ℝ ε) then 0 else 1)

/-- `H²(G, ℤ/2)` has exactly two elements, on cochains: a non-trivial class exists, and any two
non-trivial classes differ by a coboundary. -/
def H2TwoClasses (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  (∃ ε, IsCocycle2 (G := G) ε ∧ ¬ IsCoboundary2 ε) ∧
  ∀ ε₁ ε₂, IsCocycle2 (G := G) ε₁ → IsCocycle2 ε₂ → ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ →
    IsCoboundary2 (ε₁ - ε₂)

/-- **Leaf I6.2c′** (= I6.2c on cochains). -/
def LocalH2CardC : Prop :=
  (∀ (p : ℕ) [Fact p.Prime], H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p])) ∧
    H2TwoClasses (Field.absoluteGaloisGroup ℝ)

lemma IsCoboundary2.sub {G : Type*} [Group G] [TopologicalSpace G] {ε₁ ε₂ : G → G → ZMod 2}
    (h₁ : IsCoboundary2 ε₁) (h₂ : IsCoboundary2 ε₂) : IsCoboundary2 (ε₁ - ε₂) := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ - f₂, hf₁.sub hf₂, fun a b => ?_⟩
  simp only [Pi.sub_apply, e₁, e₂]; ring

lemma IsCocycle2.sub {G : Type*} [Group G] [TopologicalSpace G] {ε₁ ε₂ : G → G → ZMod 2}
    (h₁ : IsCocycle2 ε₁) (h₂ : IsCocycle2 ε₂) : IsCocycle2 (ε₁ - ε₂) := by
  refine ⟨h₁.1.sub h₂.1, fun a b c => ?_⟩
  have := h₁.2 a b c
  have := h₂.2 a b c
  simp only [Pi.sub_apply]
  linear_combination h₁.2 a b c - h₂.2 a b c

lemma IsCocycle2.resC {ε} (h : IsCocycle2 ε) (F : Type) [Field F] [Algebra ℚ F] :
    IsCocycle2 (resC F ε) := by
  refine ⟨?_, fun a b c => ?_⟩
  · have hφ := (Field.absoluteGaloisGroup.map (algebraMap ℚ F)).continuous
    exact h.1.comp ((hφ.comp continuous_fst).prodMk (hφ.comp continuous_snd))
  · simp only [PkgI6.resC, map_mul]
    exact h.2 _ _ _

/-- **The Brauer step of B2 on cochains (GLUE, proved from I6.2a′-c′).**  Two continuous
2-cocycles on `G_ℚ` with values in `ℤ/2` that are locally non-trivial at the same primes differ by
a continuous coboundary. -/
theorem cob_of_same_finite_support (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) (ε₁ ε₂) (c₁ : IsCocycle2 ε₁) (c₂ : IsCocycle2 ε₂)
    (h : ∀ (p : ℕ) [Fact p.Prime],
      IsCoboundary2 (resC ℚ_[p] ε₁) ↔ IsCoboundary2 (resC ℚ_[p] ε₂)) :
    IsCoboundary2 (ε₁ - ε₂) := by
  have c := c₁.sub c₂
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] (ε₁ - ε₂)) := by
    intro p _
    change IsCoboundary2 (resC ℚ_[p] ε₁ - resC ℚ_[p] ε₂)
    by_cases h₁ : IsCoboundary2 (resC ℚ_[p] ε₁)
    · exact h₁.sub ((h p).mp h₁)
    · exact (hC.1 p).2 _ _ (c₁.resC _) (c₂.resC _) h₁ (fun h₂ => h₁ ((h p).mpr h₂))
  have hinf : IsCoboundary2 (resC ℝ (ε₁ - ε₂)) := by
    obtain ⟨-, hev⟩ := hR _ c
    have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
        ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] (ε₁ - ε₂))} = ∅ := by
      ext q
      have : Fact (q : ℕ).Prime := ⟨q.2⟩
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hp q
    rw [hempty, Set.ncard_empty, zero_add] at hev
    by_contra hne
    rw [if_neg hne] at hev
    exact Nat.not_even_one hev
  exact hH _ c hinf hp

end Brauer

section LocalKW

/-- **Leaf I6.3 (local Kronecker–Weber for `ℚ_p`).** Every finite abelian extension of `ℚ_p`
inside `\bar ℚ_p` lies in `ℚ_p(μ_n)` for some `n ≥ 1`.  (Serre, *Local class field theory*, in
Cassels–Fröhlich, §3.? ; Neukirch, *ANT* V (1.10); Lang, *ANT* (UNVERIFIED locators).)  In B2 it
replaces "local reciprocity" in the square-root criterion: a finite-order character of `G_{ℚ_p}`
has a character square root iff it is trivial on the element acting by `ζ ↦ ζ⁻¹` on `p`-power
roots of unity and trivially on prime-to-`p` roots of unity (GLUE). -/
def LocalKroneckerWeber (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L →
    IsAbelianGalois ℚ_[p] L →
      ∃ n : ℕ, 0 < n ∧ L ≤ IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}

end LocalKW

section Chebotarev

open NumberField

/-- **Leaf I6.4 (Chebotarev, existence form).** For a finite Galois extension `M/ℚ`, a finite set
`S` of rational primes and `σ ∈ Gal(M/ℚ)`, there is a prime `p ∉ S`, unramified in `M`, and a prime
`Q` of `𝓞_M` over `p` at which `σ` is the arithmetic Frobenius.  A consequence of the density
theorem (Neukirch, *ANT* VII (13.4): the primes with Frobenius class `⟨σ⟩` have Dirichlet density
`#⟨σ⟩/#G > 0`; UNVERIFIED locator).  C10 uses it to make Frobenius elements dense in `G_ℚ`. -/
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q

end Chebotarev

section BrauerNesbitt

/-- **Leaf I6.5 (Brauer–Nesbitt, characteristic 0, trace form).** Over a field of characteristic
`0`, two finite-dimensional semisimple representations of a group with the same character are
isomorphic.  (Lang, *Algebra*, rev. 3rd ed., XVII Cor. 3.8, for semisimple modules over any
`k`-algebra; Curtis–Reiner (1962) (27.13), and (30.16) for the characteristic-polynomial version in
any characteristic: UNVERIFIED locators.) -/
def BrauerNesbittChar0 : Prop :=
  ∀ (k G V W : Type) [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule →
    IsSemisimpleModule (MonoidAlgebra k G) σ.asModule →
    (∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k W (σ g)) →
    Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra k G] σ.asModule)

end BrauerNesbitt

/-! ## Part II. Local fields: ramification groups, the different, conductors, local CFT

Setting (Serre, *Corps locaux*, Ch. III–IV): `A → B` a finite extension of discrete valuation
rings, `A` complete with perfect residue field, fraction fields separable (and Galois where
stated).  Then `B` is the integral closure of `A` in `Frac B`, and `B ≃ₐ[A] B` is `Gal(L/K)`.
The definitions below are Serre's, written over Mathlib's `IsLocalRing.maximalIdeal`. -/

section Ramification

open IsLocalRing

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- **Definition (Serre IV §1).** The lower ramification group `G_i` (`i ≥ 0`) of `B/A`:
the `σ` with `v_B(σ b − b) ≥ i + 1` for all `b ∈ B`.  Written with Mathlib's
`AddSubgroup.inertia` (the subgroup acting trivially modulo `𝔪_B^{i+1}`), as glue-conductor's
`ramGroup` does in the global setting. -/
def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

/-- Lower numbering for a real index `u ≥ -1` (Serre IV §3): `G_u = G_{⌈u⌉}`, `G_{-1} = G`. -/
noncomputable def lowerRamR (u : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  if u ≤ -1 then ⊤ else lowerRam A B (⌈u⌉.toNat)

/-- **Definition (Serre IV §3).** Herbrand's function
`φ_{B/A}(u) = ∫₀ᵘ dt / (G₀ : G_t)`. -/
noncomputable def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (Nat.card (lowerRamR A B t) : ℝ) / (Nat.card (lowerRamR A B 0) : ℝ)

/-- **Definition (Serre IV §3).** Upper numbering `G^v = G_{ψ(v)}`, `ψ = φ⁻¹`; here `ψ(v)` is
written `sInf {u ≥ -1 | v ≤ φ(u)}` (`φ` is a continuous increasing bijection of `[-1, ∞)`). -/
noncomputable def upperRam (v : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  lowerRamR A B (sInf {u : ℝ | -1 ≤ u ∧ v ≤ herbrandPhi A B u})

/-- The subgroup rule for lower numbering (Serre IV §1 Prop. 2): for an intermediate ring `C`,
`(B/C)_i = (B/A)_i ∩ Gal(B/C)`.  GLUE: immediate from the definition (proved). -/
theorem lowerRam_tower (C : Type) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (i : ℕ) :
    lowerRam C B i = (lowerRam A B i).comap (AlgEquiv.restrictScalarsHom A) := by
  ext σ; rfl

end Ramification

section LocalLeaves

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Leaf I6.6 (Serre's bound for the different).** For a finite separable extension of
complete discrete valuation rings with perfect residue field, `v_B(𝔇_{B/A}) ≤ e − 1 + v_B(e)`,
where `e` is the ramification index.  Serre, *Corps locaux*, III §6, remark after Prop. 13
(UNVERIFIED locator).  Written `𝔇 ∣ 𝔪_B^{e-1}·(e)` (ideals of a DVR are ordered by divisibility;
if `e = 0` in `B` the right side is `⊥` and the statement is empty).  Mathlib has only the lower
bound `pow_sub_one_dvd_differentIdeal`. -/
def DifferentBound : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    differentIdeal A B ∣
      maximalIdeal B ^ (Ideal.ramificationIdx (maximalIdeal B) A - 1) *
        Ideal.span {((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : B)}

/-- **Leaf I6.7 (Hilbert's formula for the different).** For `B/A` as above and Galois,
`v_B(𝔇_{B/A}) = ∑_{i ≥ 0} (|G_i| − 1)`.  Serre, *Corps locaux*, IV §1, Prop. 4 (UNVERIFIED
locator). -/
def HilbertDifferentFormula : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1))

/-- **Leaf I6.8 (Herbrand's theorem).** For a tower `A → C → B` with `B/A` and `C/A` Galois and
`r : Gal(B/A) → Gal(C/A)` the restriction, `Gal(C/A)^v = r(Gal(B/A)^v)` for all `v`.
Serre, *Corps locaux*, IV §3, Prop. 14 (UNVERIFIED locator).  (`r` is determined by `hr`.) -/
def HerbrandQuotient : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (_hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ),
    upperRam A C v = (upperRam A B v).map r

/-- **Leaf I6.9 (transitivity of Herbrand's function).** For a tower `A → C → B` with `B/A`
Galois (hence `B/C` Galois) and `C/A` Galois, `φ_{B/A} = φ_{C/A} ∘ φ_{B/C}`.
Serre, *Corps locaux*, IV §3, Prop. 15 (UNVERIFIED locator). -/
def HerbrandTransitivity : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B],
    ∀ u : ℝ, -1 ≤ u → herbrandPhi A B u = herbrandPhi A C (herbrandPhi C B u)

/-- The principal units `U^{(n)} = 1 + 𝔪^n` (`n ≥ 1`) and `U^{(0)} = A^×`, inside `K^×`. -/
def unitFiltration (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (n : ℕ) :
    Set (FractionRing A)ˣ :=
  {x | ∃ a : A, (x : FractionRing A) = algebraMap A (FractionRing A) a ∧
    (if n = 0 then IsUnit a else a - 1 ∈ maximalIdeal A ^ n)}

/-- **Leaf I6.10 (local class field theory, finite abelian level, with the upper numbering
theorem).** For `B/A` as above, abelian Galois, with finite residue field `𝔽_q`, there is a
surjective homomorphism `θ : K^× → Gal(L/K)` whose kernel is the norm group `N_{L/K}(L^×)`,
which maps `π` (any element of valuation one) to an element acting on the residue field of `B`
by `x ↦ x^q`, and which maps `U^{(⌈v⌉)}` onto `G^v` for every real `v ≥ 0` (for integer `v` this
is the upper numbering theorem; for the other `v` it adds Hasse–Arf, Serre V §7 Thm 1, that the
upper jumps of an abelian extension are integers).
Serre, *Corps locaux*, XIII §4 Prop. 13 and XV §2 Thm 1, Cor. 3; Serre, *Local class field
theory* in Cassels–Fröhlich, §§2.8, 4.? (UNVERIFIED locators).  The canonical reciprocity map
is one such `θ`, so this ∃-form is a consequence of the published theorem. -/
def LocalReciprocityUpper : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    (∀ σ τ : B ≃ₐ[A] B, σ * τ = τ * σ) →
    ∃ θ : (FractionRing A)ˣ →* (B ≃ₐ[A] B), Function.Surjective θ ∧
      (∀ x, θ x = 1 ↔ ∃ y : FractionRing B,
          Algebra.norm (FractionRing A) y = (x : FractionRing A)) ∧
      (∀ (π : A), Irreducible π → ∀ hπ : IsUnit (algebraMap A (FractionRing A) π),
          ∀ b : B, θ hπ.unit b - b ^ Nat.card (ResidueField A) ∈ maximalIdeal B) ∧
      (∀ v : ℝ, 0 ≤ v → θ '' unitFiltration A ⌈v⌉₊ = (upperRam A B v : Set (B ≃ₐ[A] B)))

end LocalLeaves

section Conductor

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- `codim V^H` for a subgroup `H` acting through `ρ`. -/
noncomputable def codimInv {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) (H : Subgroup (B ≃ₐ[A] B)) : ℕ :=
  Module.finrank k V - Module.finrank k (Representation.invariants (ρ.comp H.subtype : Representation k H V))

/-- **Definition (Serre, *Corps locaux*, VI §2).** The Artin conductor exponent of a
representation `V` of `Gal(L/K)`: `f(V) = ∑_{i ≥ 0} (|G_i|/|G_0|) · codim V^{G_i}`. -/
noncomputable def artinConductor {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (B ≃ₐ[A] B) V) : ℚ :=
  ∑ᶠ i : ℕ, ((Nat.card (lowerRam A B i) : ℚ) / Nat.card (lowerRam A B 0)) *
    (codimInv A B ρ (lowerRam A B i) : ℚ)

/-- **D4, the conductor bound used by Glazer (GLUE, to be proved from the definitions).**
If every upper ramification group `G^v` with `v > U ≥ 0` acts trivially, then
`f(V) ≤ dim V · (1 + U)`.  It is the change of variables `f(V) = ∫_{-1}^∞ codim V^{G^v} dv`
(Serre VI §2, exercise / IV §3) with `codim ≤ dim V`. -/
theorem artinConductor_le_of_upper {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Finite (B ≃ₐ[A] B)] [IsDomain B] [IsDiscreteValuationRing B]
    (ρ : Representation k (B ≃ₐ[A] B) V) (U : ℝ) (hU : 0 ≤ U)
    (h : ∀ v : ℝ, U < v → ∀ σ ∈ upperRam A B v, ρ σ = 1) :
    (artinConductor A B ρ : ℝ) ≤ Module.finrank k V * (1 + U) := by
  sorry

end Conductor

section PrincipalUnits

open IsLocalRing

/-- **D3, squaring on principal units at `p = 2` (GLUE; elementary).**  If `B` is a complete DVR
with `2·B = 𝔪^e`, `e ≥ 1`, then for `r > e` every element of `1 + 𝔪^{r+e}` is the square of an
element of `1 + 𝔪^r`.  Applied twice: `(U^{e+1})⁴ = U^{3e+1}` (N5 L835-838).  N5 cites
Silverman, AEC IV.6.4 (formal logarithm of `Ĝ_m`); it is also Newton's form of Hensel's lemma for
`x² + 2x − y` (`v(f(0)) ≥ r + e > 2e = 2 v(f'(0))`).  Mathlib's general Hensel lemma needs a unit
derivative, so this one is not immediate.  PROVED elsewhere: glue-conductor's
`scratch/glue-conductor/Dyadic.lean` (`exists_sq_eq_one_add`, `exists_fourth_root`, commit
2aeeb7f2, via `u² + u = z/4` and Mathlib's `IsAdicComplete.henselianRing`); kept here as a
statement only. -/
theorem sq_principalUnits (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (maximalIdeal B) B] (e : ℕ) (he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ maximalIdeal B ^ (r + e)) :
    ∃ x ∈ maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  sorry

end PrincipalUnits

end PkgI6


end PkgI6Sec

section CondBreaksSec
/-! ### Copied from `scratch/glue-conductor/Breaks.lean` (compiled there). -/

/-!
# glue-conductor: the elementary core of Glazer's uniform conductor bound (D1, D3, D4)

Manuscript `diophantine_zq.tex` L796-851 (h-trust steps D1-D4). Everything here is about
integers and rationals; the ramification data enter as the sequence `g i = |G_i|` of orders
of the lower ramification groups of a finite Galois extension of local fields at one prime
(`g 0 = e`, `g` antitone, `g i ≥ 1`, `g i = 1` for large `i`), as in Serre, *Corps locaux*,
IV §§1-3. The dictionary to the field-theoretic objects is:

* Hilbert's formula: `δ = v_P(𝔇) = ∑_{i ≥ 0} (|G_i| - 1)` (Serre IV §1 Prop. 4);
* Herbrand's function at an integer lower index `m ≥ 0`: `φ(m) = ∑_{i=1}^m |G_i|/|G_0|`
  (Serre IV §3), so the upper index of the lower break `b` is `φ b`;
* `G^u = G_i` for `φ(i-1) < u ≤ φ(i)`, so `∫ (1 - |G^u|⁻¹) du` is the sum of
  `(φ i - φ (i-1)) (1 - 1/|G_i|)`.

No `sorry`.
-/

namespace GlueConductor

open Finset

/-- Herbrand's `φ` at an integer lower index `m`: `φ(m) = ∑_{i=1}^m g_i / g_0`. -/
def phi (g : ℕ → ℕ) (m : ℕ) : ℚ := ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0

/-- The different exponent through Hilbert's formula, truncated at `n`:
`δ = ∑_{i<n} (g_i - 1)` (equal to the full sum once `g i = 1` for `i ≥ n`). -/
def delta (g : ℕ → ℕ) (n : ℕ) : ℚ := ∑ i ∈ range n, ((g i : ℚ) - 1)

lemma phi_zero (g : ℕ → ℕ) : phi g 0 = 0 := by simp [phi]

lemma phi_succ (g : ℕ → ℕ) (m : ℕ) : phi g (m + 1) = phi g m + (g (m + 1) : ℚ) / g 0 := by
  unfold phi
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma phi_mono (g : ℕ → ℕ) {m m' : ℕ} (h : m ≤ m') : phi g m ≤ phi g m' := by
  unfold phi
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; omega
  · intro i _ _; positivity

/-- **The Herbrand integral (step-function form).** For `n ≥ 0`,
`δ_{n+1}/e = 1 - 1/e + ∑_{i=1}^n (φ(i) - φ(i-1)) (1 - 1/|G_i|)`, i.e.
`δ/e = 1 - 1/e + ∫₀^∞ (1 - |G^u|⁻¹) du` (N5 L807-808). -/
theorem herbrand_integral (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (n : ℕ) :
    delta g (n + 1) / g 0 =
      1 - 1 / (g 0 : ℚ) + ∑ i ∈ Icc 1 n, (phi g i - phi g (i - 1)) * (1 - 1 / (g i : ℚ)) := by
  have hpos : ∀ i, (0 : ℚ) < g i := fun i => by exact_mod_cast hg i
  induction n with
  | zero =>
    simp only [delta]
    simp
    have := hpos 0
    field_simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ← ih]
    simp only [delta, Finset.sum_range_succ _ (n + 1)]
    rw [show n + 1 - 1 = n by omega, phi_succ]
    have := hpos 0
    have := hpos (n + 1)
    field_simp
    ring

/-- `φ(m) ≤ m` (the slopes of `φ` are at most one), hence `ψ(u) ≥ u`; this is the elementary
half of the subgroup formula `ψ_{F/ℚ₂}(u) ≥ u` (N5 L838-840). -/
theorem phi_le_self (g : ℕ → ℕ) (hg0 : 0 < g 0) (hanti : Antitone g) (m : ℕ) :
    phi g m ≤ m := by
  induction m with
  | zero => simp [phi_zero]
  | succ m ih =>
    rw [phi_succ]
    have h1 : (g (m + 1) : ℚ) ≤ g 0 := by exact_mod_cast hanti (Nat.zero_le _)
    have h2 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
    have : (g (m + 1) : ℚ) / g 0 ≤ 1 := (div_le_one h2).mpr h1
    push_cast; linarith

/-- **D1, break bound.** If `G_i ≠ 1` (i.e. `g i ≥ 2`) for all `i ≤ b`, then the upper index
`φ(b)` of the lower index `b` is at most `2δ/e`: before the last break the integrand
`1 - |G^u|⁻¹` is at least `1/2` (N5 L809-812). Here `δ = δ_n` for any `n > b`. -/
theorem phi_le_two_delta (g : ℕ → ℕ) (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : ∀ i ≤ b, 2 ≤ g i)
    (hbn : b < n) : phi g b ≤ 2 * delta g n / g 0 := by
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have key : (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ 2 * delta g n := by
    calc (∑ i ∈ Icc 1 b, (g i : ℚ)) ≤ ∑ i ∈ range (b + 1), (g i : ℚ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi; simp only [Finset.mem_Icc, Finset.mem_range] at hi ⊢; omega
          · intro i _ _; positivity
      _ ≤ ∑ i ∈ range (b + 1), 2 * ((g i : ℚ) - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have : (2 : ℚ) ≤ g i := by
            exact_mod_cast hb i (by simp only [Finset.mem_range] at hi; omega)
          linarith
      _ = 2 * ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * delta g n := by
          unfold delta
          have : ∑ i ∈ range (b + 1), ((g i : ℚ) - 1) ≤ ∑ i ∈ range n, ((g i : ℚ) - 1) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.range_subset_range.mpr hbn
            · intro i _ _
              have : (1 : ℚ) ≤ g i := by exact_mod_cast hg i
              linarith
          linarith
  unfold phi
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right key h0.le

/-! ## D1's arithmetic: `δ ≤ e - 1 + e v_p(e)` and `e ≤ a!` give `2δ/e ≤ 4a²` -/

/-- `a! ≤ 2^(a²)`. -/
lemma factorial_le_two_pow_sq (a : ℕ) : a.factorial ≤ 2 ^ (a ^ 2) := by
  calc a.factorial ≤ a ^ a := Nat.factorial_le_pow a
    _ ≤ (2 ^ a) ^ a := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le a
    _ = 2 ^ (a ^ 2) := by rw [← pow_mul, sq]

/-- `v_p(e) ≤ log₂ e`. -/
lemma padicValNat_le_log_two {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    padicValNat p e ≤ Nat.log 2 e := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc 2 ^ padicValNat p e ≤ p ^ padicValNat p e := Nat.pow_le_pow_left hp.two_le _
    _ ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero he) pow_padicValNat_dvd

/-- `1 + log₂(a!) ≤ 2a²` for `a ≥ 1`, the manuscript's `2(1 + log₂ a!) ≤ 4a²`. -/
lemma one_add_log_factorial_le (a : ℕ) (ha : 1 ≤ a) : 1 + Nat.log 2 a.factorial ≤ 2 * a ^ 2 := by
  have h1 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  have h2 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ ha
  omega

/-- `v_p(e) ≤ a²` when `e ≤ a!`. -/
lemma padicValNat_le_sq {p e a : ℕ} (hp : p.Prime) (he : e ≠ 0) (hea : e ≤ a.factorial) :
    padicValNat p e ≤ a ^ 2 := by
  have := padicValNat_le_log_two hp he
  have h1 : Nat.log 2 e ≤ Nat.log 2 a.factorial := Nat.log_mono_right hea
  have h2 : Nat.log 2 a.factorial ≤ a ^ 2 := by
    calc Nat.log 2 a.factorial ≤ Nat.log 2 (2 ^ (a ^ 2)) :=
          Nat.log_mono_right (factorial_le_two_pow_sq a)
      _ = a ^ 2 := Nat.log_pow (by norm_num) _
  omega

/-- **D1, arithmetic.** If `δ ≤ e - 1 + e·v_p(e)` (Serre's different bound) and `e ≤ a!`
(the normal closure of a degree-`a` extension has degree at most `a!`), then
`2δ ≤ 2(1 + log₂ a!)·e ≤ 4a²·e`. -/
theorem two_delta_le (p e a δ : ℕ) (hp : p.Prime) (he : 1 ≤ e) (ha : 1 ≤ a)
    (hea : e ≤ a.factorial) (hδ : δ ≤ e - 1 + e * padicValNat p e) :
    2 * δ ≤ 2 * (1 + Nat.log 2 a.factorial) * e ∧ 2 * (1 + Nat.log 2 a.factorial) * e ≤ 4 * a ^ 2 * e := by
  have hv : padicValNat p e ≤ Nat.log 2 a.factorial :=
    (padicValNat_le_log_two hp (by omega)).trans (Nat.log_mono_right hea)
  have hl := one_add_log_factorial_le a ha
  constructor
  · have : e * padicValNat p e ≤ e * Nat.log 2 a.factorial := Nat.mul_le_mul_left e hv
    have h2 : e - 1 + e * padicValNat p e ≤ e * (1 + Nat.log 2 a.factorial) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc 2 * δ ≤ 2 * (e * (1 + Nat.log 2 a.factorial)) := by omega
      _ = 2 * (1 + Nat.log 2 a.factorial) * e := by ring
  · have : 2 * (1 + Nat.log 2 a.factorial) ≤ 4 * a ^ 2 := by omega
    exact Nat.mul_le_mul_right e this

/-- **D1, combined.** Let `g i = |G_i|` be the lower ramification data of a finite Galois
extension of `ℚ_p`-local fields with `e = g 0 ≤ a!`, let `b` be a lower index with `G_b ≠ 1`
(e.g. the last break), and suppose the different exponent `δ = ∑_{i<n}(g_i - 1)` (Hilbert)
satisfies Serre's bound `δ ≤ e - 1 + e v_p(e)`. Then the upper index of `b` is at most
`4a²`: `u_last ≤ 2δ/e ≤ 4a²` (N5 L796-812). -/
theorem upper_break_le (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (g : ℕ → ℕ) (hanti : Antitone g)
    (hg : ∀ i, 1 ≤ g i) (b n : ℕ) (hb : 2 ≤ g b) (hbn : b < n) (hea : g 0 ≤ a.factorial)
    (hSerre : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0)) :
    phi g b ≤ 4 * a ^ 2 := by
  have hb' : ∀ i ≤ b, 2 ≤ g i := fun i hi => hb.trans (hanti hi)
  have h1 := phi_le_two_delta g hg b n hb' hbn
  have hδ : delta g n = ((∑ i ∈ range n, (g i - 1) : ℕ) : ℚ) := by
    unfold delta
    push_cast [Nat.cast_sub (hg _)]
    rfl
  obtain ⟨h2, h3⟩ := two_delta_le p (g 0) a _ hp (hg 0) ha hea hSerre
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg 0
  have h4 : (2 * delta g n : ℚ) ≤ 4 * a ^ 2 * g 0 := by
    rw [hδ]; exact_mod_cast h2.trans h3
  calc phi g b ≤ 2 * delta g n / g 0 := h1
    _ ≤ 4 * a ^ 2 * g 0 / g 0 := div_le_div_of_nonneg_right h4 h0.le
    _ = 4 * a ^ 2 := by field_simp

/-! ## D4: conductor exponents -/

/-- **D4, Swan term.** For a representation of dimension two through a finite Galois
extension with lower ramification data `g`, the Swan conductor is
`∑_{i ≥ 1} (|G_i|/|G_0|) codim V^{G_i}` (Serre VI §2). If every `G_i` with upper index
`φ(i) > U` acts trivially (`c i = 0`), and `c i ≤ 2`, then `Sw ≤ 2U` (N5 L845-846). -/
theorem swan_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc2 : ∀ i, c i ≤ 2) (htriv : ∀ i, U < phi g i → c i = 0) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 * U := by
  classical
  have h0 : (0 : ℚ) < g 0 := by exact_mod_cast hg0
  set s := (Icc 1 n).filter (fun i => phi g i ≤ U) with hs
  have step1 : ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ ∑ i ∈ s, 2 * ((g i : ℚ) / g 0) := by
    rw [hs, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    have hq : (0 : ℚ) ≤ (g i : ℚ) / g 0 := by positivity
    split_ifs with h
    · nlinarith [hc2 i]
    · rw [htriv i (lt_of_not_ge h), mul_zero]
  have step2 : ∑ i ∈ s, (g i : ℚ) / g 0 ≤ U := by
    rcases s.eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty]; exact hU
    · obtain ⟨m, hm, hmax⟩ := s.exists_max_image id hne
      have hsub : s ⊆ Icc 1 m := by
        intro i hi
        have h1 := (Finset.mem_filter.mp hi).1
        simp only [Finset.mem_Icc] at h1 ⊢
        exact ⟨h1.1, hmax i hi⟩
      calc ∑ i ∈ s, (g i : ℚ) / g 0 ≤ ∑ i ∈ Icc 1 m, (g i : ℚ) / g 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ = phi g m := rfl
        _ ≤ U := (Finset.mem_filter.mp hm).2
  rw [← Finset.mul_sum] at step1
  linarith

/-- **D4, at `p ≤ R`.** The Artin exponent `a = codim V^I + Sw` of a two-dimensional
representation with `codim V^I ≤ 2` and with every upper group above `U` acting trivially is
at most `2 + 2U`. -/
theorem artin_le (g : ℕ → ℕ) (hg0 : 0 < g 0) (c : ℕ → ℚ) (c0 U : ℚ) (hU : 0 ≤ U) (n : ℕ)
    (hc00 : c0 ≤ 2) (hc2 : ∀ i, c i ≤ 2)
    (htriv : ∀ i, U < phi g i → c i = 0) :
    c0 + ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i ≤ 2 + 2 * U := by
  have := swan_le g hg0 c U hU n hc2 htriv
  linarith

/-- **D4, tame primes `p > R`.** If the ramification index `e` is less than `p`, the wild
group `G_1` (a `p`-group whose order divides `e`) is trivial. -/
lemma wild_trivial_of_tame {p e k : ℕ} (he : 0 < e) (hep : e < p)
    (hdvd : p ^ k ∣ e) : p ^ k = 1 := by
  rcases k with _ | k
  · simp
  · exfalso
    have := Nat.le_of_dvd he hdvd
    have : p ≤ p ^ (k + 1) := Nat.le_self_pow (by omega) p
    omega

/-- **D4, tame primes**, continued: if `G_1 = 1` then the Swan term vanishes, so the Artin
exponent is `codim V^I ≤ 2`. -/
theorem swan_eq_zero_of_tame (g : ℕ → ℕ) (hanti : Antitone g) (hg1 : g 1 = 1) (c : ℕ → ℚ)
    (hc : ∀ i, g i = 1 → c i = 0) (n : ℕ) :
    ∑ i ∈ Icc 1 n, (g i : ℚ) / g 0 * c i = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have : g i ≤ 1 := hg1 ▸ hanti hi1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
  · simp [h]
  · simp [hc i h]

/-! ## D2: odd `p`, the character `β` on wild inertia -/

/-- **D2, last sentence.** Let `β : G →* H` be a homomorphism whose values have `p`-power
order, `p` odd (for `G = P_F` pro-`p` and `β` continuous into the finite group `μ_{2m}`, the
image is a finite `p`-group). If `β²` is trivial (`β² = χ` is tame, so trivial on wild
inertia), then `β` is trivial: a pro-`p` group has no quotient of order two (N5 L821-823). -/
theorem char_trivial_of_odd_pgroup {G H : Type*} [Group G] [Group H] (p : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (β : G →* H) (himg : ∀ g, ∃ k : ℕ, β g ^ (p ^ k) = 1)
    (hsq : ∀ g, β g ^ 2 = 1) : ∀ g, β g = 1 := by
  intro g
  obtain ⟨k, h1⟩ := himg g
  have hcop : Nat.Coprime 2 (p ^ k) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hodd)
  have h2 : orderOf (β g) ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq g)
  have h3 : orderOf (β g) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have : orderOf (β g) ∣ Nat.gcd 2 (p ^ k) := Nat.dvd_gcd h2 h3
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

/-- The image of a homomorphism from a finite `p`-group has `p`-power-order elements, so
`char_trivial_of_odd_pgroup` applies to `β` restricted to any finite `p`-group quotient. -/
lemma pow_card_eq_one_of_pgroup {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    (hG : IsPGroup p G) (β : G →* H) (g : G) : ∃ k : ℕ, β g ^ (p ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hG g
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

/-! ## D2-D4: the constants -/

/-- `G₀ = |GL₄(𝔽₅)|` (the degree of `L_v(A[5])/L_v` is at most this). -/
theorem card_GL4_F5 : Nat.card (GL (Fin 4) (ZMod 5)) = 116064000000 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 5)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- `|GL₄(𝔽₃)| = 24261120 ≤ G₀` (the degree of `L_v(A[3])/L_v`). -/
theorem card_GL4_F3 : Nat.card (GL (Fin 4) (ZMod 3)) = 24261120 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field (n := 4) (𝔽 := ZMod 3)]
  simp [Fin.prod_univ_four, ZMod.card]

/-- The subgroup-formula threshold at `p = 2`: `max(4D², 3e) ≤ U₀ = 4(D G₀)²` when
`e ≤ D` and `G₀ ≥ 1` (N5 L841-842). -/
theorem max_le_U0 (D G0 e : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) (he : e ≤ D) :
    max (4 * D ^ 2) (3 * e) ≤ 4 * (D * G0) ^ 2 := by
  have h1 : D ^ 2 ≤ (D * G0) ^ 2 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right D hG) 2
  have h2 : 3 * e ≤ 4 * D ^ 2 := by nlinarith
  omega

/-- `2 + 2U₀ ≤ E₀`, with `U₀ = 4(DG₀)²` and `E₀ = 10(DG₀)²` (N5 L845-846). -/
theorem two_add_two_U0_le_E0 (D G0 : ℕ) (hD : 1 ≤ D) (hG : 1 ≤ G0) :
    2 + 2 * (4 * (D * G0) ^ 2) ≤ 10 * (D * G0) ^ 2 := by
  have : 1 ≤ (D * G0) ^ 2 := Nat.one_le_pow _ _ (Nat.mul_pos hD hG)
  omega


/-! ## D1 over genuine definitions (Mathlib's rings of integers, inertia and different)

For a Galois number field `L/ℚ` and a prime `P` of `𝓞 L`, the lower ramification groups are
`G_i = {σ ∈ Gal(L/ℚ) | ∀ x ∈ 𝓞 L, σ x - x ∈ P^(i+1)}`, i.e. Mathlib's `Ideal.inertia` of
`P^(i+1)`; `G_0` is Mathlib's inertia group. (Serre, *Corps locaux*, IV §1 defines them for the
completion; they agree with these, Serre I §7 and IV §1, UNVERIFIED locators.) The two leaves
below are published theorems (local statements transported to number fields by completion). -/

open NumberField

/-- The lower ramification group `G_i` of `P` in `Gal(L/ℚ)`. -/
abbrev ramGroup (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) :
    Subgroup Gal(L/ℚ) :=
  (P ^ (i + 1)).inertia Gal(L/ℚ)

/-- `|G_i|`. -/
noncomputable abbrev ramCard (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) : ℕ :=
  Nat.card (ramGroup L P i)

/-- **Leaf (Hilbert's different formula; Serre, *Corps locaux*, IV §1, Prop. 4, with `G_i = 1`
for large `i`, IV §1; UNVERIFIED numbering).** For a Galois number field `L` and a nonzero prime
`P` of `𝓞 L`, some `G_n` is trivial and the exact power of `P` in the different of `𝓞 L/ℤ` is
`∑_{i<n} (|G_i| - 1)`. -/
def HilbertDifferentFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- **Leaf (Serre's bound for the different; Serre, *Corps locaux*, III §6, remark after
Prop. 13: `v_L(𝔇_{L/K}) ≤ e - 1 + v_L(e)`; UNVERIFIED numbering).** At `K = ℚ_p`,
`v_L(e) = e·v_p(e)`. Stated for any number field `L` and prime `P | p` of `𝓞 L`. -/
def SerreDifferentBound : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)

instance spanNatPrime_isPrime (p : ℕ) [hp : Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

/-- **D1 over genuine definitions.** From the two leaves: for a Galois number field `L`, a prime
`P | p` with ramification index `e ≤ a!` and a lower index `b` with `G_b ≠ 1`, the upper index
`φ(b)` (Herbrand's function of the genuine `|G_i|`) is at most `4a²`. -/
theorem D1_genuine (hH : HilbertDifferentFormula) (hS : SerreDifferentBound)
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (p : ℕ) [hpF : Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] [hPl : P.LiesOver (Ideal.span {(p : ℤ)})]
    (a : ℕ) (ha : 1 ≤ a) (hea : P.ramificationIdx ℤ ≤ a.factorial)
    (b : ℕ) (hb : ramGroup L P b ≠ ⊥) :
    phi (ramCard L P) b ≤ 4 * a ^ 2 := by
  have hp : p.Prime := hpF.out
  have hP0 : P ≠ ⊥ := by
    intro h
    have := hPl.over
    rw [h, Ideal.under_bot] at this
    have h2 := Ideal.span_singleton_eq_bot.mp this
    simp [hp.ne_zero] at h2
  set g := ramCard L P with hg_def
  have hanti : Antitone g := by
    intro i j hij
    apply Subgroup.card_le_of_le
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have hg1 : ∀ i, 1 ≤ g i := fun i => Nat.card_pos
  have hgb : 2 ≤ g b := by
    have h1 := hg1 b
    have h2 : g b ≠ 1 := fun h => hb (Subgroup.card_eq_one.mp h)
    omega
  obtain ⟨n, hn, hdvd, -⟩ := hH L P hP0
  have hbn : b < n := by
    by_contra h
    apply hb
    rw [eq_bot_iff, ← hn]
    intro σ hσ x
    exact Ideal.pow_le_pow_right (by omega) (hσ x)
  have he : g 0 = P.ramificationIdx ℤ := by
    show Nat.card ((P ^ (0 + 1)).inertia Gal(L/ℚ)) = _
    rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn (Ideal.span {(p : ℤ)}) P,
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P Gal(L/ℚ)]
  have hSer := hS L p hp P hPl
  have hsum : ∑ i ∈ range n, (g i - 1) ≤ g 0 - 1 + g 0 * padicValNat p (g 0) := by
    rw [he]
    by_contra hlt
    push Not at hlt
    exact hSer (dvd_trans (pow_dvd_pow P hlt) hdvd)
  exact upper_break_le p a hp ha g hanti hg1 b n hgb hbn (he ▸ hea) hsum

end GlueConductor



end CondBreaksSec

section CondDyadicSec
/-! ### Copied from `scratch/glue-conductor/Dyadic.lean` (compiled there). -/

/-!
# glue-conductor: the dyadic unit step of D3 (N5 L828-832)

N5: "the logarithm for `Ĝ_m` identifies `U_F^{e+1}` with `𝔪_F^{e+1}` since `e+1 > e`
[Silverman IV.6.4]. Multiplication by four gives `(U_F^{e+1})^4 = U_F^{3e+1}`."

The direction used is `U_F^{3e+1} ⊆ (U_F^{e+1})^4` (so that `β⁴ = 1` on `U_F` forces `β = 1` on
`U_F^{3e+1}`). We prove both directions for any complete discrete valuation ring `A` with
`v(2) = e`, i.e. `(2) = 𝔪^e`, with no logarithm: a square root of `1 + z`, `z ∈ 𝔪^{2e+s}`,
`s ≥ 1`, is `1 + 2u` with `u² + u = z/4`, a simple root by Hensel's lemma (Mathlib's
`IsAdicComplete.henselianRing`). The ring of integers of a finite extension `F/ℚ₂` with
absolute ramification index `e` satisfies the hypotheses. No `sorry`.
-/

namespace GlueConductor

open IsLocalRing Polynomial

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- Square roots near one: if `(2) = 𝔪^e`, `z ∈ 𝔪^{2e+s}` and `s ≥ 1`, then `1 + z = (1 + w)²`
for some `w ∈ 𝔪^{e+s}`. -/
theorem exists_sq_eq_one_add [IsAdicComplete (maximalIdeal A) A] (e s : ℕ) (hs : 1 ≤ s)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (2 * e + s)) :
    ∃ w ∈ maximalIdeal A ^ (e + s), (1 + w) ^ 2 = 1 + z := by
  set m := maximalIdeal A
  -- z = 4c with c ∈ 𝔪^s
  have h4 : m ^ (2 * e + s) = Ideal.span {(4 : A)} * m ^ s := by
    rw [pow_add, two_mul, pow_add, ← h2, Ideal.span_singleton_mul_span_singleton]
    norm_num
  rw [h4, Ideal.mem_span_singleton_mul] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  have hcm : c ∈ m := Ideal.pow_le_self (by omega) hc
  -- Hensel: u² + u = c
  let f : A[X] := X ^ 2 + (X - C c)
  have hmon : f.Monic :=
    (monic_X_pow 2).add_of_left (by rw [degree_X_sub_C, degree_X_pow]; norm_num)
  have heval0 : f.eval 0 ∈ m := by
    simp [f, hcm]
  have hder : IsUnit (Ideal.Quotient.mk m (f.derivative.eval 0)) := by
    simp [f]
  obtain ⟨u, hu, hu0⟩ := HenselianRing.is_henselian f hmon 0 heval0 hder
  rw [sub_zero] at hu0
  have hroot : u ^ 2 + u = c := by
    have := hu.eq_zero
    simp only [f, eval_sub, eval_add, eval_pow, eval_X, eval_C] at this
    linear_combination this
  -- u ∈ 𝔪^s, since u (u + 1) = c and u + 1 is a unit
  have hunit : IsUnit (u + 1) := by
    by_contra h
    have h1 : u + 1 ∈ m := (mem_maximalIdeal _).mpr h
    have : (1 : A) ∈ m := by simpa using sub_mem h1 hu0
    exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hus : u ∈ m ^ s := by
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have : u = c * v := by
      calc u = u * ((u + 1) * v) := by rw [hv, mul_one]
        _ = (u ^ 2 + u) * v := by ring
        _ = c * v := by rw [hroot]
    rw [this]
    exact Ideal.mul_mem_right _ _ hc
  refine ⟨2 * u, ?_, ?_⟩
  · rw [pow_add, ← h2]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self 2) hus
  · calc (1 + 2 * u) ^ 2 = 1 + 4 * (u ^ 2 + u) := by ring
      _ = 1 + 4 * c := by rw [hroot]

/-- **D3, `U^{3e+1} ⊆ (U^{e+1})⁴`.** In a complete DVR (complete local ring) with `(2) = 𝔪^e`,
every `y ∈ 1 + 𝔪^{3e+1}` is a fourth power of some `x ∈ 1 + 𝔪^{e+1}`. -/
theorem exists_fourth_root [IsAdicComplete (maximalIdeal A) A] (e : ℕ)
    (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (z : A)
    (hz : z ∈ maximalIdeal A ^ (3 * e + 1)) :
    ∃ w ∈ maximalIdeal A ^ (e + 1), (1 + w) ^ 4 = 1 + z := by
  obtain ⟨w₁, hw₁, h₁⟩ := exists_sq_eq_one_add e (e + 1) (by omega) h2 z
    (by rwa [show 2 * e + (e + 1) = 3 * e + 1 by ring])
  obtain ⟨w, hw, h⟩ := exists_sq_eq_one_add e 1 le_rfl h2 w₁
    (by rwa [show 2 * e + 1 = e + (e + 1) by ring])
  exact ⟨w, hw, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, h₁]⟩

/-- **D3, `(U^{e+1})⁴ ⊆ U^{3e+1}`** (the easy direction; no completeness needed). -/
theorem fourth_pow_mem (e : ℕ) (h2 : Ideal.span {(2 : A)} = maximalIdeal A ^ e) (w : A)
    (hw : w ∈ maximalIdeal A ^ (e + 1)) :
    (1 + w) ^ 4 - 1 ∈ maximalIdeal A ^ (3 * e + 1) := by
  set m := maximalIdeal A
  have h2m : (2 : A) ∈ m ^ e := h2 ▸ Ideal.mem_span_singleton_self 2
  have hexp : (1 + w) ^ 4 - 1 = 2 * 2 * w + 2 * (3 * w * w) + 2 * 2 * (w * w * w) + w * w * w * w := by
    ring
  rw [hexp]
  have hww : w * w ∈ m ^ (2 * e + 2) := by
    rw [show 2 * e + 2 = (e + 1) + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul hw hw
  have h22 : 2 * 2 ∈ m ^ (2 * e) := by rw [two_mul, pow_add]; exact Ideal.mul_mem_mul h2m h2m
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_
  · rw [show 3 * e + 1 = 2 * e + (e + 1) by ring, pow_add]; exact Ideal.mul_mem_mul h22 hw
  · have : 3 * w * w ∈ m ^ (2 * e + 2) := by
      rw [mul_assoc]; exact Ideal.mul_mem_left _ _ hww
    have h' := Ideal.mul_mem_mul h2m this
    rw [← pow_add] at h'
    exact Ideal.pow_le_pow_right (by omega) h'
  · have hwww : w * w * w ∈ m ^ (3 * e + 3) := by
      rw [show 3 * e + 3 = (2 * e + 2) + (e + 1) by ring, pow_add]
      exact Ideal.mul_mem_mul hww hw
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hwww)
  · have : w * w * w * w ∈ m ^ (4 * e + 4) := by
      rw [show 4 * e + 4 = (2 * e + 2) + (2 * e + 2) by ring, pow_add, mul_assoc]
      exact Ideal.mul_mem_mul hww hww
    exact Ideal.pow_le_pow_right (by omega) this

end GlueConductor


end CondDyadicSec

section CondLevelSec
/-! ### Copied from `scratch/glue-conductor/Level.lean` (compiled there). -/

/-!
# glue-conductor: the level product `N ≤ Q_R M²` (h-trust D4-D5, N5 L846-857)

Over the repository's own definitions (`ZInQ.heightE0`, `ZInQ.heightQ`,
`ZInQ.contactSupport`). The conductor exponents `a_p = v_p(N)` (Carayol's Théorème A turns the
conductor exponents of `r₅` (and of `r₃` at `p = 5`) into the exponents of the level `N`) enter
through `N.factorization`. Hypotheses, as in N5:

* `a_p ≤ E₀` at primes `p ≤ R` (D4, first case);
* at primes `p > R`, `a_p ≤ 2` (D4, tame case), and `a_p = 0` unless `p ∈ T = S ∪ supp M_S(u)`
  (D4, third case: outside `T`, `L` is unramified, `A` has good reduction and `β` is unramified).

Since `max S ≤ R`, a prime `p > R` with `a_p > 0` divides `M = M_S(u)`, a product of distinct
primes, so the large part of `N` is at most `M²`; the small part is at most
`(∏_{p ≤ R} p)^{E₀} ≤ R^{R E₀} = Q_R`. No `sorry`.
-/

namespace GlueConductor

open ZInQ

/-- `M_S(u) > 0`. -/
lemma contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  classical
  unfold contactSupport
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- `∏_{p prime, p ≤ R} p^E ≤ R^(R E)` for real `R ≥ 1`, over any finset of primes `≤ R`. -/
lemma prod_small_le (R : ℝ) (hR : 1 ≤ R) (E : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ R) :
    ∏ p ∈ s, (p : ℝ) ^ E ≤ R ^ (R * E) := by
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hcard : (s.card : ℝ) ≤ R := by
    have hsub : s ⊆ Finset.Icc 1 ⌊R⌋₊ := by
      intro p hp
      obtain ⟨hpp, hpR⟩ := hs p hp
      simp only [Finset.mem_Icc]
      exact ⟨hpp.one_lt.le, Nat.le_floor hpR⟩
    have h1 : s.card ≤ ⌊R⌋₊ := by
      simpa using Finset.card_le_card hsub
    calc (s.card : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast h1
      _ ≤ R := Nat.floor_le hR0
  calc ∏ p ∈ s, (p : ℝ) ^ E = (∏ p ∈ s, (p : ℝ)) ^ E := by rw [Finset.prod_pow]
    _ ≤ (R ^ s.card) ^ E := by
        apply pow_le_pow_left₀ (Finset.prod_nonneg fun p _ => by positivity)
        calc ∏ p ∈ s, (p : ℝ) ≤ ∏ _p ∈ s, R :=
              Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p hp => (hs p hp).2)
          _ = R ^ s.card := Finset.prod_const R
    _ = R ^ ((s.card : ℝ) * E) := by
        rw [Real.rpow_mul hR0, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ R ^ (R * E) := by
        apply Real.rpow_le_rpow_of_exponent_le hR
        exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **D5's product (N5 L852-857).** Let `N ≥ 1` have exponents `a_p = v_p(N)` with `a_p ≤ E₀`
at `p ≤ R`, and, at `p > R`, `a_p ≤ 2` and `a_p = 0` unless `p ∈ S` or `p ∣ M_S(u)`. If every
prime of `S` is at most `R` and `R ≥ 1`, then `N ≤ Q_R · M_S(u)²`. -/
theorem level_le (S : Finset ℕ) (u : ℚ) (R : ℝ) (hR : 1 ≤ R) (hS : ∀ p ∈ S, (p : ℝ) ≤ R)
    (N : ℕ) (hN : N ≠ 0)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ R → N.factorization p ≤ heightE0)
    (hlarge : ∀ p : ℕ, p.Prime → R < p → N.factorization p ≤ 2)
    (houtside : ∀ p : ℕ, p.Prime → p ∣ N → p ∈ S ∨ p ∣ contactSupport S u) :
    (N : ℝ) ≤ heightQ R * (contactSupport S u : ℝ) ^ 2 := by
  classical
  set M := contactSupport S u
  have hM : 0 < M := contactSupport_pos' S u
  have hN' : (N : ℝ) = ∏ p ∈ N.primeFactors, (p : ℝ) ^ (N.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hN]
    push_cast
    rfl
  rw [hN', ← Finset.prod_filter_mul_prod_filter_not N.primeFactors (fun p : ℕ => (p : ℝ) ≤ R)]
  set sm := N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R)
  set lg := N.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ R)
  -- small primes
  have h1 : ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ heightQ R := by
    calc ∏ p ∈ sm, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ sm, (p : ℝ) ^ heightE0 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le) (hsmall p hpp hpR)
      _ ≤ R ^ (R * heightE0) := by
          apply prod_small_le R hR heightE0 sm
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          exact ⟨Nat.prime_of_mem_primeFactors hpN, hpR⟩
      _ = heightQ R := rfl
  -- large primes
  have h2 : ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ (M : ℝ) ^ 2 := by
    have hdvd : (∏ p ∈ lg, p) ∣ M := by
      apply Finset.prod_primes_dvd
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).prime
      · intro p hp
        obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
        have hpp := Nat.prime_of_mem_primeFactors hpN
        rcases houtside p hpp (Nat.dvd_of_mem_primeFactors hpN) with h | h
        · exact absurd (hS p h) hpR
        · exact h
    have hle : (∏ p ∈ lg, p) ≤ M := Nat.le_of_dvd hM hdvd
    calc ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p) ≤ ∏ p ∈ lg, (p : ℝ) ^ 2 := by
          apply Finset.prod_le_prod₀ (fun p _ => by positivity)
          intro p hp
          obtain ⟨hpN, hpR⟩ := Finset.mem_filter.mp hp
          have hpp := Nat.prime_of_mem_primeFactors hpN
          exact pow_le_pow_right₀ (by exact_mod_cast hpp.one_lt.le)
            (hlarge p hpp (lt_of_not_ge hpR))
      _ = ((∏ p ∈ lg, p : ℕ) : ℝ) ^ 2 := by push_cast; rw [Finset.prod_pow]
      _ ≤ (M : ℝ) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast hle
  have hQ : 0 ≤ heightQ R := Real.rpow_nonneg (by linarith) _
  calc (∏ p ∈ sm, (p : ℝ) ^ (N.factorization p)) * ∏ p ∈ lg, (p : ℝ) ^ (N.factorization p)
      ≤ heightQ R * (M : ℝ) ^ 2 :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun p _ => by positivity) hQ

end GlueConductor


end CondLevelSec

section AssemblySec
/-! ### Copied from `scratch/glue-assembly/GlueAssembly.lean` (compiled there). -/


/-!
# Step F2 of h-trust: `h(Φ(z)) ≤ 40 h(z) + 22` over Mathlib's Weil heights

`Φ(z) = 3779136 (∏ z_m)⁴ / (∑ z_m⁸)⁵` (N5 L920-932). The statement is about Mathlib's genuine
Weil height `Height.logHeight` on a field with admissible absolute values (number fields).
-/

namespace GlueAssembly

open MvPolynomial Height Real

/-- The two coordinates of `Φ`, as polynomials over `ℕ` in ten variables. -/
noncomputable def PhiNat : Fin 2 → MvPolynomial (Fin 10) ℕ :=
  ![C 3779136 * (∏ i, X i) ^ 4, (∑ i, X i ^ 8) ^ 5]

theorem PhiNat_homogeneous (j : Fin 2) : (PhiNat j).IsHomogeneous 40 := by
  fin_cases j
  · have h1 : (∏ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ)).IsHomogeneous 10 := by
      have := IsHomogeneous.prod (Finset.univ : Finset (Fin 10)) (fun i => (X i : MvPolynomial (Fin 10) ℕ))
        (fun _ => 1) (fun i _ => isHomogeneous_X ℕ i)
      simpa using this
    have := (h1.pow 4).C_mul 3779136
    simpa [PhiNat] using this
  · have h1 : (∑ i : Fin 10, (X i : MvPolynomial (Fin 10) ℕ) ^ 8).IsHomogeneous 8 :=
      IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_X_pow i 8)
    simpa [PhiNat] using h1.pow 5

/-- The sum of the coefficients of a polynomial over `ℕ` is its value at `1`. -/
theorem sum_coeff_eq_eval_one {σ : Type*} (P : MvPolynomial σ ℕ) :
    ∑ s ∈ P.support, P.coeff s = eval (fun _ => 1) P := by
  rw [eval_eq]; simp

theorem PhiNat_eval_one (j : Fin 2) : eval (fun _ => 1) (PhiNat j) ≤ 3779136 := by
  fin_cases j <;> simp [PhiNat]

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- `Φ`'s coordinates over `K`. -/
noncomputable def PhiK (K : Type*) [CommSemiring K] : Fin 2 → MvPolynomial (Fin 10) K :=
  fun j => map (Nat.castRingHom K) (PhiNat j)

theorem PhiK_eval (z : Fin 10 → K) :
    (fun j => (PhiK K j).eval z) = ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] := by
  ext j; fin_cases j <;> simp [PhiK, PhiNat]

/-- Local bound at an absolute value: the `ℓ¹`-norm of the coefficients is at most the value at
`1` of the `ℕ`-polynomial. -/
theorem coeff_sum_le (v : AbsoluteValue K ℝ) (P : MvPolynomial (Fin 10) ℕ) :
    (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) ≤
      ((eval (fun _ => 1) P : ℕ) : ℝ) := by
  have e : (AddMonoidAlgebra.coeff (map (Nat.castRingHom K) P)).sum (fun _ c => v c) =
      ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s) := rfl
  rw [e, ← sum_coeff_eq_eval_one]
  push_cast
  calc ∑ s ∈ (map (Nat.castRingHom K) P).support, v ((map (Nat.castRingHom K) P).coeff s)
      ≤ ∑ s ∈ P.support, v ((map (Nat.castRingHom K) P).coeff s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (support_map_subset _ _)
          (fun _ _ _ => v.nonneg _)
    _ ≤ ∑ s ∈ P.support, (P.coeff s : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [coeff_map]
        simpa using v.apply_nat_le_self (P.coeff s)

theorem mulHeightBound_PhiK_le :
    mulHeightBound (PhiK K) ≤ (3779136 : ℝ) ^ totalWeight K := by
  rw [mulHeightBound_eq]
  have hnon : (∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal (K := K),
      ⨆ j, max (⨆ s : (PhiK K j).support, v.val ((PhiK K j).coeff s)) 1) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    have hv := AdmissibleAbsValues.isNonarchimedean v.val v.prop
    refine le_antisymm (ciSup_le fun j => max_le ?_ le_rfl) ?_
    · rcases isEmpty_or_nonempty (PhiK K j).support with h | h
      · simp
      refine ciSup_le fun s => ?_
      simp only [PhiK, coeff_map]
      exact hv.apply_natCast_le_one (map_zero_le v.val 1) (map_one v.val)
    · exact le_trans (le_max_right _ 1) (Finite.le_ciSup_of_le (0 : Fin 2) le_rfl)
  rw [hnon, mul_one]
  have hle : ∀ v ∈ AdmissibleAbsValues.archAbsVal (K := K),
      (⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)) ≤ (3779136 : ℝ) := by
    intro v _
    refine ciSup_le fun j => (coeff_sum_le v (PhiNat j)).trans ?_
    exact_mod_cast PhiNat_eval_one j
  calc (AdmissibleAbsValues.archAbsVal.map fun v =>
        ⨆ j, (AddMonoidAlgebra.coeff (PhiK K j)).sum (fun _ c => v c)).prod
      ≤ (AdmissibleAbsValues.archAbsVal.map fun _ => (3779136 : ℝ)).prod :=
        Multiset.prod_map_le_prod_map₀ _ _
          (fun v _ => Real.iSup_nonneg fun j => Finsupp.sum_nonneg' fun _ => v.nonneg _) hle
    _ = (3779136 : ℝ) ^ totalWeight K := by
        simp [totalWeight]

/-- **F2, relative form.** For `z ∈ K¹⁰` (any field with admissible absolute values), the
projective height of `[3779136 (∏ z_m)⁴ : (∑ z_m⁸)⁵]` is at most
`40 h_K(z) + n_K log 3779136`, `n_K` the total weight (`= [K:ℚ]` for number fields). -/
theorem logHeight_Phi_le (z : Fin 10 → K) :
    logHeight ![3779136 * (∏ i, z i) ^ 4, (∑ i, z i ^ 8) ^ 5] ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  have hp : ∀ j, (PhiK K j).IsHomogeneous 40 := fun j => (PhiNat_homogeneous j).map _
  have h := logHeight_eval_le hp z
  rw [PhiK_eval] at h
  have hB : log (max (mulHeightBound (PhiK K)) 1) ≤ totalWeight K * log 3779136 := by
    rw [← Real.log_pow]
    refine Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _)) ?_
    exact max_le mulHeightBound_PhiK_le (one_le_pow₀ (by norm_num))
  push_cast at h
  linarith

/-- **F2, affine form**: `h_K(Φ(z)) ≤ 40 h_K(z) + n_K log 3779136`, with `Φ(z)` the quotient. -/
theorem logHeight₁_Phi_le (z : Fin 10 → K) :
    logHeight₁ (3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5) ≤
      40 * logHeight z + totalWeight K * log 3779136 := by
  rw [logHeight₁_div_eq_logHeight]; exact logHeight_Phi_le z

end GlueAssembly


/-!
# Height of a rational number in a number field

`h_K(q) = [K:ℚ] · log max(|num q|, den q)` for `q ∈ ℚ` and a number field `K` (Mathlib's relative
height `Height.logHeight₁`). This is the invariance of the absolute height under finite
extension, for rational numbers.
-/

namespace GlueAssembly

open Height NumberField Real

variable {K : Type*} [Field K] [NumberField K]

theorem iSup_fin_two (f : Fin 2 → ℝ) : ⨆ i, f i = max (f 0) (f 1) := by
  refine le_antisymm (ciSup_le fun i => ?_) (max_le (Finite.le_ciSup_of_le 0 le_rfl)
    (Finite.le_ciSup_of_le 1 le_rfl))
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- At a finite place, a coprime pair of integers has maximal absolute value `1`. -/
theorem finitePlace_max_eq_one (v : FinitePlace K) {a b : ℤ} (hab : IsCoprime a b) :
    max (v (a : K)) (v (b : K)) = 1 := by
  have hv : IsNonarchimedean (v : K → ℝ) := FinitePlace.add_le v
  have H (n : ℤ) : v (n : K) ≤ 1 :=
    hv.apply_intCast_le_one (map_zero_le v 1) (map_one v) (map_neg_eq_map v)
  obtain ⟨s, t, hst⟩ := hab
  refine le_antisymm (max_le (H a) (H b)) ?_
  have h1 : (1 : ℝ) = v ((s : K) * a + (t : K) * b) := by
    have : ((s : K) * a + (t : K) * b) = ((s * a + t * b : ℤ) : K) := by push_cast; ring
    rw [this, hst]; simp
  rw [h1]
  refine (hv _ _).trans (max_le_max ?_ ?_)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H s)
  · rw [map_mul]; exact mul_le_of_le_one_left (apply_nonneg v _) (H t)

/-- The multiplicative height over `K` of a coprime integer pair `[a : b]` is
`max(|a|, |b|)^[K:ℚ]`. -/
theorem mulHeight_intPair {a b : ℤ} (hab : IsCoprime a b) (hb : b ≠ 0) :
    mulHeight ![(a : K), (b : K)] = (max |(a : ℝ)| |(b : ℝ)|) ^ Module.finrank ℚ K := by
  have hx : ![(a : K), (b : K)] ≠ 0 := by
    intro h
    have := congrFun h 1
    simp at this
    exact hb this
  rw [NumberField.mulHeight_eq hx]
  have hfin : (∏ᶠ v : FinitePlace K, ⨆ i, v (![(a : K), (b : K)] i)) = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [iSup_fin_two]
    simpa using finitePlace_max_eq_one v hab
  rw [hfin, mul_one]
  have hinf : ∀ v : InfinitePlace K, (⨆ i, v (![(a : K), (b : K)] i)) = max |(a : ℝ)| |(b : ℝ)| := by
    intro v
    rw [iSup_fin_two]
    simp [InfinitePlace.map_intCast, Int.norm_eq_abs]
  simp_rw [hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

/-- **Height of a rational number in a number field.** `h_K(q) = [K:ℚ] · log max(|num|, den)`. -/
theorem logHeight₁_algebraMap_rat (q : ℚ) :
    logHeight₁ (algebraMap ℚ K q) =
      Module.finrank ℚ K * log (max |(q.num : ℝ)| (q.den : ℝ)) := by
  have hden : ((q.den : ℤ) : K) ≠ 0 := by exact_mod_cast q.den_nz
  have e : algebraMap ℚ K q = ((q.num : ℤ) : K) / ((q.den : ℤ) : K) := by
    conv_lhs => rw [← Rat.num_div_den q]
    simp
  rw [e, logHeight₁_div_eq_logHeight, logHeight_eq_log_mulHeight,
    mulHeight_intPair (Rat.isCoprime_num_den q) (by exact_mod_cast q.den_nz), Real.log_pow]
  congr 2
  push_cast
  rw [abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℝ) < q.den)]

end GlueAssembly


/-!
# E2-E4 and F3 arithmetic of N5 (h-trust steps E2, E3, E4, F3), and the CM-branch arithmetic

Real-number lemmas. Their hypotheses are the numerical outputs of the literature theorems
(Javanpeykar, Gaudron–Rémond Thm 1.4, Faltings' Lemma 5 with additivity, Bost, Pazuki); their
conclusions are N5's displayed bounds.
-/

namespace GlueAssembly

open Real ZInQ

/-! ### E3-E4: the non-CM transfer (N5 L868-905) -/

/-- **E3-E4 arithmetic, wk-h's form** (`scratch/wk-h/Arakelov.lean`, re-proved here). -/
theorem transfer_numerics {Q M hFJ g d L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hg2 : 2 ≤ g) (hg : g ≤ Q ^ 3 * M ^ 4) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hJ : hFJ ≤ Q ^ 13 * M ^ 24)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hZ : -(2 * g) ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  set P := Q * M ^ 4 with hPdef
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hM4 : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ hM
  have hP : (10 : ℝ) ^ 12 ≤ P := by
    calc (10 : ℝ) ^ 12 = 10 ^ 12 * 1 := by ring
      _ ≤ Q * M ^ 4 := by gcongr
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogP : log P ≤ P := le_trans (log_le_sub_one_of_pos hP0) (by linarith)
  have hl1 : log (14 * g) ≤ 4 * P := by
    have h14 : 14 * g ≤ P ^ 4 := by
      have hM12 : (1 : ℝ) ≤ M ^ 12 := one_le_pow₀ hM
      calc 14 * g ≤ 14 * (Q ^ 3 * M ^ 4) := by linarith
        _ ≤ Q * (Q ^ 3 * M ^ 4) * M ^ 12 := by
            have : (14 : ℝ) ≤ Q := le_trans (by norm_num) hQ
            have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hM12 (mul_nonneg (by positivity : (0:ℝ) ≤ Q) h0)]
        _ = P ^ 4 := by rw [hPdef]; ring
    calc log (14 * g) ≤ log (P ^ 4) := log_le_log (by linarith) h14
      _ = 4 * log P := by rw [log_pow]; norm_num
      _ ≤ 4 * P := by linarith
  have hl2 : log d ≤ P := by
    have : d ≤ P := by
      calc d ≤ Q * M := hd
        _ ≤ Q * M ^ 4 := by
            gcongr
            calc M = M ^ 1 := (pow_one M).symm
              _ ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    linarith [log_le_log (by linarith) this]
  have hl3 : log (max hFJ (max (log d) 1)) ≤ 13 * P := by
    have hY : max hFJ (max (log d) 1) ≤ P ^ 13 := by
      have hP13 : P ≤ P ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
      have hQM : Q ^ 13 * M ^ 24 ≤ P ^ 13 := by
        rw [hPdef, mul_pow, ← pow_mul]
        gcongr
        · norm_num
      refine max_le (hJ.trans hQM) (max_le ?_ ?_)
      · linarith [log_le_sub_one_of_pos (by linarith : (0:ℝ) < d)]
      · linarith
    calc log (max hFJ (max (log d) 1)) ≤ log (P ^ 13) :=
          log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hY
      _ = 13 * log P := by rw [log_pow]; norm_num
      _ ≤ 13 * P := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hlog14 : 0 ≤ log (14 * g) := log_nonneg (by linarith)
  have hL' : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by
    refine hL.trans ?_
    gcongr
  have hg3 : g ^ 3 ≤ (Q ^ 3 * M ^ 4) ^ 3 := by gcongr
  have hg2' : g ^ 2 ≤ (Q ^ 3 * M ^ 4) ^ 2 := by gcongr
  have hL'' : L ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) := by
    refine hL'.trans ?_
    have : 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) ≤
        64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P := by nlinarith
    have h0 : 0 ≤ 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) := by positivity
    calc 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P))
        ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by gcongr
      _ ≤ _ := by gcongr
  have hT : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) ≤
      262144 * Q ^ 16 * M ^ 24 + 27648 * Q ^ 16 * M ^ 24 := by
    rw [hPdef]
    have hM8 : (1 : ℝ) ≤ M ^ 8 := one_le_pow₀ hM
    have hQ6 : (1 : ℝ) ≤ Q ^ 6 := one_le_pow₀ hQ1
    have e1 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * (Q * M ^ 4))) =
        262144 * Q ^ 16 * M ^ 24 := by ring
    have e2 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (27 * (Q * M ^ 4)) = 27648 * (Q ^ 10 * M ^ 16) := by ring
    have e3 : Q ^ 10 * M ^ 16 ≤ Q ^ 16 * M ^ 24 := by
      have : Q ^ 16 * M ^ 24 = (Q ^ 10 * M ^ 16) * (Q ^ 6 * M ^ 8) := by ring
      rw [this]
      have h0 : 0 ≤ Q ^ 10 * M ^ 16 := by positivity
      nlinarith [one_le_mul_of_one_le_of_one_le hQ6 hM8]
    nlinarith [e1, e2, e3]
  have hlow : Q ^ 3 * M ^ 4 ≤ Q ^ 16 * M ^ 24 := by
    have h1 : (1 : ℝ) ≤ Q ^ 13 := one_le_pow₀ hQ1
    have h2 : (1 : ℝ) ≤ M ^ 20 := one_le_pow₀ hM
    have : Q ^ 16 * M ^ 24 = (Q ^ 3 * M ^ 4) * (Q ^ 13 * M ^ 20) := by ring
    rw [this]
    have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
    nlinarith [one_le_mul_of_one_le_of_one_le h1 h2]
  have hJ' : Q ^ 13 * M ^ 24 ≤ Q ^ 16 * M ^ 24 := by
    have : Q ^ 13 ≤ Q ^ 16 := pow_le_pow_right₀ hQ1 (by norm_num)
    gcongr
  have hfin : Q ^ 16 * M ^ 24 * 10 ^ 12 ≤ Q ^ 17 * M ^ 24 := by
    have : Q ^ 17 * M ^ 24 = Q ^ 16 * M ^ 24 * Q := by ring
    rw [this]; gcongr
  have hT0 : 0 ≤ Q ^ 16 * M ^ 24 := by positivity
  nlinarith

/-- **E2-E4 arithmetic from the level** (N5 L868-905): from the conductor bound `N ≤ QM²` (D5),
Javanpeykar's bound at `X₁(N)` (`h_F(J) ≤ 1.3·10⁷ N¹²`, `2 ≤ g ≤ N²`), `[L':ℚ] ≤ QM`, the
Gaudron–Rémond degree bound, Faltings' height variation with additivity, and Bost's lower bound
`h_F(Z) ≥ −(3/2)·dim Z` with `dim Z ≤ g`, conclude `h_F(A) ≤ Q¹⁷M²⁴`. -/
theorem transfer_of_level {Q M N g d hFJ L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hN1 : 1 ≤ N) (hN : N ≤ Q * M ^ 2) (hJav : hFJ ≤ 13000000 * N ^ 12)
    (hg2 : 2 ≤ g) (hg : g ≤ N ^ 2) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hBost : -(3 / 2) * g ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hN0 : 0 ≤ N := by linarith
  have hN12 : N ^ 12 ≤ Q ^ 12 * M ^ 24 := by
    calc N ^ 12 ≤ (Q * M ^ 2) ^ 12 := by gcongr
      _ = Q ^ 12 * M ^ 24 := by ring
  have hJ : hFJ ≤ Q ^ 13 * M ^ 24 := by
    have h0 : 0 ≤ Q ^ 12 * M ^ 24 := by positivity
    calc hFJ ≤ 13000000 * N ^ 12 := hJav
      _ ≤ 13000000 * (Q ^ 12 * M ^ 24) := by gcongr
      _ ≤ Q * (Q ^ 12 * M ^ 24) := by gcongr; linarith
      _ = Q ^ 13 * M ^ 24 := by ring
  have hg' : g ≤ Q ^ 3 * M ^ 4 := by
    calc g ≤ N ^ 2 := hg
      _ ≤ (Q * M ^ 2) ^ 2 := by gcongr
      _ = Q ^ 2 * M ^ 4 := by ring
      _ ≤ Q ^ 3 * M ^ 4 := by
          have : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
          gcongr
  exact transfer_numerics hQ hM hg2 hg' hd1 hd hJ hL hvar (by linarith)

/-! ### CM branch (N5 L581-631): `h_F(A) ≤ C_cm` -/

theorem log_two_mul_bcm_le {D : ℝ} (hD : 1 ≤ D) (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) :
    log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 := by
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
  have hle : 2 * (D ^ 2 * 3 ^ n + 1) ≤ 4 * (D ^ 2 * 3 ^ n) := by nlinarith
  have hpos : 0 < 2 * (D ^ 2 * 3 ^ n + 1) := by positivity
  have hlog4 : log 4 ≤ 2 := by
    have : (4 : ℝ) ≤ exp 2 := by
      have := add_one_le_exp (2 : ℝ)
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 4 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlog3 : log 3 ≤ 2 := by
    have : (3 : ℝ) ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 3 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlogD : log D ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  calc log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ log (4 * (D ^ 2 * 3 ^ n)) := log_le_log hpos hle
    _ = log 4 + 2 * log D + n * log 3 := by
        rw [log_mul (by norm_num) (by positivity), log_mul (by positivity) (by positivity),
          log_pow, log_pow]
        push_cast; ring
    _ ≤ 2 + 2 * D + 42000 * D ^ 2 := by
        rw [hn]
        have : 21000 * D ^ 2 * log 3 ≤ 21000 * D ^ 2 * 2 := by gcongr
        linarith

/-- **CM-branch arithmetic** (N5 L606-628): `h_F(E) ≤ B_cm`, `[L:ℚ] ≤ D`, Gaudron–Rémond with
source `E²` (`g = 2`: exponent `1024·2³ = 8192`, `(14·2)^{64·2²} = 28^{256}`), height variation
and additivity give `h_F(A) ≤ C_cm = 2B_cm + 4096(1028 + 5D + 84000D²)`. -/
theorem cm_numerics {D d hE L hA : ℝ} (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) (hD : 1 ≤ D)
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ D ^ 2 * 3 ^ n + 1)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) :
    hA ≤ 2 * (D ^ 2 * 3 ^ n + 1) + 4096 * (1028 + 5 * D + 84000 * D ^ 2) := by
  set B := D ^ 2 * 3 ^ n + 1 with hB
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hBD : D ≤ B := by rw [hB]; nlinarith
  have hlogd : log d ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hmax : max (2 * hE) (max (log d) 1) ≤ 2 * B :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have hlogmax : log (max (2 * hE) (max (log d) 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 :=
    (log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hmax).trans
      (log_two_mul_bcm_le hD n hn)
  have hlog28 : log 28 ≤ 4 := by
    have : (28 : ℝ) ≤ exp 4 := by
      have h4 : exp 4 = (exp 1) ^ 4 := by rw [← exp_nat_mul]; norm_num
      have he := exp_one_gt_d9
      rw [h4]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 4]
    calc log 28 ≤ log (exp 4) := log_le_log (by norm_num) this
      _ = 4 := log_exp 4
  have : L ≤ 8192 * (1028 + 5 * D + 84000 * D ^ 2) := by
    refine hL.trans ?_
    nlinarith
  linarith

/-! ### F3: Pazuki's bound in N5's normalization (N5 L934-947) -/

theorem log_sixteen_le : log (2 ^ 4 : ℝ) ≤ 3 := by
  have : (2 ^ 4 : ℝ) ≤ exp 3 := by
    have h3 : exp 3 = (exp 1) ^ 3 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]
  calc log (2 ^ 4 : ℝ) ≤ log (exp 3) := log_le_log (by norm_num) this
    _ = 3 := log_exp 3

/-- **F3 arithmetic.** From Pazuki's Cor. 1.3(2) for `g = 2`, `r = 2` in the Deligne metric,
`h_Θ ≤ X_D/2 + C₂ log(X_D + 2)` with `X_D = max(1, h_F(A) + log π)` and
`C₂ = 1000·2⁴·(log 2⁴)⁵`, conclude `h ≤ 10⁴·2²⁴·max(1, h_F(A))`. -/
theorem pazuki_numerics {hz hA : ℝ}
    (hP : hz ≤ max 1 (hA + log π) / 2 +
      1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)) :
    hz ≤ 10000 * 2 ^ 24 * max 1 hA := by
  set X := max 1 hA with hX
  set XD := max 1 (hA + log π) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hlogpi : log π ≤ 2 := by
    have : π ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      have hpi := pi_lt_d2
      nlinarith
    calc log π ≤ log (exp 2) := log_le_log pi_pos this
      _ = 2 := log_exp 2
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hXD3 : XD ≤ 3 * X := by
    refine max_le (by linarith) ?_
    have : hA ≤ X := le_max_right _ _
    linarith
  have hlogXD : log (XD + 2) ≤ 2 * XD := by
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC0 : 0 ≤ log (2 ^ 4 : ℝ) := log_nonneg (by norm_num)
  have hC : (log (2 ^ 4 : ℝ)) ^ 5 ≤ 243 := by
    calc (log (2 ^ 4 : ℝ)) ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ hC0 log_sixteen_le 5
      _ = 243 := by norm_num
  have hlog0 : 0 ≤ log (XD + 2) := log_nonneg (by linarith)
  have h1 : 1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (XD + 2) ≤ 1000 * 2 ^ 4 * 243 * (6 * X) := by
    have : log (XD + 2) ≤ 6 * X := by linarith
    gcongr
  have h2 : XD / 2 ≤ 3 * X / 2 := by linarith
  have h3 := hP.trans (add_le_add h2 h1)
  have h4 : 3 * X / 2 + 1000 * 2 ^ 4 * 243 * (6 * X) ≤ 10000 * 2 ^ 24 * X := by nlinarith
  exact h3.trans h4

end GlueAssembly


/-!
# Copy of `ZInQKernel/Hypotheses/JHeight.lean` (F4), for scratch use

Scratch files cannot import `ZInQKernel.Hypotheses.JHeight` in this worktree (its import chain
reaches the unbuilt upstream package `lean/`). The F4 part of that file is copied verbatim
(namespace changed); `SixContactMinAt S` is `SixContactMin` at `S = Mult.S_mul` by `rfl`.
-/

namespace GlueAssembly

open ZInQ

/-- The binary sextic `F_h(a,b) = a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b)`. -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- `C₀ = 57600²·3⁷·(2¹⁰3⁸5⁶)⁷`, the bound for the cancellation in `J(u)`. -/
def C0 : ℤ := (57600 * 3 ^ 7) * (57600 * 104976000000 ^ 7)

/-- **Cancellation bound.** For coprime `a, b`, a common divisor of `57600F_h²` and `G_h⁶` divides
`C₀` (from `cert_x`, `cert_y` raised to the 7th power). -/
theorem dvd_C0 {a b c : ℤ} (hab : IsCoprime a b) (hP : c ∣ 57600 * Fh a b ^ 2)
    (hQ : c ∣ Gh a b ^ 6) : c ∣ C0 := by
  have key : ∀ x y : ℤ, 57600 * (x + y) ^ 7 =
      57600 * x ^ 2 * (x ^ 5 + 7 * x ^ 4 * y + 21 * x ^ 3 * y ^ 2 + 35 * x ^ 2 * y ^ 3 +
        35 * x * y ^ 4 + 21 * y ^ 5) + y ^ 6 * (57600 * (7 * x + y)) := by intros; ring
  have hsplit : ∀ (A B : ℤ), c ∣ 57600 * (A * Fh a b + B * Gh a b) ^ 7 := by
    intro A B
    rw [key]
    refine dvd_add ?_ ?_
    · have : 57600 * (A * Fh a b) ^ 2 = (57600 * Fh a b ^ 2) * A ^ 2 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hP _
    · have : (B * Gh a b) ^ 6 = Gh a b ^ 6 * B ^ 6 := by ring
      rw [this, mul_assoc]; exact dvd_mul_of_dvd_left hQ _
  have hx : c ∣ 57600 * 3 ^ 7 * a ^ 49 := by
    have e : 57600 * 3 ^ 7 * a ^ 49 = 57600 * (3 * a ^ 7) ^ 7 := by ring
    rw [e, cert_x]; exact hsplit _ _
  have hy : c ∣ 57600 * 104976000000 ^ 7 * b ^ 49 := by
    have e : 57600 * 104976000000 ^ 7 * b ^ 49 = 57600 * (104976000000 * b ^ 7) ^ 7 := by ring
    rw [e, cert_y]; exact hsplit _ _
  obtain ⟨s, t, hst⟩ := hab.pow (m := 49) (n := 49)
  have e : C0 = (57600 * 104976000000 ^ 7 * s) * (57600 * 3 ^ 7 * a ^ 49) +
      (57600 * 3 ^ 7 * t) * (57600 * 104976000000 ^ 7 * b ^ 49) := by
    have : C0 = C0 * (s * a ^ 49 + t * b ^ 49) := by rw [hst, mul_one]
    rw [this, C0]; ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right hy _)

theorem abs_monomial_le {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (i j : ℕ) :
    |a ^ i * b ^ j| ≤ m ^ (i + j) := by
  have hm : 0 ≤ m := (abs_nonneg a).trans ha
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ha _) (pow_le_pow_left₀ (abs_nonneg _) hb _)
    (by positivity) (by positivity)

/-- **Lower bound.** With `m = max(|a|, |b|) > 0`: `m¹² ≤ 10⁴⁸ max(57600F_h², G_h⁶)`. -/
theorem lower_bound {a b m : ℤ} (ha : |a| ≤ m) (hb : |b| ≤ m) (hm : 0 < m)
    (hmax : m = |a| ∨ m = |b|) :
    m ^ 12 ≤ 10 ^ 48 * max (57600 * Fh a b ^ 2) (Gh a b ^ 6) := by
  by_contra hlt
  push Not at hlt
  have hP := le_max_left (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hQ := le_max_right (57600 * Fh a b ^ 2) (Gh a b ^ 6)
  have hF : 240 * 10 ^ 24 * |Fh a b| < m ^ 6 := by
    have h2 : (240 * 10 ^ 24 * |Fh a b|) ^ 2 < (m ^ 6) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hG : 10 ^ 8 * |Gh a b| < m ^ 2 := by
    have h6 : (10 ^ 8 * |Gh a b|) ^ 6 < (m ^ 2) ^ 6 := by
      rw [mul_pow, pow_abs, abs_of_nonneg (by positivity : (0:ℤ) ≤ Gh a b ^ 6)]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 6 (by positivity) h6
  have hX : 240 * 10 ^ 24 * (m * |Fh a b|) < m ^ 7 := by nlinarith
  have hY : 10 ^ 8 * (m ^ 5 * |Gh a b|) < m ^ 7 := by
    have : (0 : ℤ) < m ^ 5 := by positivity
    nlinarith
  have m10 : -m ≤ a ∧ a ≤ m := abs_le.mp ha
  have m01 : -m ≤ b ∧ b ≤ m := abs_le.mp hb
  have mono : ∀ i j : ℕ, i + j = 5 → -m ^ 5 ≤ a ^ i * b ^ j ∧ a ^ i * b ^ j ≤ m ^ 5 := by
    intro i j hij
    have := abs_monomial_le ha hb i j
    rw [hij] at this
    exact abs_le.mp this
  have m50 := mono 5 0 rfl
  have m41 := mono 4 1 rfl
  have m32 := mono 3 2 rfl
  have m23 := mono 2 3 rfl
  have m14 := mono 1 4 rfl
  have m05 := mono 0 5 rfl
  simp only [pow_one, pow_zero, mul_one, one_mul] at m50 m41 m32 m23 m14 m05
  have hm7 : (0 : ℤ) < m ^ 7 := by positivity
  have tri : ∀ A B : ℤ, |A * Fh a b + B * Gh a b| ≤ |A| * |Fh a b| + |B| * |Gh a b| := by
    intro A B; rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
  rcases hmax with h | h
  · have hA : |-200 * a - 4800 * b| ≤ 5000 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4| ≤ 20328129 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-200 * a - 4800 * b) (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 +
      2880000 * a ^ 2 * b ^ 3 + 17280000 * a * b ^ 4)
    rw [← cert_x, abs_mul, abs_pow, ← h, show |(3 : ℤ)| = 3 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith
  · have hA : |-1001 * a - 37650 * b| ≤ 38651 * m := by
      rw [abs_le]; constructor <;> linarith
    have hB : |143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 +
        20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5| ≤
        184009200 * m ^ 5 := by
      rw [abs_le]; constructor <;> linarith
    have e := tri (-1001 * a - 37650 * b) (143 * a ^ 5 + 20557 * a ^ 4 * b +
      1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5)
    rw [← cert_y, abs_mul, abs_pow, ← h, show |(104976000000 : ℤ)| = 104976000000 by norm_num] at e
    have e1 := mul_le_mul_of_nonneg_right hA (abs_nonneg (Fh a b))
    have e2 := mul_le_mul_of_nonneg_right hB (abs_nonneg (Gh a b))
    linarith

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 450` for `u ∉ 𝒞` (N5: `h(u) < h(J(u)) + 74`). -/
theorem twelve_mul_ratHeight_le (u : ℚ) (_hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 450 := by
  set a : ℤ := u.num with ha_def
  set b : ℤ := (u.den : ℤ) with hb_def
  have hb : 0 < b := by rw [hb_def]; exact_mod_cast u.den_pos
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact u.reduced
  have hu_eq : u = (a : ℚ) / (b : ℚ) := by
    rw [ha_def, hb_def]; push_cast; exact (Rat.num_div_den u).symm
  have hFq : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) =
      (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fh; push_cast; field_simp
  have hGq : 7 * u ^ 2 + 300 * u + 3600 = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gh; push_cast; field_simp
  have hG0 : 0 < Gh a b := by unfold Gh; nlinarith [sq_nonneg (7 * a + 150 * b), mul_pos hb hb]
  set n : ℤ := -(57600 * Fh a b ^ 2) with hn_def
  set d : ℤ := Gh a b ^ 6 with hd_def
  have hdpos : 0 < d := by positivity
  have hJ : Jmap u = (n : ℚ) / (d : ℚ) := by
    have hGq0 : (Gh a b : ℚ) ≠ 0 := by exact_mod_cast hG0.ne'
    unfold Jmap; rw [hFq, hGq, hn_def, hd_def]; push_cast; field_simp
  obtain ⟨c, hn, hd⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den n hdpos.ne'
  rw [← hJ] at hn hd
  set J := Jmap u with hJdef
  have hden : (0 : ℤ) < (J.den : ℤ) := by exact_mod_cast J.den_pos
  have hcpos : 0 < c := by
    by_contra h; push Not at h; rw [hd] at hdpos; nlinarith
  have hcdvd : c ∣ C0 := dvd_C0 hcop (dvd_neg.mp (Dvd.intro _ hn.symm)) (Dvd.intro _ hd.symm)
  have hcle : c ≤ C0 := Int.le_of_dvd (by norm_num [C0]) hcdvd
  have hmaxeq : max (57600 * Fh a b ^ 2) d = c * max |J.num| (J.den : ℤ) := by
    have h1 : 57600 * Fh a b ^ 2 = |n| := by
      rw [hn_def, abs_neg, abs_of_nonneg (by positivity)]
    rw [h1, hn, hd, abs_mul, abs_of_pos hcpos, mul_max_of_nonneg _ _ hcpos.le]
  set m := max |a| b with hm_def
  have hm : 0 < m := lt_of_lt_of_le hb (le_max_right _ _)
  have hlow := lower_bound (a := a) (b := b) (le_max_left |a| b)
    (by rw [abs_of_pos hb]; exact le_max_right _ _) hm
    (by rcases max_choice |a| b with h | h
        · left; exact h
        · right; rw [abs_of_pos hb]; exact h)
  rw [hmaxeq] at hlow
  set H := max |J.num| (J.den : ℤ) with hH_def
  have hH : 1 ≤ H := le_max_of_le_right (by exact_mod_cast J.den_pos)
  have hlow2 : m ^ 12 ≤ 10 ^ 139 * H := by
    have hC : 10 ^ 48 * C0 ≤ 10 ^ 139 := by norm_num [C0]
    calc m ^ 12 ≤ 10 ^ 48 * (c * H) := hlow
      _ ≤ 10 ^ 48 * (C0 * H) := by gcongr
      _ = (10 ^ 48 * C0) * H := by ring
      _ ≤ 10 ^ 139 * H := by gcongr
  have hu_h : ratHeight u = Real.log (m : ℝ) := by
    unfold ratHeight; rw [hm_def]; push_cast [ha_def, hb_def]; rfl
  have hJ_h : ratHeight J = Real.log (H : ℝ) := by
    unfold ratHeight; rw [hH_def]; push_cast; rfl
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlowR : (m : ℝ) ^ 12 ≤ 10 ^ 139 * (H : ℝ) := by exact_mod_cast hlow2
  have hlog10 : Real.log 10 < 3 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have h1 := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : (2.7 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
      pow_lt_pow_left₀ (by linarith) (by norm_num) (by norm_num)
    rw [this]; norm_num at h2 ⊢; linarith
  have key : 12 * Real.log (m : ℝ) ≤ 139 * Real.log 10 + Real.log (H : ℝ) := by
    have := Real.log_le_log (by positivity) hlowR
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at this
    push_cast at this
    linarith
  rw [hu_h, hJ_h]
  linarith

/-- `M_S(u) > 0` (copied from `Hypotheses/HeightMin.lean`). -/
theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- The constant `X(R) = max(1, C_cm, Q_R¹⁷)` of N5's final display (as in `JHeight.lean`). -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- `JHeightBound S` (as in `JHeight.lean`). -/
def JHeightBound (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

/-- `SixContactMin` at a prime set `S`; `SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin`
(`Hypotheses/HeightMin.lean`) by `rfl`. -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24

theorem heightH6_eq (R : ℝ) : heightH6 R = 2 * 10 ^ 13 * heightX R := rfl

/-- `JHeightBound S → SixContactMinAt S` (as `sixContactMin_of_jHeightBound` in `JHeight.lean`). -/
theorem sixContactMinAt_of_jHeightBound {S : Finset ℕ} (hJ : JHeightBound S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  rw [heightH6_eq]
  nlinarith

end GlueAssembly

/-!
# The assembly: from the numerical outputs of E2-E4, F1, F3 to `SixContactMinAt S`

`GlueOutputs S` is a conjunction, for every `u ∉ 𝒞`, of the numerical outputs that steps
A1-E1 (modularity half), E2-E4 (Javanpeykar, Gaudron–Rémond, Faltings, Bost), F1 (the theta
expression of `j`) and F3 (Pazuki) give. Lean checks the assembly: F2 (`logHeight_Phi_le`, over
Mathlib's Weil height), the invariance of the height of a rational number in a number field
(`logHeight₁_algebraMap_rat`), the E-arithmetic (`transfer_of_level`, `cm_numerics`), the
F3-arithmetic (`pazuki_numerics`), F4 (`twelve_mul_ratHeight_le`) and the final constant.

`GlueOutputs S` is NOT a faithful statement of the literature theorems: the abelian varieties and
their Faltings heights do not exist in Mathlib, so they appear only as real numbers with the
inequalities the theorems give. As a Lean Prop it is a height bound in disguise (wk-h §4.3).
What is faithful is the theta point: a genuine point of `K¹⁰` with its genuine Weil height.
-/

namespace GlueAssembly

open Real ZInQ Height

/-- A bundled number field. -/
structure NF where
  K : Type
  [fld : Field K]
  [nf : NumberField K]

attribute [instance] NF.fld NF.nf

/-- **Outputs of the non-CM transfer (A1-E1, E2, E3, E4)**, for `Q = Q_D`, `M = M_S(u)`, and
`hA` the stable Faltings height of `A`: a level `N` with `1 ≤ N ≤ QM²` (D5); `g = dim J₁(N)`
with `2 ≤ g ≤ N²` and `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` (Javanpeykar, `g, deg_B ≤ N²`); `d = [L':ℚ]`
with `1 ≤ d ≤ QM` (B3); `L = log deg φ` for the Gaudron–Rémond isogeny `J₁(N) → A × Z` (E1,
E3); `h_F(A) + h_F(Z) ≤ h_F(J₁(N)) + L/2` (Faltings' Lemma 5 and additivity) and
`h_F(Z) ≥ −(3/2)g` (Bost, `dim Z ≤ g`). -/
def NonCMOutput (Q M hA : ℝ) : Prop :=
  ∃ N g d hFJ L hZ : ℝ, 1 ≤ N ∧ N ≤ Q * M ^ 2 ∧ hFJ ≤ 13000000 * N ^ 12 ∧
    2 ≤ g ∧ g ≤ N ^ 2 ∧ 1 ≤ d ∧ d ≤ Q * M ∧
    L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))) ∧
    hA + hZ ≤ hFJ + L / 2 ∧ -(3 / 2) * g ≤ hZ

/-- **Outputs of the CM branch (N5 L581-628)**: `d = [L:ℚ] ≤ D`, `h_F(E) ≤ B_cm`, `L = log deg`
of the Gaudron–Rémond isogeny `E² → A`, and `h_F(A) ≤ 2h_F(E) + L/2`. -/
def CMOutput (hA : ℝ) : Prop :=
  ∃ d hE L : ℝ, 1 ≤ d ∧ d ≤ heightD ∧ hE ≤ heightBcm ∧
    L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))) ∧
    hA ≤ 2 * hE + L / 2

/-- **Output of F3 (Pazuki, Cor. 1.3(2), `g = r = 2`, Deligne metric)** for the absolute
sup-norm height `hz` of the even theta nulls. -/
def PazukiOutput (hz hA : ℝ) : Prop :=
  hz ≤ max 1 (hA + log π) / 2 +
    1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)

/-- **The glue interface.** For every `u ∉ 𝒞`: a number field `K`, the ten even theta nulls
`z ∈ K¹⁰` of the QM surface `A` over `J(u)` (F1: `Φ(z) = J(u)`), the Faltings height `hA` of
`A`, Pazuki's bound for the absolute Weil height `h(z) = h_K(z)/[K:ℚ]` (F3), and the outputs of
either the non-CM transfer (at `Q = Q_D`, `M = M_S(u)`) or the CM branch. -/
def GlueOutputs (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (z : Fin 10 → K.K) (hA : ℝ),
    3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
    PazukiOutput (logHeight z / Module.finrank ℚ K.K) hA ∧
    (NonCMOutput (heightQ heightD) (contactSupport S u) hA ∨ CMOutput hA)

/-- `Q_D ≥ D ≥ 10¹²`. -/
theorem heightQ_heightD_ge : (10 : ℝ) ^ 12 ≤ heightQ heightD := by
  have hD : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hD1 : (1 : ℝ) ≤ heightD := le_trans (by norm_num) hD
  have hDpos : 0 < heightD := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  have hE : (1 : ℝ) ≤ heightE0 := by
    have : 1 ≤ heightE0 := by
      rw [ZInQ.Compiler.Precision.heightE0_eq]
      have hG : 0 < heightG0 := by unfold heightG0; norm_num
      have := Nat.mul_pos hDpos hG
      have := pow_pos this 2
      omega
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ (heightD : ℝ) * heightE0 := one_le_mul_of_one_le_of_one_le hD1 hE
  calc (10 : ℝ) ^ 12 ≤ heightD := hD
    _ = (heightD : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    _ ≤ (heightD : ℝ) ^ ((heightD : ℝ) * heightE0) := rpow_le_rpow_of_exponent_le hD1 h1
    _ = heightQ heightD := rfl

/-- Casting `C_cm`'s defining equation, over variables (the kernel cannot unfold the constants;
see `ZInQKernel/Compiler/Precision/HeightConstant.lean`). -/
theorem cast_ccm {C B D : ℕ} (h : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) :
    (C : ℝ) = 2 * (B : ℝ) + 4096 * (1028 + 5 * (D : ℝ) + 84000 * (D : ℝ) ^ 2) := by
  rw [h]; push_cast; ring

/-- The CM branch over variables: `h_F(A) ≤ C_cm` (applied to the constants through their
defining equations only). -/
theorem cm_branch_nat {D B C : ℕ} (hBe : B = D ^ 2 * 3 ^ (21000 * D ^ 2) + 1)
    (hCe : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) (hD : 1 ≤ D) {d hE L hA : ℝ}
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ B)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) : hA ≤ C := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hB : (B : ℝ) = (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := by rw [hBe]; push_cast; ring
  have hnR : ((21000 * D ^ 2 : ℕ) : ℝ) = 21000 * (D : ℝ) ^ 2 := by push_cast; ring
  have hcm := cm_numerics (21000 * D ^ 2) hnR hD1 hd1 hd (hEB.trans (le_of_eq hB)) hL hvar
  rw [cast_ccm hCe, hB]
  exact hcm

theorem one_le_heightD_real : (1 : ℝ) ≤ heightD := by
  have : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  linarith

/-- Non-CM half of the E-part: `max(1, h_F(A)) ≤ X(D)·M²⁴`. -/
theorem max_one_hA_le_noncm {M hA : ℝ} (hM : 1 ≤ M) (h : NonCMOutput (heightQ heightD) M hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨N, g, d, hFJ, L, hZ, hN1, hN, hJav, hg2, hg, hd1, hd, hL, hvar, hBost⟩ := h
  have h1 := transfer_of_level heightQ_heightD_ge hM hN1 hN hJav hg2 hg hd1 hd hL hvar hBost
  have hQX : heightQ heightD ^ 17 ≤ heightX heightD :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM24 : 0 ≤ M ^ 24 := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_right hQX hM24)

/-- CM half of the E-part. -/
theorem max_one_hA_le_cm {M hA : ℝ} (hM : 1 ≤ M) (h : CMOutput hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨d, hE, L, hd1, hd, hEB, hL, hvar⟩ := h
  have hDn : 1 ≤ heightD := le_trans (by norm_num) ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hcm := cm_branch_nat ZInQ.Compiler.Precision.heightBcm_eq
    ZInQ.Compiler.Precision.heightCcm_eq hDn hd1 hd hEB hL hvar
  have hCX : (heightCcm : ℝ) ≤ heightX heightD :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hX1 : 0 ≤ heightX heightD := le_trans zero_le_one (le_max_left _ _)
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  calc hA ≤ heightCcm := hcm
    _ ≤ heightX heightD := hCX
    _ ≤ heightX heightD * M ^ 24 := le_mul_of_one_le_right hX1 hM24

/-- The E-part of the assembly: `max(1, h_F(A)) ≤ X(D)·M²⁴` in both branches (N5 L903-905). -/
theorem max_one_hA_le {M hA : ℝ} (hM : 1 ≤ M)
    (h : NonCMOutput (heightQ heightD) M hA ∨ CMOutput hA) :
    max 1 hA ≤ heightX heightD * M ^ 24 := by
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  have hX1 : 1 ≤ heightX heightD := le_max_left _ _
  refine max_le (le_trans hX1 (le_mul_of_one_le_right (by linarith) hM24)) ?_
  rcases h with h | h
  · exact max_one_hA_le_noncm hM h
  · exact max_one_hA_le_cm hM h

theorem log_3779136_le : log 3779136 ≤ 16 := by
  have : (3779136 : ℝ) ≤ exp 16 := by
    have h : exp 16 = (exp 1) ^ 16 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 16]
  calc log 3779136 ≤ log (exp 16) := log_le_log (by norm_num) this
    _ = 16 := log_exp 16

/-- **F1 + F2 + invariance**: if `Φ(z) = j` for `j ∈ ℚ`, then
`h(j) ≤ 40·h_K(z)/[K:ℚ] + log 3779136`. -/
theorem ratHeight_le_of_theta {K : Type} [Field K] [NumberField K] (z : Fin 10 → K) (j : ℚ)
    (hF1 : 3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K j) :
    ratHeight j ≤ 40 * (logHeight z / Module.finrank ℚ K) + log 3779136 := by
  have h2 := logHeight₁_Phi_le z
  rw [hF1, logHeight₁_algebraMap_rat, NumberField.totalWeight_eq_finrank] at h2
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold ratHeight
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set L := log (max |(j.num : ℝ)| (j.den : ℝ))
  calc L = (n * L) / n := by field_simp
    _ ≤ (40 * logHeight z + n * log 3779136) / n := div_le_div_of_nonneg_right h2 hn.le
    _ = 40 * (logHeight z / n) + log 3779136 := by field_simp

/-- **The assembly.** `GlueOutputs S → JHeightBound S`. -/
theorem jHeightBound_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) : JHeightBound S := by
  intro u hu
  obtain ⟨K, z, hA, hF1, hPaz, hE⟩ := h u hu
  have hM : (1 : ℝ) ≤ contactSupport S u := by exact_mod_cast contactSupport_pos S u
  set Y := heightX heightD * (contactSupport S u : ℝ) ^ 24 with hY
  have hXM : max 1 hA ≤ Y := max_one_hA_le hM hE
  have hz := pazuki_numerics hPaz
  have hj := ratHeight_le_of_theta z (Jmap u) hF1
  have hY1 : 1 ≤ Y := (le_max_left 1 hA).trans hXM
  have hlog := log_3779136_le
  have : ratHeight (Jmap u) ≤ (40 * 10000 * 2 ^ 24 + 22 : ℝ) * Y := by nlinarith
  rw [hY] at this
  linarith

/-- **H from the glue interface.** `GlueOutputs S → SixContactMinAt S`; at `S = Mult.S_mul`
the conclusion is `ZInQ.SixContactMin`. -/
theorem sixContactMinAt_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) :
    SixContactMinAt S :=
  sixContactMinAt_of_jHeightBound (jHeightBound_of_glueOutputs h)

end GlueAssembly


end AssemblySec

section AsmC8Sec
/-! ### Copied from `scratch/glue-assembly/C8.lean` (compiled there). -/

/-!
# Elementary glue of step C8 (twist and weight) and of E1, over genuine Mathlib objects

* `weight_match`: the Hodge–Tate weight comparison `{n, n+1−k} = {0, −1}`, `k ≥ 1` ⇒ `k = 2`,
  `n = 0` (Tate normalization), and its cohomological variant.
* The determinant argument for the finiteness of the twisting character `ψ` (h-trust C8 items
  1-3), as group theory: (a) a character trivial-on-squares on a finite-index subgroup has finite
  image; (b) a character into the units of a field whose square has finite image has finite image.
  These are stated for an arbitrary group `G` (for C8, `G = G_ℚ` and `H = G_F`), with values in
  `Eˣ` for a field `E` (for C8, `E = \bar ℚ₅`).
-/

namespace GlueAssembly

/-- **Weight comparison, Tate normalization** (h-trust C8 "Check here"). If the weights
`{n, n + 1 − k}` of `ρ_g ⊗ χ^{-n}`-type twist equal `{0, −1}` as sets and `k ≥ 1`, then `k = 2`
and `n = 0`. -/
theorem weight_match {n k : ℤ} (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Finset ℤ) = {0, -1}) : k = 2 ∧ n = 0 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Finset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Finset ℤ) := by rw [h]; simp
  have hn : n ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  have hm : n + 1 - k ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 hn hm
  omega

/-- **Weight comparison, cohomological normalization** (Pan's convention, weights `{0, k − 1}`):
`{n, n + k − 1} = {0, −1}`, `k ≥ 1` ⇒ `k = 2`, `n = −1` (twist by `χ¹`, rv-h-c8 `weights.py`). -/
theorem weight_match_coh {n k : ℤ} (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Finset ℤ) = {0, -1}) : k = 2 ∧ n = -1 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Finset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Finset ℤ) := by rw [h]; simp
  have hn : n ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  have hm : n + k - 1 ∈ ({0, -1} : Finset ℤ) := by rw [← h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1 hn hm
  omega

/-- **Determinant argument, step 2** (h-trust C8 item 2): a homomorphism `α : G →* M` whose
values on a finite-index subgroup `H` lie in a finite set has finite image. For C8: `α = det r₅·χ⁻¹`,
`H = G_F`, `α(H) ⊆ {±1}`. -/
theorem finite_range_of_finiteIndex {G M : Type*} [Group G] [Group M] (α : G →* M)
    (H : Subgroup G) [H.FiniteIndex] (hH : (α '' H).Finite) : (Set.range α).Finite := by
  classical
  -- `G` is a finite union of cosets `g H`, and `α(gH) = α(g)·α(H)`.
  obtain ⟨T, hT⟩ : ∃ T : Finset G, ∀ g : G, ∃ t ∈ T, t⁻¹ * g ∈ H := by
    haveI := H.fintypeQuotientOfFiniteIndex
    refine ⟨(Finset.univ : Finset (G ⧸ H)).image fun q => q.out, fun g => ?_⟩
    refine ⟨(g : G ⧸ H).out, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    have := QuotientGroup.mk_out_eq_mul H g
    obtain ⟨h, hh⟩ := this
    rw [hh]; simp [mul_assoc]
  have hsub : Set.range α ⊆ ⋃ t ∈ T, (fun m => α t * m) '' (α '' H) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨t, ht, hg⟩ := hT g
    simp only [Set.mem_iUnion, Set.mem_image]
    exact ⟨t, ht, α (t⁻¹ * g), ⟨t⁻¹ * g, hg, rfl⟩, by simp⟩
  exact Set.Finite.subset (Set.Finite.biUnion T.finite_toSet fun t _ => hH.image _) hsub

/-- **Determinant argument, step 3** (h-trust C8 item 3): a character `ψ : G →* Eˣ` into the units
of a field whose square `ψ²` has finite image has finite image (each value is a square root of
one of finitely many scalars). For C8: `ψ² = α ε_g⁻¹`. -/
theorem finite_range_of_sq {G E : Type*} [Group G] [Field E] (ψ : G →* Eˣ)
    (h : (Set.range fun g => ψ g ^ 2).Finite) : (Set.range ψ).Finite := by
  classical
  have hsub : Set.range ψ ⊆ ⋃ c ∈ h.toFinset, {x : Eˣ | (x : E) ∈ Polynomial.nthRoots 2 (c : E)} := by
    rintro _ ⟨g, rfl⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Set.mem_range]
    refine ⟨ψ g ^ 2, ⟨g, rfl⟩, ?_⟩
    rw [Polynomial.mem_nthRoots (by norm_num)]
    simp
  refine Set.Finite.subset (Set.Finite.biUnion h.toFinset.finite_toSet fun c _ => ?_) hsub
  have hfin : ((Polynomial.nthRoots 2 (c : E)).toFinset : Set E).Finite := Finset.finite_toSet _
  refine Set.Finite.subset (hfin.preimage Units.val_injective.injOn) ?_
  intro x hx
  simpa using hx

/-- **Determinant argument, assembled** (h-trust C8 items 1-3, group-theoretic content). Let
`G` be a group with a finite-index subgroup `H`, `E` a field, and `r, ε, χ, ψ : G →* Eˣ` with
`r = ε · χ · ψ²` (`det r₅ = det ρ_g · ψ² = ε_g χ ψ²` at `k = 2`), `r² = χ²` on `H`
(`(det r₅)² = det V₅(A) = χ²` on `G_F`), and `ε` of finite image (a nebentypus). Then `ψ` has
finite image. -/
theorem twist_finite {G E : Type*} [Group G] [Field E] (H : Subgroup G) [H.FiniteIndex]
    (r ε χ ψ : G →* Eˣ) (hdet : ∀ g, r g = ε g * χ g * ψ g ^ 2)
    (hH : ∀ h ∈ H, r h ^ 2 = χ h ^ 2) (hε : (Set.range ε).Finite) : (Set.range ψ).Finite := by
  classical
  -- `α = r χ⁻¹` is `±1` on `H`, hence of finite image.
  let α : G →* Eˣ := r * χ⁻¹
  have hαH : (α '' H).Finite := by
    refine Set.Finite.subset ((Polynomial.nthRoots 2 (1 : E)).toFinset.finite_toSet.preimage
      Units.val_injective.injOn) ?_
    rintro _ ⟨h, hh, rfl⟩
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (by norm_num)]
    have := hH h hh
    have e : (α h) ^ 2 = 1 := by
      simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, this,
        mul_inv_cancel]
    have := congrArg Units.val e
    simpa using this
  have hα := finite_range_of_finiteIndex α H hαH
  -- `ψ² = α ε⁻¹`.
  have hsq : (Set.range fun g => ψ g ^ 2) ⊆ (fun p : Eˣ × Eˣ => p.1 * p.2⁻¹) '' (Set.range α ×ˢ Set.range ε) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨(α g, ε g), ⟨⟨g, rfl⟩, ⟨g, rfl⟩⟩, ?_⟩
    simp only [α, MonoidHom.mul_apply, MonoidHom.inv_apply, hdet]
    apply Units.ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have h1 := (ε g).ne_zero
    have h2 := (χ g).ne_zero
    field_simp
  exact finite_range_of_sq ψ (((hα.prod hε).image _).subset hsq)

end GlueAssembly

end AsmC8Sec

section AsmE1Sec
/-! ### Copied from `scratch/glue-assembly/E1Lin.lean` (compiled there). -/

/-!
# E1 glue: invariants commute with extension of the coefficient field

N5 L862-864: "Invariants in their finite-dimensional Hom space commute with extension of the
coefficient field." The direction used: if `(E ⊗_F W)^G ≠ 0` then `W^G ≠ 0`, for a
representation `W` of a group `G` over a field `F` and a field extension `E/F` (for E1:
`W = Hom_{ℚ₅}(V₅A, V₅J)`, `G = G_{L'}`, `E` a finite extension of `ℚ₅`). Proved for any
`F`-module `W` (no finiteness needed) by expanding in an `F`-basis of `E`.
-/

namespace GlueAssembly

open TensorProduct

variable {F E W G : Type*} [Field F] [Field E] [Algebra F E] [AddCommGroup W] [Module F W]
  [Group G]

/-- Coordinates of `E ⊗_F W` in an `F`-basis `b` of `E` are natural in `W`. -/
theorem coord_lTensor {ι : Type*} [DecidableEq ι] (b : Module.Basis ι F E) (f : W →ₗ[F] W) (x : E ⊗[F] W)
    (i : ι) :
    finsuppScalarLeft F W ι (LinearEquiv.rTensor W b.repr (LinearMap.lTensor E f x)) i =
      f (finsuppScalarLeft F W ι (LinearEquiv.rTensor W b.repr x) i) := by
  induction x using TensorProduct.inductionOn with
  | tmul y w => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

/-- **Invariants and extension of scalars.** If `W^G = 0` then every `G`-invariant vector of
`E ⊗_F W` vanishes. -/
theorem baseChange_invariant_eq_zero (ρ : Representation F G W) (h : ρ.invariants = ⊥)
    (x : E ⊗[F] W) (hx : ∀ g : G, LinearMap.lTensor E (ρ g) x = x) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  let e : E ⊗[F] W ≃ₗ[F] _ := LinearEquiv.rTensor W b.repr ≪≫ₗ finsuppScalarLeft F W _
  have hcoord : ∀ i, e x i = 0 := by
    intro i
    have hi : e x i ∈ ρ.invariants := by
      rw [Representation.mem_invariants]
      intro g
      have := coord_lTensor b (ρ g) x i
      rw [hx g] at this
      exact this.symm
    rw [h] at hi
    exact hi
  have : e x = 0 := Finsupp.ext hcoord
  exact e.injective (this.trans e.map_zero.symm)

/-- Contrapositive form used in E1: a nonzero invariant after extension of scalars gives a
nonzero invariant before. -/
theorem invariants_ne_bot_of_baseChange (ρ : Representation F G W) (x : E ⊗[F] W) (hx0 : x ≠ 0)
    (hx : ∀ g : G, LinearMap.lTensor E (ρ g) x = x) : ρ.invariants ≠ ⊥ :=
  fun h => hx0 (baseChange_invariant_eq_zero ρ h x hx)

end GlueAssembly

end AsmE1Sec

section AsmE2Sec
/-! ### Copied from `scratch/glue-assembly/E2Index.lean` (compiled there). -/

/-!
# E2 glue: `[SL₂(ℤ) : Γ₁(N)] ≤ N²` (N5 L871: "The index of `Γ₁(N)` is at most `N²`")

The first column modulo `N` separates the left cosets of `Γ₁(N)`.
-/

namespace GlueAssembly

open Matrix CongruenceSubgroup
open scoped MatrixGroups

/-- The first column of `γ ∈ SL₂(ℤ)` modulo `N`. -/
def firstColMod (N : ℕ) (γ : SL(2, ℤ)) : ZMod N × ZMod N :=
  (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ), ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ))

/-- The algebra of `firstColMod_eq_iff`, over variables. -/
theorem firstCol_algebra {N : ℕ} (A B C : Matrix (Fin 2) (Fin 2) ℤ)
    (hda : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1) (hdet : C 0 0 * C 1 1 - C 0 1 * C 1 0 = 1)
    (c00 : C 0 0 = A 1 1 * B 0 0 - A 0 1 * B 1 0) (c10 : C 1 0 = -A 1 0 * B 0 0 + A 0 0 * B 1 0)
    (b00 : B 0 0 = A 0 0 * C 0 0 + A 0 1 * C 1 0) (b10 : B 1 0 = A 1 0 * C 0 0 + A 1 1 * C 1 0) :
    ((A 0 0 : ZMod N), (A 1 0 : ZMod N)) = ((B 0 0 : ZMod N), (B 1 0 : ZMod N)) ↔
      (C 0 0 : ZMod N) = 1 ∧ (C 1 1 : ZMod N) = 1 ∧ (C 1 0 : ZMod N) = 0 := by
  rw [Prod.mk.injEq]
  have hdaN := congrArg (fun x : ℤ => (x : ZMod N)) hda
  have hdetN := congrArg (fun x : ℤ => (x : ZMod N)) hdet
  push_cast at hdaN hdetN
  constructor
  · rintro ⟨h0, h1⟩
    have e00 : (C 0 0 : ZMod N) = 1 := by
      rw [c00]; push_cast; rw [← h0, ← h1]; linear_combination hdaN
    have e10 : (C 1 0 : ZMod N) = 0 := by
      rw [c10]; push_cast; rw [← h0, ← h1]; ring
    refine ⟨e00, ?_, e10⟩
    rw [e00, e10] at hdetN
    linear_combination hdetN
  · rintro ⟨e00, _, e10⟩
    constructor
    · rw [b00]; push_cast; rw [e00, e10]; ring
    · rw [b10]; push_cast; rw [e00, e10]; ring

theorem firstColMod_eq_iff (N : ℕ) (a b : SL(2, ℤ)) :
    firstColMod N a = firstColMod N b ↔ a⁻¹ * b ∈ Gamma1 N := by
  have hCe : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(a : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(a : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
        -(a : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (a : Matrix (Fin 2) (Fin 2) ℤ) 0 0] *
        (b : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e1 : ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.adjugate (a : Matrix (Fin 2) (Fin 2) ℤ) * (b : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [e1, Matrix.adjugate_fin_two]
  have hBe : (b : Matrix (Fin 2) (Fin 2) ℤ) =
      (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    have e2 : ((a * (a⁻¹ * b) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
        (a : Matrix (Fin 2) (Fin 2) ℤ) * ((a⁻¹ * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [← e2, mul_inv_cancel_left]
  have hdet := (a⁻¹ * b).det_coe
  have hda := a.det_coe
  rw [Matrix.det_fin_two] at hdet hda
  rw [Gamma1_mem]
  refine firstCol_algebra _ _ _ hda hdet ?_ ?_ ?_ ?_
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  · rw [hCe]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · conv_lhs => rw [hBe]
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **`[SL₂(ℤ) : Γ₁(N)] ≤ N²`.** -/
theorem index_Gamma1_le (N : ℕ) [NeZero N] : (Gamma1 N).index ≤ N ^ 2 := by
  classical
  let g : SL(2, ℤ) ⧸ Gamma1 N → ZMod N × ZMod N :=
    Quotient.lift (firstColMod N) fun a b hab =>
      (firstColMod_eq_iff N a b).2 (QuotientGroup.leftRel_apply.mp hab)
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on
    induction y using QuotientGroup.induction_on
    exact QuotientGroup.eq.mpr ((firstColMod_eq_iff N _ _).1 hxy)
  rw [Subgroup.index_eq_card]
  calc Nat.card (SL(2, ℤ) ⧸ Gamma1 N) ≤ Nat.card (ZMod N × ZMod N) :=
        Nat.card_le_card_of_injective g hg
    _ = N ^ 2 := by rw [Nat.card_prod, Nat.card_zmod]; ring

end GlueAssembly

end AsmE2Sec

section AsmF3Sec
/-! ### Copied from `scratch/glue-assembly/F3Glue.lean` (compiled there). -/

/-!
# Elementary glue of step F3: normalizations of the theta height (N5 L934-947)

* `mulHeight_le_mulHeightL2`: the projective height with the Euclidean (`L²`) norm at the
  archimedean places dominates Mathlib's sup-norm height (N5: "His Euclidean projective height
  dominates our supremum projective height").
* `logHeight_sixteen_eq`: adjoining the six vanishing odd theta constants does not change the
  height (N5 L932-933), Mathlib's `logHeight_sumElim_zero_eq`.
* `logHeight_rootsOfUnity_smul`: multiplying coordinates by roots of unity does not change the
  height (N5 L937: the permitted changes of theta structure permute coordinates and multiply them
  by roots of unity).
-/

namespace GlueAssembly

open Height Real

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} [Fintype ι]

/-- The multiplicative projective height with the `L²` norm at the archimedean places and the
max norm at the nonarchimedean ones (relative to `K`; junk value `1` at `0`). -/
noncomputable def mulHeightL2 (x : ι → K) : ℝ :=
  open Classical in
  if x = 0 then 1 else
    (AdmissibleAbsValues.archAbsVal.map fun v => √(∑ i, v (x i) ^ 2)).prod *
      ∏ᶠ v : AdmissibleAbsValues.nonarchAbsVal, ⨆ i, v.val (x i)

/-- The `L²` projective height dominates the sup-norm one. -/
theorem mulHeight_le_mulHeightL2 (x : ι → K) : mulHeight x ≤ mulHeightL2 x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [mulHeightL2]
  rw [mulHeight_eq hx, mulHeightL2, if_neg hx]
  refine mul_le_mul_of_nonneg_right ?_
    (finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass _ _)
  refine Multiset.prod_map_le_prod_map₀ _ _
    (fun v _ => Real.iSup_nonneg_of_nonnegHomClass _ _) fun v _ => ?_
  have : Nonempty ι := by
    obtain ⟨i, _⟩ := Function.ne_iff.mp hx
    exact ⟨i⟩
  refine ciSup_le fun i => Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => v (x j) ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

/-- Logarithmic form. -/
theorem logHeight_le_log_mulHeightL2 (x : ι → K) : logHeight x ≤ log (mulHeightL2 x) :=
  log_le_log (mulHeight_pos x) (mulHeight_le_mulHeightL2 x)

/-- The ten even theta constants and the sixteen (six odd ones vanish) have the same height. -/
theorem logHeight_sixteen_eq (z : Fin 10 → K) :
    logHeight (Sum.elim z (0 : Fin 6 → K)) = logHeight z :=
  logHeight_sumElim_zero_eq z

/-- Multiplying the coordinates by roots of unity does not change the height: for `ζ i ^ n = 1`
(`n ≥ 1`), `mulHeight (ζ * x) = mulHeight x`. -/
theorem mulHeight_rootsOfUnity_mul {n : ℕ} (hn : 0 < n) (ζ x : ι → K) (hζ : ∀ i, ζ i ^ n = 1) :
    mulHeight (ζ * x) = mulHeight x := by
  have hv : ∀ v : AbsoluteValue K ℝ, ∀ i, v (ζ i) = 1 := by
    intro v i
    have h := congrArg v (hζ i)
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_of_nonneg (v.nonneg _) hn.ne').1 h
  have hz : ∀ i, ζ i ≠ 0 := fun i h => by simpa [h, zero_pow hn.ne'] using hζ i
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : ζ * x ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Function.ne_iff.mpr ⟨i, by simpa using mul_ne_zero (hz i) hi⟩
  rw [mulHeight_eq hx, mulHeight_eq hx']
  simp only [Pi.mul_apply, map_mul, hv, one_mul]

end GlueAssembly

end AsmF3Sec

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

/-! ## §0. Cheap definitions -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. (Its restriction to `ℚ` is then `ℤ_(p)`.) -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`: it stabilizes `v` and acts as
`x ↦ x^p` on its residue field. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (Mathlib's normed
`PadicAlgCl ℓ`). Continuity for the norm topology is equivalent to the usual notion (the image
lies in `GL_n` of a finite extension of `ℚ_ℓ`), by compactness and Baire. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- Every arithmetic Frobenius above `p` has trace `a` (meaningful at unramified `p`). -/
def GaloisRep.FrobTrace (ρ : GaloisRep ℓ n) (p : ℕ) (a : PadicAlgCl ℓ) : Prop :=
  ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
    Matrix.trace (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) = a

/-- `c` is a complex conjugation: it is induced by `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c`. -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → Matrix.det (ρ.toHom c : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = -1

/-- `ρ` is (absolutely) irreducible, in Burnside's form: its image spans `M_n(ℚ̄_ℓ)`. Over the
algebraically closed `ℚ̄_ℓ` this is equivalent to irreducibility. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ)
    (Set.range fun σ => (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W) →
    ∃ W', IsCompl W W' ∧
      ∀ σ, W'.map (Matrix.toLin' (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))) ≤ W'

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators with nebentypus `χ`, expressed through
its coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}` (with `χ(d) = 0`
for `(d, N) > 1`). For a form with nebentypus `χ` this is equivalent to the Hecke definition
(Diamond–Shurman, Prop. 5.3.1; locator UNVERIFIED). -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `ρ` is attached to the eigenform `g` (through embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`): for
`p ∤ Nℓ`, `ρ` is unramified at `p` and its Frobenius trace is `ιL(α)` where `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧ ρ.FrobTrace p (ιL α)

/-! ## §1. Leaves statable today over the cheap definitions (not proved here; copied from the
hdec-faithful draft). Numbering of the note: T13 Skolem–Noether, T14 HasseBrauerQ, T17
Kronecker–Weber, T18 FrobeniusDense, T19 Brauer–Nesbitt, R14 EigenformRepExists, R15
DeligneSerreConseq, T24 EigenformTwist. -/

/-- **L14. Skolem–Noether** (Reiner, *Maximal orders*, Thm 7.21; Tau Ceti `skolemNoether`).
Exact. -/
def SkolemNoether : Prop :=
  ∀ (K A B : Type) [Field K] [Ring A] [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] [Ring B] [Algebra K B] [IsSimpleRing B] [FiniteDimensional K B]
    (f g : B →ₐ[K] A), ∃ x : Aˣ, ∀ b, g b = (x : A) * f b * ((x⁻¹ : Aˣ) : A)

/-- **L15(a). Hasse principle for `Br(ℚ)`, in the form used** (Albert–Brauer–Hasse–Noether with
the sum formula; Milne, *Arithmetic duality theorems*, Ch. I). A central simple `ℚ`-algebra that
splits over every `ℚ_p` splits over `ℚ`. Consequence (the real invariant is forced to 0). -/
def HasseBrauerQ : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℚ A] [Algebra.IsCentral ℚ A] [IsSimpleRing A]
    [FiniteDimensional ℚ A] (n : ℕ), Module.finrank ℚ A = n ^ 2 →
    (∀ p : ℕ, ∀ _ : Fact p.Prime,
      Nonempty (TensorProduct ℚ ℚ_[p] A ≃ₐ[ℚ_[p]] Matrix (Fin n) (Fin n) ℚ_[p])) →
    Nonempty (A ≃ₐ[ℚ] Matrix (Fin n) (Fin n) ℚ)

/-- **L17. Kronecker–Weber** (Washington, *Cyclotomic fields*, Thm 14.1; Tau Ceti
`kroneckerWeber`). Exact. -/
def KroneckerWeber : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
    (∀ σ τ : L ≃ₐ[ℚ] L, σ * τ = τ * σ) →
    ∃ n : ℕ+, Nonempty (L →ₐ[ℚ] CyclotomicField (n : ℕ) ℚ)

/-- **L18. Chebotarev, in the density form used** (Neukirch VII.13.4; Tau Ceti). Frobenius
elements are dense in `G_ℚ`, avoiding any finite set of primes. Consequence. -/
def FrobeniusDense : Prop :=
  ∀ (U : Subgroup GQ), IsOpen (U : Set GQ) → ∀ (σ : GQ) (S : Finset ℕ),
    ∃ p, p.Prime ∧ p ∉ S ∧ ∃ (v : ValuationSubring Qbar) (τ : GQ),
      LiesOver v p ∧ IsArithFrob τ v p ∧ τ⁻¹ * σ ∈ U

/-- **L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact. -/
def BrauerNesbitt : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

/-- **L27(a). Galois representations of eigenforms** (Eichler–Shimura `k = 2`, Deligne 1971
`k ≥ 2`, Deligne–Serre 1974 `k = 1`). Consequence (the published statements also give the
determinant). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence. -/
def DeligneSerreConseq : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **L28(a). Twisting an eigenform** (Shimura 1971, Prop. 3.64; Atkin–Li 1978). The twist of a
normalized eigenform of level `N` by a character mod `m` is a normalized eigenform of level
`Nm²` with coefficients `ψ(p) a_p` at `p ∤ Nm`. Consequence. -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p


/-! ## §2. Leaves that need definitions Mathlib lacks: placeholders (no content)

Each docstring gives the statement in the form the proof uses, the reference (UNVERIFIED unless
the note says otherwise), and the missing definitions with their cost tier. -/

/-- **R1. Shimura–Deligne: canonical model and moduli interpretation of the level-3 QM curve.**
`B = (2,−3)/ℚ`, `𝒪` maximal, `μ = 2j + ij`, `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`. (a) The functor on
`ℚ`-schemes of `(A, ι, λ, η)` (abelian scheme of relative dimension 2, `ι : 𝒪 → End A`, principal
polarization with Rosati involution `a ↦ μ⁻¹āμ`, `𝒪`-linear `η : 𝒪/3𝒪 ≅ A[3]`) is represented by
a smooth projective curve `Y₃/ℚ`; (b) complex uniformization compatible with the universal
family; (c) the finite-adelic normalizer acts over `ℚ`; (d) Shimura reciprocity at CM points.
Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21,
Cor. 5.7, Ex. 5.8, §§4.8-4.17; Kottwitz, JAMS 5 (1992), §5 (UNVERIFIED). Consequence (the PEL
theorem specialized to this datum). Missing: abelian schemes over a base with PEL structure,
moduli functors, representability (very large). -/
opaque R01_ShimuraDeligne : Prop

/-- **R2. Baba–Granath.** `X₆/W ≅ P¹_j`, branched over `0, ∞, −16/27` with indices 4, 6, 2 at the
CM points of discriminants −4, −3, −24; two QM surfaces with principal polarization of the fixed
type have the same polarized moduli point iff their points of `X₆` are `W`-conjugate. Canad. J.
Math. 60 (2008), Thm 2.1, Lemma 3.1 (journal numbering UNVERIFIED; 2005 preprint read by a model).
Exact. Missing: `X₆` and its Atkin–Lehner group (very large, via R1). -/
opaque R02_BabaGranath : Prop

/-- **R3. Lin–Yang.** On the finite nonzero `j`-locus the QM surface over `j` is the Jacobian of a
genus-2 curve with `[J₂ : J₄ : J₆ : J₁₀] = [12(j+1) : 6(j²+j+1) : 4(j³−2j²+1) : j³]`.
Math. Z. 295 (2020), Example 30, eqs. (13)-(14) (VERIFIED in arXiv v1 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: the QM locus (very large). -/
opaque R03_LinYang : Prop

/-- **R5. González–Rotger.** For an order `R` of conductor `f`, `(f,6) = 1`, in an imaginary
quadratic `k` embeddable in `𝒪`, `#CM(R) = h(R)` on `X₆` and `ℚ(x)` is the ring class field `H_R`
or has index 2 in it (according as some prime dividing 6 is inert in `k` or not). J. Math. Soc.
Japan 58 (2006), Thm 5.12, Prop. 5.6 (VERIFIED in arXiv:math/0612732 by a repository note;
journal numbering UNVERIFIED). Exact. Missing: as R2. -/
opaque R05_GonzalezRotger : Prop

/-- **R8. Grothendieck's semistable reduction theorem** (Néron-model form). An abelian variety over
the fraction field of a henselian DVR acquires semistable reduction over a finite extension. SGA 7
I, Exp. IX, Thm 3.6 (UNVERIFIED). Exact. Needed only on the reviewed route for A6 (Lemma PR(ii));
the Raynaud route of the reduction-theory report avoids it. Missing: Néron models (large). The
Galois consequence is stated as `PkgI2.GrothendieckMonodromy`. -/
opaque R08_SemistableReduction : Prop

/-- **R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F` an abelian variety of dimension `g`,
`H¹_et(A_F̄, ℚ_ℓ)` is de Rham with `D_dR ≅ H¹_dR(A/F)`; hence `V_ℓ(A)` is de Rham with Hodge–Tate
weights `0, −1`, each of multiplicity `g`. Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with
Thms 9.1, 9.3, corrigendum 2016; or Faltings 1989, Tsuji 1999 (UNVERIFIED). Exact (first clause).
Missing: `B_dR` with Galois action and filtration, de Rham representations (large). -/
opaque R10_DeRhamComparison : Prop

/-- **R11. Berger's p-adic monodromy theorem.** A de Rham representation of `G_K`, `K/ℚ_p` finite,
is potentially semistable. Invent. Math. 148 (2002), Thm 0.7 = Cor. 5.22 (read by a model).
Exact. Missing: `B_st`, potentially semistable representations (very large). -/
opaque R11_Berger : Prop

/-- **R12. Pan's Fontaine–Mazur theorem.** For an odd prime `p` and a continuous irreducible
`ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially semistable at `p`, odd, with
distinct Hodge–Tate weights (and, if `p = 3`, the residual clause): there are a normalized
eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))` for almost
all `v` (the trace reading of "comes from a cuspidal eigenform up to twist", implied by every
reading in the literature). JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by a
repository note; JAMS numbering UNVERIFIED). Consequence. Expressible now except "potentially
semistable" (very large) and "Hodge–Tate weights" (large). -/
opaque R12_Pan : Prop

/-- **R13. Hodge–Tate weights of eigenform representations at every level.** For a normalized
eigenform `g` of weight `k ≥ 2`, any level and nebentypus, `ρ_{g,ι}` (Tate normalization) is
Hodge–Tate at `ℓ` with weights `{0, 1−k}`. Saito, Invent. Math. 129 (1997); or Kato, Astérisque
295 (2004), §9.4; or Scholl 1990 with R10 and T23 (UNVERIFIED). Consequence (normalization).
Missing: Hodge–Tate representations (large). -/
opaque R13_EigenformHT : Prop

/-- **R16. Eichler–Shimura in `J₁(N)`.** For a weight-2 newform `f` of level `N`,
`V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a `G_ℚ`-stable two-dimensional subquotient on which
`tr(Frob_p) = ι(a_p(f))` for `p ∤ Nℓ`. Shimura 1971, Thm 7.9, §7; Shimura, J. Math. Soc. Japan 25
(1973), Thm 1 (UNVERIFIED). Consequence. Missing: `X₁(N)`, `J₁(N)` over `ℚ` (very large). -/
opaque R16_EichlerShimuraJ1 : Prop

/-- **R17. Carayol's local–global compatibility.** For a weight-2 newform of level `N` and `p ≠ ℓ`,
the Artin conductor exponent of `ρ_{f,λ}|G_{ℚ_p}` is `v_p(N)`. Ann. Sci. ÉNS 19 (1986),
Théorème (A) (UNVERIFIED; that it covers `F = ℚ` at `p | N` is an open check). Consequence.
Missing: conductors of ℓ-adic representations, newforms (medium). -/
opaque R17_Carayol : Prop

/-- **R18. Javanpeykar.** A smooth projective connected curve `X/ℚ̄` of genus `g ≥ 1` with a Belyi
map of degree `d` has `h_F(Jac X) ≤ 13·10⁶ · g · d⁵`. Algebra Number Theory 8 (2014), Thm 1.1.1
(read by a model). Exact. Missing: Faltings height (very large), Belyi maps, Jacobians. -/
opaque R18_Javanpeykar : Prop

/-- **R19. Gaudron–Rémond isogeny theorem.** Isogenous abelian varieties `A, B` of dimension `g`
over a number field `K` admit an isogeny `A → B` of degree at most
`((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`. Duke Math. J. 163 (2014), Thm 1.4 (read
by a model). Exact. Missing: Faltings height (very large). -/
opaque R19_GaudronRemond : Prop

/-- **R20. Faltings' height lemma.** For an isogeny `φ : A → B` over a number field,
`|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Faltings 1983, Lemma 5; Raynaud, Astérisque 127 (1985),
Exp. VII, Cor. 2.1.3 (UNVERIFIED). Exact. Missing: Faltings height. -/
opaque R20_FaltingsHeightLemma : Prop

/-- **R21. Bost's lower bound.** `h_F(A) ≥ −(3/2)·dim A` (Bost: `≥ −log(π√2)·dim A`). Bost,
Sém. Bourbaki 795 (1996), as recorded in Gaudron–Rémond 2014, §9 (read by a model). Consequence.
Missing: Faltings height. -/
opaque R21_Bost : Prop

/-- **R22. Pazuki.** For a principally polarized abelian surface over a number field,
`h_Θ(A) ≤ ½X_D + C₂ log(X_D + 2)`, `X_D = max(1, h_F(A) + log π)`, `C₂ = 1000·2⁴(log 2⁴)⁵`,
`h_Θ` the height of the level-2 theta constants. Bull. Soc. Math. France 140 (2012), Cor. 1.3(2)
(read by a model). Exact. Missing: Faltings height, theta constants. -/
opaque R22_Pazuki : Prop

/-- **T9. Weil pairing.** The Weil pairing of a polarization is Galois-equivariant with values in
`ℤ_ℓ(1)`, so `G_K` acts on `V_ℓ(A)` through `GSp` with cyclotomic multiplier (Mumford §§20, 23,
UNVERIFIED). Missing: polarizations, Tate modules (medium). -/
opaque T09_WeilPairing : Prop

/-- **T10. `V_ℓ(A) ≅ H¹_et(A_K̄, ℚ_ℓ)^∨`**, Galois-equivariantly (Milne in Cornell–Silverman 1986,
Thm 15.1(a), UNVERIFIED). Missing: ℓ-adic étale cohomology (large). -/
opaque T10_TateDuality : Prop

/-- **T11. Riemann's theorem, GAGA, rigidity.** `End⁰(A_ℂ)` is the algebra of endomorphisms of
the rational Hodge structure `H₁(A(ℂ), ℚ)`, and `Hom(A, B) = Hom(A_ℂ, B_ℂ)` over `ℚ̄` (Mumford
§§1-3; Serre 1956; Conrad 2006, §3; UNVERIFIED). Missing: analytification (large). -/
opaque T11_RiemannGAGA : Prop

/-- **T12. Artin comparison.** `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, compatibly with complex conjugation
(SGA 4 XI 4.4, UNVERIFIED; elementary for abelian varieties via `ℂ²/Λ`). Missing: as T11. -/
opaque T12_ArtinComparison : Prop

/-- **T23. Fontaine's closure properties.** de Rham representations are closed under duals,
tensor products, sums and subquotients (Astérisque 223 (1994), Thm 3.8, UNVERIFIED). Missing: as
R10 (large). -/
opaque T23_FontaineClosure : Prop

/-- **T25. Newforms** (Atkin–Lehner–Li; Li, Math. Ann. 212 (1975), Thm 5; UNVERIFIED): each system
of Hecke eigenvalues of a normalized eigenform away from the level is that of a unique newform of
level dividing it; Galois conjugates of newforms are newforms. Missing: old space and newforms
(medium; Tau Ceti). -/
opaque T25_Newforms : Prop

/-- **T29. Local normalizers of maximal orders.** For a quaternion algebra `B_p` over `ℚ_p` and a
maximal order `𝒪_p`, the group `N(𝒪_p)/ℚ_p^×𝒪_p^×` has order 2 if `B_p` is a division algebra
(generated by a uniformizer of `B_p`) and order 1 if `B_p ≅ M₂(ℚ_p)` (`N(M₂(ℤ_p)) = ℚ_p^×GL₂(ℤ_p)`);
for `B = (2,−3)` (ramified at 2, 3) this gives the normalizer index 4 of A3 (Vignéras, LNM 800,
Ch. II, UNVERIFIED). Statable over Mathlib's quaternion algebras (pkg-I1 I1-f), not drafted. -/
opaque T29_LocalNormalizers : Prop

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R14`,
`R15` (§1 here). -/
structure ResearchLeaves : Prop where
  r1 : R01_ShimuraDeligne
  r2 : R02_BabaGranath
  r3 : R03_LinYang
  r4 : PkgI1.ThetaModularity
  r5 : R05_GonzalezRotger
  r6 : PkgI2.RaynaudCriterion.{0}
  r7a : PkgI2.NeronOggShafarevich.{0}
  r7b : PkgI2.SerreTatePotentialGood.{0}
  r8 : R08_SemistableReduction
  r9a : PkgI3.FaltingsSemisimple
  r9b : PkgI3.FaltingsTate
  r10 : R10_DeRhamComparison
  r11 : R11_Berger
  r12 : R12_Pan
  r13 : R13_EigenformHT
  r14 : EigenformRepExists
  r15 : DeligneSerreConseq
  r16 : R16_EichlerShimuraJ1
  r17 : R17_Carayol
  r18 : R18_Javanpeykar
  r19 : R19_GaudronRemond
  r20 : R20_FaltingsHeightLemma
  r21 : R21_Bost
  r22 : R22_Pazuki

/-- **The textbook foundations** (note §2.2), bundled. -/
structure TextbookLeaves : Prop where
  t1 : PkgI2.PurityBranchLocus.{0}
  t2 : PkgI2.AbhyankarDVR.{0}
  t3 : PkgI2.NeronMappingAbelianScheme.{0}
  t4 : PkgI2.ReductionTorsionBijective.{0}
  t5 : PkgI2.TorsionStructure.{0}
  t6 : PkgI3.HomFreeFinite
  t7 : PkgI3.CharPolyIndepOfEll
  t8 : PkgI3.PoincareReducibility
  t9 : T09_WeilPairing
  t10 : T10_TateDuality
  t11 : T11_RiemannGAGA
  t12 : T12_ArtinComparison
  t13 : SkolemNoether
  t14a : PkgI6.BrauerHasse2
  t14b : PkgI6.BrauerReciprocity2
  t15 : PkgI6.LocalH2Card
  t16a : ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p
  t16b : PkgI6.LocalReciprocityUpper
  t17 : KroneckerWeber
  t18 : FrobeniusDense
  t19 : BrauerNesbitt
  t20 : GlueConductor.HilbertDifferentFormula
  t21 : GlueConductor.SerreDifferentBound
  t22a : PkgI6.HerbrandQuotient
  t22b : PkgI6.HerbrandTransitivity
  t23 : T23_FontaineClosure
  t24 : EigenformTwist
  t25 : T25_Newforms
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomy
  t28 : PkgI1.IgusaClebschSeparation
  t29 : T29_LocalNormalizers

/-- **The glue G1-G17 and G19 (non-Arakelov part).** The leaves give glue-assembly's interface
`GlueOutputs` at `S = Mult.S_mul`: for each `u ∉ 𝒞`, the theta point `z` of the QM surface over
`J(u)`, a real `h_A` (the Faltings height of `A`) with Pazuki's bound, and the numerical outputs of
the non-CM transfer. Not proved: the glue needs the definitions of §4 of the note, and most leaves
are placeholders. `GlueOutputs` is an intermediate contract, not a leaf. -/
theorem glueOutputs_of_leaves (_r : ResearchLeaves) (_t : TextbookLeaves) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  sorry

/-- **G18-G20, proved** (glue-assembly): `GlueOutputs Mult.S_mul → SixContactMin`, through F2
over Mathlib's Weil heights, the E2-E4 and F3 arithmetic, the final constant, and F4.
`GlueAssembly.SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` by definition. -/
theorem sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  GlueAssembly.sixContactMinAt_of_glueOutputs h

/-- The scratch copy of `JHeightBound` in glue-assembly is the repository's. -/
theorem jHeightBound_copy_iff :
    GlueAssembly.JHeightBound ZInQ.Mult.S_mul ↔ ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul :=
  Iff.rfl

/-- **G0. The leaves imply `SixContactMin`**: G1-G17, G19 (`sorry`) then G18-G20 (proved). -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t)

/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/
example (h : ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul) : ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound h

end HSyn

end

#print axioms HSyn.weight_match
#print axioms PkgI2.inertiaTrivial_of_goodReduction
#print axioms PkgI2.D2_fixed_of_raynaud
#print axioms GlueConductor.D1_genuine
#print axioms GlueConductor.level_le
#print axioms GlueConductor.fourth_pow_mem
#print axioms HSyn.sixContactMin_of_glueOutputs
#print axioms PkgI1.f1_algebra
#print axioms PkgI1.equiv_of_lyVec
#print axioms PkgI3.exists_hom_ne_zero_of_equivariant
#print axioms PkgI3.finrank_equivEnd
#print axioms PkgI6.eq_of_same_finite_support
#print axioms GlueAssembly.twist_finite
#print axioms GlueAssembly.index_Gamma1_le
#print axioms GlueAssembly.mulHeight_le_mulHeightL2
#print axioms GlueAssembly.invariants_ne_bot_of_baseChange
#print axioms HSyn.sixContactMin_of_leaves
