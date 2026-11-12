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
* `PkgI4` (pkg-I4): the `G_{ℚ_p}`-action on `ℂ_p` and on Mathlib's `BDeRham`, the de Rham predicate,
  Hodge–Tate multiplicities; the modularity leaves (`DeRhamComparison`, `PanBerger`, `EigenformHT`,
  `NewformOfEigenform`, `CarayolUnramified`) and templates. Its copy of pkg-I3 is renamed `PkgI4.I3`.
* `PkgI6` (pkg-I6): continuous Galois cohomology leaves for B2, local Kronecker–Weber, local
  reciprocity with upper numbering, ramification leaves; the proved Brauer step of B2.
* `GlueConductor` (glue-conductor): the elementary core of D1-D5, proved; two different-ideal
  leaves stated over Mathlib.
* `GlueAssembly` (glue-assembly): F2 on Mathlib's Weil heights, E2-E4/F3 arithmetic, the final
  constant and F4: `GlueOutputs S → SixContactMinAt S`, proved; C8, E1, E2, F3 glue.
* `GlueDescent` (glue-descent): B1/C1 algebra, B2-B3 over Mathlib's `G_ℚ` from four leaves
  (`GlueDescent.B3Q.b3_degree_le_QM`, proved).
* `GlueRepo` (glue-repo): the quaternion order, `1 + 3M_r(ℤ₃)` torsion-free, the arithmetic of
  Lemma PR(i), Minkowski's bound, the NoCM fibre computation (proved).
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

No `axiom` declarations. Leaf numbering (R1-R22 research-level, T1-T32 textbook) is that of the
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

section PkgI4Sec
/-! ### Copied from `scratch/pkg-I4/I4.lean` (compiled there). The copy of pkg-I3 inside it is renamed `PkgI4.I3`. -/

/-!
# Package I4 (modularity): leaves statable over Mathlib today

Draft for `docs/research/pkg-I4.md` (task pkg-I4, 2026-11-11). Check with
`lake env lean scratch/pkg-I4/I4.lean`.

* `PkgI4.Cp`, `PkgI4.DR` (first): `𝓞_ℂ_[p]` is `p`-adically complete (instances missing in
  Mathlib), and Mathlib's `BDeRhamPlus`/`BDeRham` are functorial (naturality of `untilt` and of
  Fontaine's `θ`, maps of adic completions, generators of `ker θ`). Used in §1b for the action of
  `G_{ℚ_p}` on `B_dR` and the **de Rham predicate**.
* §0 Galois side over `ℚ̄`: copied, with small changes, from `scratch/hdec-faithful/Leaves.lean`
  §0 (places as valuation subrings, inertia, arithmetic Frobenius, complex conjugation,
  continuous `GL_n(ℚ̄_ℓ)`-representations, characters).
* §1 **new**: the local Galois group `G_{ℚ_p}`, its action on Mathlib's `ℂ_[p]`, the
  `p`-adic cyclotomic character, and **Hodge–Tate multiplicities** (Tate–Sen definition through
  `(ℂ_p(i) ⊗ V)^{G_{ℚ_p}}`, written as a space of equivariant `ℚ_p`-linear maps `V → ℂ_p`).
* §2 modular side: cusp forms on `Γ₁(N)`, nebentypus, normalized eigenforms (Hecke recursion of
  the q-coefficients, as hdec-faithful), representations attached to eigenforms (trace form),
  and **new**: the old space and newforms.
* §1b **new**: the action of `G_{ℚ_p}` on `B_dR = BDeRham 𝓞_ℂ_[p] p`, `ℚ_p ⊆ B_dR` fixed by it,
  `D_dR`, and the **de Rham predicate** `IsDeRham` / `LocalIsDeRham` (genuine; no `sorry`).
* §3 the leaves of I4 that are statable now, as `def … : Prop` (none proved).
* §4 templates — functions of a missing predicate (`IsPst`, the conductor exponent) — and the
  leaf **`PanBerger`** = `PanFor LocalIsDeRham`, statable now. A template is **not** a leaf:
  `PanFor P` says nothing until `P` is the genuine potentially-semistable predicate.
* §5 small glue facts, proved.

Faithfulness caveat: `IsDeRham` and `htMult` are genuine definitions, but no theorem about them is
proved here (e.g. `B_dR^{G_{ℚ_p}} = ℚ_p`, Tate's `ℂ_p(i)^G = 0`). A definitional slip could make a
hypothesis unsatisfiable and a leaf vacuous; the standard non-vacuity checks are listed in
`docs/research/pkg-I4.md` §3.4.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace PkgI4.Cp

open Ideal

variable (p : ℕ) [hp : Fact p.Prime]

theorem mem_O_iff (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def]
  change (PadicComplex.valued p).v x ≤ 1 ↔ _
  rw [← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
    IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p]; exact inv_pos.mpr (by exact_mod_cast hp.1.pos)

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)

/-- `x ∈ p^n 𝓞` iff `‖x‖ ≤ ‖p‖^n`. -/
theorem mem_span_pow_iff (x : 𝓞_ℂ_[p]) (n : ℕ) :
    x ∈ span {(p : 𝓞_ℂ_[p])} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖(z : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp z.2
    have e : ((z * (p : 𝓞_ℂ_[p]) ^ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (z : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
      push_cast; rfl
    rw [e, norm_mul, norm_pow]
    calc ‖(z : ℂ_[p])‖ * ‖(p : ℂ_[p])‖ ^ n ≤ 1 * ‖(p : ℂ_[p])‖ ^ n := by gcongr
      _ = _ := one_mul _
  · intro h
    have hpn : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))
    refine ⟨⟨(x : ℂ_[p]) / (p : ℂ_[p]) ^ n, (mem_O_iff p _).mpr ?_⟩, ?_⟩
    · rw [norm_div, norm_pow, div_le_one (pow_pos (norm_p_pos p) n)]
      exact h
    · apply Subtype.ext
      push_cast
      field_simp


theorem smodEq_iff (x y : 𝓞_ℂ_[p]) (n : ℕ) :
    x ≡ y [SMOD (span {(p : 𝓞_ℂ_[p])} ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff]
  push_cast
  rfl

instance notIsUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := ⟨fun h => by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  have hv' : (p : ℂ_[p]) * (v : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hv
    push_cast at this
    exact this
  have h1 : ‖(v : ℂ_[p])‖ ≤ 1 := (mem_O_iff p _).mp v.2
  have h2 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ = 1 := by rw [← norm_mul, hv', norm_one]
  have h3 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ < 1 :=
    calc ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact norm_p_lt_one p
  linarith⟩

theorem tendsto_norm_p_pow :
    Filter.Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_p_lt_one p)

instance isHausdorff : IsHausdorff (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  haus' x hx := by
    have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
      have := (smodEq_iff p x 0 n).mp (hx n)
      simpa using this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 := ge_of_tendsto' (tendsto_norm_p_pow p) h
    exact Subtype.ext (by simpa using norm_le_zero_iff.mp h0)

instance isPrecomplete : IsPrecomplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  prec' f hf := by
    set g : ℕ → ℂ_[p] := fun n => (f n : ℂ_[p])
    have hmn : ∀ m n, m ≤ n → ‖g m - g n‖ ≤ ‖(p : ℂ_[p])‖ ^ m := fun m n h =>
      (smodEq_iff p _ _ m).mp (hf h)
    have hcs : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ‖(p : ℂ_[p])‖ ^ N) (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        calc ‖g n - g m‖ = ‖(g N - g m) - (g N - g n)‖ := by congr 1; ring
          _ ≤ ‖g N - g m‖ + ‖g N - g n‖ := norm_sub_le _ _
          _ ≤ ‖(p : ℂ_[p])‖ ^ N + ‖(p : ℂ_[p])‖ ^ N := add_le_add (hmn N m hm) (hmn N n hn)
          _ = 2 * ‖(p : ℂ_[p])‖ ^ N := by ring
      · simpa using (tendsto_norm_p_pow p).const_mul 2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' (hL.norm) fun n => (mem_O_iff p _).mp (f n).2
    refine ⟨⟨L, (mem_O_iff p L).mpr hL1⟩, fun n => (smodEq_iff p _ _ n).mpr ?_⟩
    have ht : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨n, fun k hk => hmn n k hk⟩)

instance isAdicComplete : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where

end PkgI4.Cp

namespace PkgI4.DR

open Ideal

variable {R S : Type*} [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem span_p_le_comap (f : R →+* S) :
    span {(p : R)} ≤ (span {(p : S)}).comap f := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

/-- `R/p → S/p` induced by `f`. -/
def modPMap (f : R →+* S) : ModP R p →+* ModP S p :=
  Ideal.quotientMap _ f (span_p_le_comap p f)

variable [Fact ¬IsUnit (p : R)] [Fact ¬IsUnit (p : S)]

/-- The tilt is functorial: `R♭ → S♭`. -/
def preTiltMap (f : R →+* S) : PreTilt R p →+* PreTilt S p :=
  Perfection.map p (modPMap p f)

theorem coeff_preTiltMap (f : R →+* S) (x : PreTilt R p) (n : ℕ) :
    Perfection.coeff _ p n (preTiltMap p f x) = modPMap p f (Perfection.coeff _ p n x) :=
  rfl

variable [IsAdicComplete (span {(p : R)}) R] [IsAdicComplete (span {(p : S)}) S]

/-- Naturality of `untilt`. -/
theorem untilt_preTiltMap (f : R →+* S) (x : PreTilt R p) :
    PreTilt.untilt (preTiltMap p f x) = f (PreTilt.untilt x) := by
  refine Perfection.teichmuller_spec fun n => ?_
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ p n x)
  refine ⟨f w, ?_, ?_⟩
  · rw [coeff_preTiltMap, ← hw]
    rfl
  · have h := Perfection.teichmuller_sModEq (p := p) (I := span {(p : R)}) (x := x) (y := w) hw
    rw [SModEq.sub_mem] at h ⊢
    have h' := Ideal.mem_map_of_mem f h
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast, map_sub,
      map_pow] at h'
    have h'' := neg_mem h'
    rw [neg_sub] at h''
    exact h''

/-- **Naturality of Fontaine's `θ`**: `θ_S ∘ W(f♭) = f ∘ θ_R`. -/
theorem fontaineTheta_naturality (f : R →+* S) :
    (WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f)) =
      f.comp (WittVector.fontaineTheta R p) := by
  ext x
  refine (IsHausdorff.eq_iff_smodEq (I := span {(p : S)})).mpr fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.idealQuotientMk]
  have key : (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp
      ((WittVector.fontaineTheta S p).comp (WittVector.map (preTiltMap p f))) =
      (Ideal.Quotient.mk (span {(p : S)} ^ n)).comp (f.comp (WittVector.fontaineTheta R p)) := by
    refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ fun y => ?_
    · rw [← map_natCast (Ideal.Quotient.mk (span {(p : S)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton_self _
    · simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_preTiltMap]
  exact congrArg (fun g => g x) key


/-! ### Functoriality of adic completions of rings -/

section AdicMap

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

include hg in
theorem pow_le_comap (n : ℕ) : J ^ n ≤ (J' ^ n).comap g := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hg) n

theorem factorPow_evalₐ {m n : ℕ} (hle : m ≤ n) (x : AdicCompletion J A) :
    Ideal.Quotient.factorPow J hle (AdicCompletion.evalₐ J n x) = AdicCompletion.evalₐ J m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective J A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, ← AdicCompletion.Ideal.mk_eq_mk J hle]
  rfl

/-- `A ⧸ J^n`-components of the map `Â_J → B̂_{J'}`. -/
def adicMapAux (n : ℕ) : AdicCompletion J A →+* B ⧸ J' ^ n :=
  (Ideal.quotientMap (J' ^ n) g (pow_le_comap J J' g hg n)).comp
    (AdicCompletion.evalₐ J n : AdicCompletion J A →+* A ⧸ J ^ n)

theorem adicMapAux_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J' hle).comp (adicMapAux J J' g hg n) = adicMapAux J J' g hg m := by
  ext x
  simp only [RingHom.comp_apply, adicMapAux]
  erw [← factorPow_evalₐ J hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  erw [← ha]
  rfl

/-- The ring map `Â_J → B̂_{J'}` induced by `g` with `g(J) ⊆ J'`. -/
def adicMap : AdicCompletion J A →+* AdicCompletion J' B :=
  AdicCompletion.liftRingHom J' (adicMapAux J J' g hg) (adicMapAux_compat J J' g hg)

end AdicMap

/-! ### Functoriality of `B_dR^+` -/

section BdR

/-- `W(R♭)[1/p] → W(S♭)[1/p]`. -/
def locMap (f : R →+* S) :
    Localization.Away (p : WittVector p (PreTilt R p)) →+*
      Localization.Away (p : WittVector p (PreTilt S p)) :=
  Localization.awayLift ((algebraMap _ _).comp (WittVector.map (preTiltMap p f))) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- `R[1/p] → S[1/p]`. -/
def locMapBase (f : R →+* S) : Localization.Away (p : R) →+* Localization.Away (p : S) :=
  Localization.awayLift ((algebraMap _ _).comp f) _ (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit _)

/-- Naturality of `θ[1/p]`. -/
theorem fontaineThetaInvertP_naturality (f : R →+* S) :
    (fontaineThetaInvertP S p).comp (locMap p f) =
      (locMapBase p f).comp (fontaineThetaInvertP R p) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
  ext w
  simp only [RingHom.comp_apply, locMap, locMapBase, fontaineThetaInvertP,
    Localization.awayLift, IsLocalization.Away.lift, IsLocalization.lift_eq]
  rw [← RingHom.comp_apply (WittVector.fontaineTheta S p), fontaineTheta_naturality]
  rfl

theorem ker_le_comap_locMap (f : R →+* S) :
    RingHom.ker (fontaineThetaInvertP R p) ≤
      (RingHom.ker (fontaineThetaInvertP S p)).comap (locMap p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply,
    fontaineThetaInvertP_naturality, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero]

/-- **Functoriality of `B_dR^+`**: `B_dR^+(R) → B_dR^+(S)` for `f : R →+* S`. -/
def bdrPlusMap (f : R →+* S) : BDeRhamPlus R p →+* BDeRhamPlus S p :=
  adicMap _ _ (locMap p f) (ker_le_comap_locMap p f)

end BdR


/-! ### Inverse pairs, generators of `ker θ`, and the map on `B_dR` -/

section Inverse

variable (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)

include hgf in
theorem modPMap_comp_eq_id (y : ModP R p) : modPMap p g (modPMap p f y) = y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  change Ideal.Quotient.mk _ (g (f x)) = _
  rw [hgf]

include hgf in
theorem preTiltMap_comp_eq_id (y : PreTilt R p) : preTiltMap p g (preTiltMap p f y) = y :=
  Perfection.ext fun n => by
    rw [coeff_preTiltMap, coeff_preTiltMap, modPMap_comp_eq_id p f g hgf]

include hgf in
theorem wittMap_comp_eq_id (y : WittVector p (PreTilt R p)) :
    WittVector.map (preTiltMap p g) (WittVector.map (preTiltMap p f) y) = y := by
  ext n
  rw [WittVector.map_coeff, WittVector.map_coeff, preTiltMap_comp_eq_id p f g hgf]

include hgf in
theorem locMap_comp_eq_id (y : Localization.Away (p : WittVector p (PreTilt R p))) :
    locMap p g (locMap p f y) = y := by
  have h : (locMap p g).comp (locMap p f) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : WittVector p (PreTilt R p)))
    ext w
    simp only [RingHom.comp_apply, RingHom.id_apply, locMap, Localization.awayLift,
      IsLocalization.Away.lift, IsLocalization.lift_eq]
    rw [wittMap_comp_eq_id p f g hgf]
  exact congrArg (fun φ => φ y) h


include hgf in
/-- If `ker θ_R[1/p] = (a)`, then `ker θ_S[1/p] = (locMap f a)` (for an isomorphism `f`). -/
theorem ker_eq_span_locMap (hfg : ∀ y, f (g y) = y)
    (a : Localization.Away (p : WittVector p (PreTilt R p)))
    (ha : RingHom.ker (fontaineThetaInvertP R p) = Ideal.span {a}) :
    RingHom.ker (fontaineThetaInvertP S p) = Ideal.span {locMap p f a} := by
  apply le_antisymm
  · intro x hx
    have h1 : locMap p g x ∈ RingHom.ker (fontaineThetaInvertP R p) :=
      ker_le_comap_locMap p g hx
    rw [ha, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    rw [Ideal.mem_span_singleton']
    refine ⟨locMap p f c, ?_⟩
    rw [← map_mul, hc, locMap_comp_eq_id p g f hfg]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine ker_le_comap_locMap p f ?_
    rw [ha]
    exact Ideal.mem_span_singleton_self a

end Inverse

section AdicOf

variable {A B : Type*} [CommRing A] [CommRing B] (J : Ideal A) (J' : Ideal B) (g : A →+* B)
  (hg : J ≤ J'.comap g)

theorem adicMap_evalₐ (n : ℕ) (x : AdicCompletion J A) :
    AdicCompletion.evalₐ J' n (adicMap J J' g hg x) = adicMapAux J J' g hg n x := by
  unfold adicMap
  exact AdicCompletion.evalₐ_liftRingHom _ _ (adicMapAux_compat J J' g hg) n x

theorem adicMap_of (x : A) :
    adicMap J J' g hg (AdicCompletion.of J A x) = AdicCompletion.of J' B (g x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [adicMap_evalₐ, AdicCompletion.evalₐ_of]
  simp only [adicMapAux, RingHom.comp_apply]
  erw [AdicCompletion.evalₐ_of]

end AdicOf

section BdRMap


/-- The submonoid of `B_dR^+(R)` inverted in Mathlib's `BDeRham R p`. -/
def genMonoid (T : Type*) [CommRing T] [Fact ¬IsUnit (p : T)]
    [IsAdicComplete (span {(p : T)}) T] : Submonoid (BDeRhamPlus T p) :=
  Submonoid.closure <| AdicCompletion.of (RingHom.ker (fontaineThetaInvertP T p)) _ ''
    {a | RingHom.ker (fontaineThetaInvertP T p) = Ideal.span {a}}

theorem genMonoid_le_comap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x)
    (hfg : ∀ y, f (g y) = y) :
    genMonoid p R ≤ (genMonoid p S).comap (bdrPlusMap p f) := by
  rw [genMonoid, Submonoid.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Submonoid.subset_closure
  refine ⟨locMap p f a, (ker_eq_span_locMap p f g hgf hfg a ha), ?_⟩
  exact (adicMap_of _ _ _ _ a).symm

/-- **The map on `B_dR`** induced by a ring isomorphism `f` (with inverse `g`). Mathlib's
`BDeRham R p` is by definition `Localization (genMonoid p R)`. -/
def bdrMap (f : R →+* S) (g : S →+* R) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    Localization (genMonoid p R) →+* Localization (genMonoid p S) :=
  IsLocalization.map (M := genMonoid p R) (T := genMonoid p S) (Localization (genMonoid p S))
    (bdrPlusMap p f) (genMonoid_le_comap p f g hgf hfg)

end BdRMap

end PkgI4.DR

/-! ## Abelian varieties and Tate modules: copied from pkg-I3

Lines 26-335 of `scratch/pkg-I3/I3.lean` on `origin/wip/pkg-I3` (commit 7406c0ae), unchanged:
`PkgI4.I3.Tate.T`, `PkgI4.I3.AbVar`, `AbVar.Pt`, `AbVar.V`, `AbVar.galRep`. Used only by the statement
`DeRhamComparison` (§3). -/

/-! ## 1. The `ℓ`-adic Tate module of an abelian group -/

namespace PkgI4.I3.Tate

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

end PkgI4.I3.Tate

/-! ## 2. Abelian varieties, their Hom groups, points, Tate modules -/

namespace PkgI4.I3

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

end PkgI4.I3

namespace PkgI4

open scoped MatrixGroups ModularForm

/-! ## §0. Galois side over `ℚ̄` -/

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ = Gal(ℚ̄/ℚ)`, with Mathlib's Krull topology. -/
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

/-- `v` is a place of `ℚ̄` above the prime `p`: a valuation subring of `ℚ̄` in which `p` is not a
unit. -/
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits

/-- `σ` is an arithmetic Frobenius at the place `v` above `p`. -/
def IsArithFrob (σ : GQ) (v : ValuationSubring Qbar) (p : ℕ) : Prop :=
  σ ∈ v.decompositionSubgroup ℚ ∧ ∀ x ∈ v, σ x - x ^ p ∈ v.nonunits

/-- A continuous `n`-dimensional representation of `G_ℚ` over `ℚ̄_ℓ` (`PadicAlgCl ℓ` with its
spectral norm). As in Pan's paper, the coefficients are `ℚ̄_ℓ`. -/
structure GaloisRep (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) where
  toHom : GQ →* GL (Fin n) (PadicAlgCl ℓ)
  continuous_toHom : Continuous toHom

/-- A continuous character `G_ℚ → ℚ̄_ℓ^×`. -/
structure GaloisChar (ℓ : ℕ) [Fact ℓ.Prime] where
  toHom : GQ →* (PadicAlgCl ℓ)ˣ
  continuous_toHom : Continuous toHom

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The matrix of `ρ(σ)`. -/
def GaloisRep.mat (ρ : GaloisRep ℓ n) (σ : GQ) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) :=
  (ρ.toHom σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ))

/-- `ρ` is unramified at `p`: every inertia group above `p` acts trivially. -/
def GaloisRep.UnramifiedAt (ρ : GaloisRep ℓ n) (p : ℕ) : Prop :=
  ∀ v : ValuationSubring Qbar, LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ρ.toHom ((σ : v.decompositionSubgroup ℚ) : GQ) = 1

/-- `ρ` is ramified at only finitely many primes. -/
def GaloisRep.FinitelyRamified (ρ : GaloisRep ℓ n) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p

/-- `c` is a complex conjugation: it is `z ↦ z̄` through some embedding `ℚ̄ → ℂ`. -/
def IsComplexConj (c : GQ) : Prop :=
  ∃ ι : Qbar →ₐ[ℚ] ℂ, ∀ x, ι (c x) = starRingEnd ℂ (ι x)

/-- `ρ` is odd: `det ρ(c) = −1` for every complex conjugation `c` (Pan, Conj. 1.0.1). -/
def GaloisRep.IsOdd (ρ : GaloisRep ℓ 2) : Prop :=
  ∀ c, IsComplexConj c → (ρ.mat c).det = -1

/-- `ρ` is irreducible over the algebraically closed `ℚ̄_ℓ`, in Burnside's form: the image spans
`M_n(ℚ̄_ℓ)`. -/
def GaloisRep.IsIrreducible (ρ : GaloisRep ℓ n) : Prop :=
  Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) = ⊤

/-- `ρ` is semisimple: every invariant subspace has an invariant complement. -/
def GaloisRep.IsSemisimple (ρ : GaloisRep ℓ n) : Prop :=
  ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
    (∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W) →
    ∃ W', IsCompl W W' ∧ ∀ σ, W'.map (Matrix.toLin' (ρ.mat σ)) ≤ W'

/-! ## §1. The local Galois group, `ℂ_p`, and Hodge–Tate multiplicities -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `G_{ℚ_p} = Gal(ℚ̄_p/ℚ_p)`, with `ℚ̄_p = PadicAlgCl p`; this is Mathlib's
`Field.absoluteGaloisGroup ℚ_[p]`. -/
abbrev GQp := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

/-- The decomposition map `G_{ℚ_p} → G_ℚ` (restriction along an embedding `ℚ̄ → ℚ̄_p`, Mathlib's
`Field.absoluteGaloisGroup.map`). Its image is a decomposition group at a place above `p`; the
choice of embedding changes it by conjugation, which no property below depends on. -/
def decomp : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
    Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ)

/-- `ρ|_{G_{ℚ_p}}`. -/
def GaloisRep.restrictLocal (ρ : GaloisRep ℓ n) : GQp p →* GL (Fin n) (PadicAlgCl ℓ) :=
  ρ.toHom.comp (decomp p)

/-- Every `σ ∈ G_{ℚ_p}` is an isometry of `ℚ̄_p` (Mathlib: `spectralNorm_eq_of_equiv`). -/
theorem norm_gqp_apply (σ : GQp p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem continuous_gqp (σ : GQp p) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_gqp_apply p σ)).continuous

/-- `σ ∈ G_{ℚ_p}` as a continuous ring endomorphism of `ℚ̄_p`. -/
def gqpRingHom (σ : GQp p) : PadicAlgCl p →+* PadicAlgCl p := σ.toAlgHom.toRingHom

theorem continuous_gqpRingHom (σ : GQp p) : Continuous (gqpRingHom p σ) :=
  continuous_gqp p σ

/-- The action of `σ ∈ G_{ℚ_p}` on `ℂ_p = ℂ_[p]`: the extension of `σ` to the completion. -/
def cpAct (σ : GQp p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom (gqpRingHom p σ) (continuous_gqpRingHom p σ)

theorem cpAct_coe (σ : GQp p) (x : PadicAlgCl p) :
    cpAct p σ (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ x

theorem cpAct_algebraMap (σ : GQp p) (c : ℚ_[p]) :
    cpAct p σ (algebraMap ℚ_[p] ℂ_[p] c) = algebraMap ℚ_[p] ℂ_[p] c := by
  rw [IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    cpAct_coe, AlgEquiv.commutes]

/-- The `p`-adic cyclotomic character `χ : G_{ℚ_p} → ℤ_p^×` (Mathlib's `cyclotomicCharacter`
on `ℚ̄_p`, which contains all `p`-power roots of unity). -/
def cyc (σ : GQp p) : ℤ_[p]ˣ :=
  cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv

/-- `χ(σ)^i ∈ ℚ_p` for `i ∈ ℤ`. -/
def cycPow (σ : GQp p) (i : ℤ) : ℚ_[p] :=
  ((((cyc p σ) ^ i : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]

/-- For an `E`-linear representation `ρ` of `G_{ℚ_p}` on `V = E^n` (`E/ℚ_p` finite), the space
`H_i(ρ) = { φ : V →ₗ[ℚ_p] ℂ_p | φ(ρ(σ)v) = χ(σ)^i · σ(φ(v)) }`. It is
`(ℂ_p(i) ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}` written as equivariant maps. -/
def htSpace (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = cycPow p σ i • cpAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- **Hodge–Tate multiplicity** of the weight `w`, in the convention of N5 and Pan: the
cyclotomic character has weight `−1`. It is `dim_E (ℂ_p(−w) ⊗ V^∨)^{G}` =
`dim_E (ℂ_p(w) ⊗ V)^{G}`·, computed as `dim_{ℚ_p} H_{−w}(ρ) / [E : ℚ_p]`. (Check: for `V = ℚ_p(1)`,
`H_i ≠ 0` iff `ℂ_p(1−i)^G ≠ 0` iff `i = 1`, i.e. weight `−1`, by Tate's theorem.) -/
def htMult (ρ : GQp p →* GL (Fin n) E) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpace p ρ (-w)) / Module.finrank ℚ_[p] E

/-- `ρ` is Hodge–Tate with weight multiset `S` (`card S = n` makes it Hodge–Tate). -/
def HasHTWeights (ρ : GQp p →* GL (Fin n) E) (S : Multiset ℤ) : Prop :=
  ∀ w : ℤ, htMult p ρ w = S.count w

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` has Hodge–Tate weights `S`: it takes values in
`GL_n(E)` for a finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation has weights `S`. (The
multiplicities do not depend on `E`, by base change; STANDARD.) -/
def LocalHasHTWeights (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (S : Multiset ℤ) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    HasHTWeights p ρE S

/-- `ρ|_{G_{ℚ_p}}` has Hodge–Tate weights `S` (for `ρ` with `ℚ̄_p` coefficients). -/
def GaloisRep.HasHTWeightsAtSelf (ρ : GaloisRep p n) (S : Multiset ℤ) : Prop :=
  LocalHasHTWeights p (ρ.restrictLocal p) S

/-- `ρ|_{G_{ℚ_p}}` has distinct Hodge–Tate weights (2-dimensional case). -/
def GaloisRep.DistinctHTWeights (ρ : GaloisRep p 2) : Prop :=
  ∃ a b : ℤ, a ≠ b ∧ ρ.HasHTWeightsAtSelf p {a, b}


/-! ### Sanity check of the Hodge–Tate convention (given Tate's theorem as a hypothesis) -/

/-- `σ ↦ σ` as ring automorphisms, multiplicatively. -/
def toRingEquivHom : GQp p →* (PadicAlgCl p ≃+* PadicAlgCl p) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `ℚ_p(1)` as a one-dimensional representation over `ℚ_p`. -/
def cycRep : GQp p →* GL (Fin 1) ℚ_[p] :=
  (Units.map (algebraMap ℚ_[p] (Matrix (Fin 1) (Fin 1) ℚ_[p])).toMonoidHom).comp
    ((Units.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]).toMonoidHom).comp
      ((cyclotomicCharacter (PadicAlgCl p) p).comp (toRingEquivHom p)))

theorem cycPow_add_one (σ : GQp p) (j : ℤ) :
    cycPow p σ (j + 1) = cycPow p σ 1 * cycPow p σ j := by
  simp only [cycPow, zpow_add, zpow_one, Units.val_mul, PadicInt.coe_mul]
  ring

theorem cycPow_one_ne_zero (σ : GQp p) : cycPow p σ 1 ≠ 0 := by
  simp only [cycPow, zpow_one]
  intro h
  have := (cyc p σ).ne_zero
  exact this (PadicInt.ext (by simp at h))

/-- **Convention check.** If `ℂ_p(j)^{G_{ℚ_p}} = 0` for `j ≠ 0` (Tate's theorem, here a
hypothesis), then `H_i(ℚ_p(1)) = 0` for `i ≠ 1`; so `htMult` of `ℚ_p(1)` vanishes outside the
weight `−1`, which is N5's and Pan's convention. -/
theorem htSpace_cycRep_eq_bot
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (i : ℤ) (hi : i ≠ 1) : htSpace p (cycRep p) i = ⊥ := by
  rw [eq_bot_iff]
  intro φ hφ
  rw [Submodule.mem_bot]
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  have hc : φ e = 0 := by
    refine tate (i - 1) (by omega) (φ e) fun σ => ?_
    have h := hφ σ e
    have hmv : Matrix.mulVec ((cycRep p σ : GL (Fin 1) ℚ_[p]) : Matrix (Fin 1) (Fin 1) ℚ_[p]) e =
        cycPow p σ 1 • e := by
      ext k
      fin_cases k
      simp [cycRep, e, Matrix.mulVec, dotProduct, cycPow, toRingEquivHom, cyc,
        Algebra.algebraMap_eq_smul_one, PadicInt.Coe.ringHom_apply]
      rfl
    rw [hmv, map_smul] at h
    have h2 : cycPow p σ 1 • φ e = (cycPow p σ 1 * cycPow p σ (i - 1)) • cpAct p σ (φ e) := by
      rw [← cycPow_add_one]; simpa using h
    rw [mul_smul] at h2
    exact (smul_right_injective _ (cycPow_one_ne_zero p σ) h2).symm
  refine LinearMap.ext fun v => ?_
  have hv : v = v 0 • e := by
    ext k; fin_cases k; simp [e]
  rw [LinearMap.zero_apply, hv, map_smul, hc, smul_zero]

theorem htMult_cycRep_eq_zero
    (tate : ∀ j : ℤ, j ≠ 0 → ∀ c : ℂ_[p], (∀ σ : GQp p, cycPow p σ j • cpAct p σ c = c) → c = 0)
    (w : ℤ) (hw : w ≠ -1) : htMult p (cycRep p) w = 0 := by
  rw [htMult, htSpace_cycRep_eq_bot p tate (-w) (by omega), finrank_bot, Nat.zero_div]

end Local

/-! ## §1b. The action of `G_{ℚ_p}` on `B_dR` and the de Rham predicate -/

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem continuous_cpAct (σ : GQp p) : Continuous (cpAct p σ) :=
  UniformSpace.Completion.continuous_map

theorem norm_cpAct (σ : GQp p) (x : ℂ_[p]) : ‖cpAct p σ x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_cpAct p σ)) continuous_norm
  | ih a => rw [cpAct_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_gqp_apply]

theorem cpAct_inv_apply (σ : GQp p) (x : ℂ_[p]) : cpAct p σ⁻¹ (cpAct p σ x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((continuous_cpAct p _).comp (continuous_cpAct p σ)) continuous_id
  | ih a =>
    rw [cpAct_coe, cpAct_coe, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

/-- `σ` acting on `𝓞_ℂ_[p]`. -/
def oAct (σ : GQp p) : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p] :=
  (cpAct p σ).restrict 𝓞_ℂ_[p] 𝓞_ℂ_[p] fun x hx => by
    rw [Cp.mem_O_iff, norm_cpAct]
    exact (Cp.mem_O_iff p x).mp hx

theorem oAct_inv_apply (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ⁻¹ (oAct p σ x) = x :=
  Subtype.ext (cpAct_inv_apply p σ x)

theorem oAct_apply_inv (σ : GQp p) (x : 𝓞_ℂ_[p]) : oAct p σ (oAct p σ⁻¹ x) = x := by
  simpa using oAct_inv_apply p σ⁻¹ x

/-- `B_dR = B_dR(𝓞_ℂ_p)`: Mathlib's `BDeRham (𝓞_ℂ_[p]) p`, unfolded (see `bdR_eq`). -/
abbrev BdR := Localization (DR.genMonoid p 𝓞_ℂ_[p])

example : BdR p = BDeRham 𝓞_ℂ_[p] p := rfl

/-- **The action of `G_{ℚ_p}` on `B_dR`**, by functoriality of Mathlib's construction. -/
def bdrAct (σ : GQp p) : BdR p →+* BdR p :=
  DR.bdrMap p (oAct p σ) (oAct p σ⁻¹) (oAct_inv_apply p σ) (oAct_apply_inv p σ)

/-! ### `ℚ_p ⊆ B_dR`, fixed by `G_{ℚ_p}` -/

instance isLocalization_padic : IsLocalization (Submonoid.powers (p : ℤ_[p])) ℚ_[p] where
  map_units := by
    rintro ⟨_, k, rfl⟩
    exact IsUnit.mk0 _ (by simp [Fact.out (p := p.Prime) |>.ne_zero])
  surj z := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < 1 / (‖z‖ + 1))
      (by simpa using (Padic.norm_p_lt_one (p := p)))
    refine ⟨⟨⟨(p : ℚ_[p]) ^ k * z, ?_⟩, ⟨(p : ℤ_[p]) ^ k, k, rfl⟩⟩, ?_⟩
    · change ‖(p : ℚ_[p]) ^ k * z‖ ≤ 1
      rw [norm_mul, norm_pow, Padic.norm_p]
      have h1 : (p : ℝ)⁻¹ ^ k * (‖z‖ + 1) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at hk
      nlinarith [norm_nonneg z, pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p)) k]
    · change z * (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * z
      push_cast
      ring
  exists_of_eq {x y} h := ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact PadicInt.ext h⟩

/-- `ℤ_p = W(𝔽_p) → W(𝓞_ℂ_p♭)`. -/
def zpToW : ℤ_[p] →+* WittVector p (PreTilt 𝓞_ℂ_[p] p) :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

/-- `ℚ_p → W(𝓞_ℂ_p♭)[1/p]`. -/
def qpToLoc : ℚ_[p] →+* Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :=
  IsLocalization.lift (M := Submonoid.powers (p : ℤ_[p]))
    (g := (algebraMap _ _).comp (zpToW p)) (by
      rintro ⟨_, k, rfl⟩
      have := (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)))
        (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))).pow k
      rw [map_natCast] at this
      simpa only [RingHom.comp_apply, map_pow, map_natCast] using this)

/-- `W(R♭)[1/p] → B_dR^+`. -/
def ofLoc : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p)) →+*
    BDeRhamPlus 𝓞_ℂ_[p] p :=
  algebraMap _ (AdicCompletion (RingHom.ker (fontaineThetaInvertP 𝓞_ℂ_[p] p))
    (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))))

/-- `ℚ_p → B_dR`. -/
def qpToBdR : ℚ_[p] →+* BdR p :=
  (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp ((ofLoc p).comp (qpToLoc p))

theorem wittMap_zpToW (f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p) (z : ℤ_[p]) :
    WittVector.map f (zpToW p z) = zpToW p z := by
  ext n
  simp only [zpToW, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) _))
    (ZMod.castHom (dvd_refl p) _)) _

theorem qpToLoc_algebraMap (z : ℤ_[p]) :
    qpToLoc p (algebraMap ℤ_[p] ℚ_[p] z) = algebraMap _ _ (zpToW p z) :=
  IsLocalization.lift_eq _ _

theorem locMap_algebraMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (w : WittVector p (PreTilt 𝓞_ℂ_[p] p)) :
    DR.locMap p f (algebraMap _ (Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) w) =
      algebraMap _ _ (WittVector.map (DR.preTiltMap p f) w) := by
  unfold DR.locMap Localization.awayLift IsLocalization.Away.lift
  rw [IsLocalization.lift_eq]
  rfl

theorem bdrPlusMap_ofLoc (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (y : Localization.Away (p : WittVector p (PreTilt 𝓞_ℂ_[p] p))) :
    DR.bdrPlusMap p f (ofLoc p y) = ofLoc p (DR.locMap p f y) := by
  have e : ∀ y', ofLoc p y' = AdicCompletion.of _ _ y' := fun y' => by
    rw [ofLoc]
    erw [AdicCompletion.algebraMap_apply]
  rw [e, e]
  exact DR.adicMap_of _ _ _ _ y

/-- `G_{ℚ_p}` fixes `ℚ_p ⊆ B_dR`. -/
theorem bdrAct_qpToBdR (σ : GQp p) (c : ℚ_[p]) : bdrAct p σ (qpToBdR p c) = qpToBdR p c := by
  have h : (bdrAct p σ).comp (qpToBdR p) = qpToBdR p := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (p : ℤ_[p]))
    ext z
    simp only [RingHom.comp_apply, qpToBdR]
    rw [qpToLoc_algebraMap, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_ofLoc,
      locMap_algebraMap, wittMap_zpToW]
  exact congrArg (fun φ => φ c) h

/-- `B_dR` as a `ℚ_p`-algebra (through `qpToBdR`). -/
instance : Algebra ℚ_[p] (BdR p) := (qpToBdR p).toAlgebra

theorem bdrAct_smul (σ : GQp p) (c : ℚ_[p]) (x : BdR p) :
    bdrAct p σ (c • x) = c • bdrAct p σ x := by
  rw [Algebra.smul_def, map_mul, Algebra.smul_def]
  congr 1
  exact bdrAct_qpToBdR p σ c

variable {E : Type*} [Field E] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E] {n : ℕ}

/-- `D_dR(V^∨) = (B_dR ⊗_{ℚ_p} V^∨)^{G_{ℚ_p}}`, written as `G_{ℚ_p}`-equivariant `ℚ_p`-linear maps
`V → B_dR`, for `V = E^n` with `E`-linear action `ρ`. -/
def ddrSpace (ρ : GQp p →* GL (Fin n) E) : Submodule ℚ_[p] ((Fin n → E) →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ (σ : GQp p) (v : Fin n → E),
    φ (Matrix.mulVec (ρ σ : Matrix (Fin n) (Fin n) E) v) = bdrAct p σ (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- **`ρ` is de Rham** (Fontaine): `dim_{ℚ_p} D_dR = dim_{ℚ_p} V`. Stated for `V^∨` (equivalent:
`V` is de Rham iff `V^∨` is; Fontaine, Astérisque 223, Thm 3.8; STANDARD), with `K = ℚ_p`. -/
def IsDeRham (ρ : GQp p →* GL (Fin n) E) : Prop :=
  Module.finrank ℚ_[p] (ddrSpace p ρ) = n * Module.finrank ℚ_[p] E

/-- A `ℚ̄_p`-valued representation of `G_{ℚ_p}` is de Rham: it takes values in `GL_n(E)` for a
finite `E/ℚ_p` inside `ℚ̄_p`, and the `E`-representation is de Rham. -/
def LocalIsDeRham (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) : Prop :=
  ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] E)
    (ρE : GQp p →* GL (Fin n) E),
    (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) ∧
    IsDeRham p ρE


/-! ### Sanity check of `IsDeRham` (given `B_dR^{G_{ℚ_p}} = ℚ_p` as a hypothesis) -/

/-- **Normalization check.** If every `G_{ℚ_p}`-invariant of `B_dR` lies in `ℚ_p` (Fontaine's
`B_dR^{G_{ℚ_p}} = ℚ_p`, here a hypothesis) and `ℚ_p → B_dR` is injective, then the trivial
one-dimensional representation is de Rham in the sense of `IsDeRham`. -/
theorem isDeRham_trivial
    (hfix : ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p))
    (hinj : Function.Injective (qpToBdR p)) :
    IsDeRham p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
  set e : Fin 1 → ℚ_[p] := fun _ => 1
  -- the evaluation-at-`0` functional, followed by `ℚ_p → B_dR`
  set φ₀ : (Fin 1 → ℚ_[p]) →ₗ[ℚ_[p]] BdR p :=
    (LinearMap.proj (R := ℚ_[p]) (φ := fun _ : Fin 1 => ℚ_[p]) 0).smulRight (1 : BdR p)
  have hφ₀ : ∀ v, φ₀ v = qpToBdR p (v 0) := fun v => by
    simp [φ₀, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hmem : φ₀ ∈ ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := by
    intro σ v
    simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec, hφ₀, bdrAct_qpToBdR]
  have hne : φ₀ ≠ 0 := by
    intro h
    have h1 := congrArg (fun ψ => ψ e) h
    simp only [hφ₀, LinearMap.zero_apply, e] at h1
    exact one_ne_zero (hinj (h1.trans (map_zero _).symm))
  have hspan : ddrSpace p (1 : GQp p →* GL (Fin 1) ℚ_[p]) = ℚ_[p] ∙ φ₀ := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := hfix (φ e) fun σ => by
        have := hφ σ e
        simp only [MonoidHom.one_apply, Units.val_one, Matrix.one_mulVec] at this
        exact this.symm
      rw [Submodule.mem_span_singleton]
      refine ⟨c, LinearMap.ext fun v => ?_⟩
      have hv : v = v 0 • e := by ext k; fin_cases k; simp [e]
      rw [LinearMap.smul_apply, hφ₀, hv, map_smul, ← hc]
      simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hmem
  rw [IsDeRham, hspan, finrank_span_singleton hne, Module.finrank_self]


/-! ### Over a finite extension `F/ℚ_p`, for any `ℚ_p`-linear representation

These forms take a Mathlib `Representation` of `G_F = Field.absoluteGaloisGroup F`, which is the
shape of pkg-I3's `AbVar.galRep` (the Galois action on `V_p(A)`); with them the comparison leaf of
C3 can be stated over genuine definitions (note §1.2). -/

section Over

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `G_F → G_{ℚ_p}` (restriction along an embedding `ℚ̄_p → F̄`; Mathlib's
`Field.absoluteGaloisGroup.map`). It is injective with image `G_{F'}`, `F'` the image of `F`. -/
def gfToGqp : Field.absoluteGaloisGroup F →* GQp p :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ_[p] F) :
    Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroup ℚ_[p])

variable {F} {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `D_dR,F(V^∨)` as `G_F`-equivariant `ℚ_p`-linear maps `V → B_dR`. -/
def ddrSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] BdR p) where
  carrier := {φ | ∀ σ v, φ (ρ σ v) = bdrAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v, bdrAct_smul]

/-- `V` (finite-dimensional over `ℚ_p`) is de Rham as a `G_F`-representation:
`dim_F D_dR,F = dim_{ℚ_p} V`, i.e. `dim_{ℚ_p} D_dR,F = [F:ℚ_p] · dim_{ℚ_p} V`. -/
def IsDeRhamOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) : Prop :=
  Module.finrank ℚ_[p] (ddrSpaceOver p ρ) = Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] V

/-- `H_i` over `F`: `G_F`-equivariant maps `V → ℂ_p(i)`. -/
def htSpaceOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    Submodule ℚ_[p] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  carrier := {φ | ∀ σ v,
    φ (ρ σ v) = cycPow p (gfToGqp p F σ) i • cpAct p (gfToGqp p F σ) (φ v)}
  zero_mem' := by intro σ v; simp
  add_mem' := by
    intro φ ψ hφ hψ σ v
    simp only [Set.mem_ofPred_eq] at hφ hψ
    simp only [LinearMap.add_apply, hφ σ v, hψ σ v, map_add, smul_add]
  smul_mem' := by
    intro c φ hφ σ v
    simp only [Set.mem_ofPred_eq] at hφ
    simp only [LinearMap.smul_apply, hφ σ v]
    rw [Algebra.smul_def c (φ v), map_mul, cpAct_algebraMap, ← Algebra.smul_def, smul_comm]

/-- Hodge–Tate multiplicity of `w` for a `G_F`-representation on a `ℚ_p`-space (cyclotomic
weight `−1`): `dim_F (ℂ_p(−w) ⊗ V^∨)^{G_F}`. For `V_p(A)`, `dim A = g`, the multiplicities are
`g` at `0` and `g` at `−1`. -/
def htMultOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (w : ℤ) : ℕ :=
  Module.finrank ℚ_[p] (htSpaceOver p ρ (-w)) / Module.finrank ℚ_[p] F

end Over

end DeRham

/-! ## §2. Modular side -/

/-- Cusp forms of weight `k` on `Γ₁(N)` (Mathlib). -/
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k

/-- The `m`-th q-expansion coefficient `a_m(f)` (period 1). -/
def coeff {N : ℕ} {k : ℤ} (f : CF N k) (m : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff m

/-- `f` has nebentypus `χ`: `f|_k γ = χ(d) f` for `γ = (a b; c d) ∈ Γ₀(N)`. -/
def HasNebentypus {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 N, (⇑f ∣[k] γ) = χ (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) • ⇑f

/-- `f` is a normalized eigenform of all Hecke operators `T_n` with nebentypus `χ`, through its
coefficients: `a₁ = 1` and `a_m a_n = Σ_{d ∣ (m,n)} χ(d) d^{k−1} a_{mn/d²}`. Equivalent to the
Hecke definition for forms with nebentypus `χ` (Diamond–Shurman Prop. 5.3.1 and §5.8; locator
UNVERIFIED). Same as hdec-faithful. -/
def IsNormalizedEigenform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  HasNebentypus f χ ∧ coeff f 1 = 1 ∧
    ∀ m n : ℕ, 0 < m → 0 < n →
      coeff f m * coeff f n =
        ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * coeff f (m * n / d ^ 2)

/-- `τ ↦ dτ` on `ℍ`, for `d ≥ 1`. -/
def scaleH (d : ℕ+) (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(d : ℂ) * (τ : ℂ), by
    have h := τ.coe_im_pos
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast d.pos) h⟩

/-- The **old space** of level `N`, weight `k`: the span of the functions `τ ↦ f(dτ)` with
`f ∈ S_k(Γ₁(M))`, `M ∣ N`, `M < N`, `d ∣ N/M` (Atkin–Lehner, Li 1975 §1). -/
def oldSpace (N : ℕ) (k : ℤ) : Submodule ℂ (UpperHalfPlane → ℂ) :=
  Submodule.span ℂ {F | ∃ (M : ℕ) (d : ℕ+) (f : CF M k), 0 < M ∧ M ∣ N ∧ M < N ∧
    (d : ℕ) * M ∣ N ∧ F = fun τ => f (scaleH d τ)}

/-- `f` is a **newform** of level `N`: a normalized eigenform of all `T_n` not lying in the old
space. For an eigenform of all `T_n` this is equivalent to Li's definition (orthogonal to the
old space for the Petersson product): the new and old spaces are stable under all `T_n` and, by
strong multiplicity one, share no eigensystem away from `N` (Li 1975, Thms 3 and 5;
Diamond–Shurman Thm 5.8.2; locators UNVERIFIED). The Petersson definition needs the Petersson
integral over `Γ₁(N)\ℍ`, which Mathlib lacks (it has the integrand, `petersson`). -/
def IsNewform {N : ℕ} {k : ℤ} (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  IsNormalizedEigenform f χ ∧ (⇑f : UpperHalfPlane → ℂ) ∉ oldSpace N k

/-- `ρ` is attached to the eigenform `g` (through `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`), in the
Tate-module normalization (arithmetic Frobenius, `tr = a_p`): for `p ∤ Nℓ`, `ρ` is unramified at
`p` and every arithmetic Frobenius above `p` has trace `ιL(α)` with `ιC(α) = a_p(g)`. -/
def GaloisRep.AttachedTo (ρ : GaloisRep ℓ 2) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : CF N k) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = ιL α

/-- `ρ` is attached to `g` **up to the twist** `ψ`, outside a finite set `S`: Pan's conclusion
"comes from a cuspidal eigenform up to twist", in trace form (see `PanFor`). -/
def GaloisRep.AttachedUpToTwist (ρ : GaloisRep ℓ 2) (ψ : GaloisChar ℓ) (ιC : Qbar →ₐ[ℚ] ℂ)
    (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) {N : ℕ} {k : ℤ} (g : CF N k) (S : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ S →
    ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff g p ∧
      ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
        (ρ.mat σ).trace = (ψ.toHom σ : PadicAlgCl ℓ) * ιL α

/-! ## §3. Leaves of I4 statable now (statements only; none is proved) -/

/-- **I4-L0. de Rham comparison for abelian varieties, with Hodge–Tate weights** (C3; Fontaine,
LNM 1016 (1983) and Fontaine–Messing (1987) for abelian varieties; Faltings 1989; Tsuji 1999 with
de Jong; Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3 and the 2016 corrigendum; with
`V_p(A) ≅ H¹_et(A_F̄, ℚ_p)^∨`, Mumford §§19-20 / Milne 1986 Thm 15.1(a); numbers UNVERIFIED except
Scholze's wording, VERIFIED by h-leaves §3.1). For an abelian variety `A` of dimension `g` over a
finite extension `F` of `ℚ_p`, `V_p(A)` (pkg-I3's `galRep`) is de Rham as a
`G_F`-representation, with Hodge–Tate weight `0` and `−1` each of multiplicity `g`. Consequence
form. Statable now over genuine definitions: pkg-I3's abelian varieties and Tate modules, and
§1b's `IsDeRhamOver`, `htMultOver`. -/
def DeRhamComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
      htMultOver p (A.galRep p) (-1) = g

/-- **I4-L1. Galois representations of eigenforms** (Eichler–Shimura and Shimura 1971 Thm 7.14
for `k = 2`; Deligne 1971 for `k ≥ 2`; Deligne–Serre 1974 Thm 6.1 for `k = 1`; theorem numbers
UNVERIFIED). Consequence form (the published statements also give the determinant
`ε_g χ^{k−1}`). Same as hdec-faithful L27(a). -/
def EigenformRepExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g

/-- **I4-L2. Hodge–Tate weights of eigenform representations, every level** (Faltings, Math.
Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level); Kato, Astérisque 295 (2004) §9.4 (de Rham, every level); Scholl 1990
with Scholze 2013 and Fontaine's closure). A semisimple `ρ` attached to a normalized eigenform of
weight `k ≥ 2` and any level `N` (including `ℓ ∣ N`) is Hodge–Tate at `ℓ` with weights
`{0, 1 − k}` in the Tate normalization (cyclotomic weight `−1`; h-trust C8). Consequence form
(the published theorems give de Rham or pst, which imply Hodge–Tate with the same weights). -/
def EigenformHT : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **I4-L3. Deligne–Serre** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with Chebotarev and
Brauer–Nesbitt): a semisimple `ρ` attached to a weight-one eigenform has finite image.
Consequence form. Same as hdec-faithful L27(b). -/
def DeligneSerreFinite : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

/-- **I4-L4. Twisting an eigenform** (Shimura 1971 Prop. 3.64; Atkin–Li, Invent. Math. 48 (1978)
Prop. 3.1; locators UNVERIFIED). Consequence form. Same as hdec-faithful L28(a). -/
def EigenformTwist : Prop :=
  ∀ (N m : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ m) (g : CF N k),
    0 < N → 0 < m → IsNormalizedEigenform g χ →
    ∃ (χ' : DirichletCharacter ℂ (N * m ^ 2)) (g' : CF (N * m ^ 2) k),
      IsNormalizedEigenform g' χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * m → coeff g' p = ψ (p : ZMod m) * coeff g p

/-- **I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form. -/
def NewformOfEigenform : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

/-- **I4-L6. Carayol at unramified primes** (Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), the
case "conductor exponent 0"; theorem letter VERIFIED from N5 L9778's locator, content
UNVERIFIED). For a newform `f` of weight 2 and level `N` and a semisimple `ρ` attached to it, a
prime `p ≠ ℓ` at which `ρ` is unramified does not divide `N`. Consequence form (Théorème (A)
gives `v_p(N) =` the conductor exponent, which is 0 exactly when `ρ` is unramified). -/
def CarayolUnramified : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → ρ.UnramifiedAt p → ¬ p ∣ N

/-! ## §4. Templates (not leaves) and the statable Pan∘Berger leaf

`PanFor IsPst` is Pan's theorem once `IsPst` is the genuine "potentially semistable in the sense
of Fontaine" predicate on `ℚ̄_p`-representations of `G_{ℚ_p}`; for any other argument it means
nothing. Likewise for `BergerFor`, `CarayolFor`. -/

/-- A predicate on `ℚ̄_p`-valued representations of `G_{ℚ_p}`, for every `p` and `n`. -/
abbrev LocalPred := ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), (GQp p →* GL (Fin n) (PadicAlgCl p)) → Prop

/-- **Template for I4-L7, Pan's theorem** (Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169,
Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 from the arXiv
source; JAMS numbering UNVERIFIED)), for `p ≥ 5` (which drops the `p = 3` residual clause):
a continuous irreducible `ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many primes, potentially
semistable at `p`, odd, with distinct Hodge–Tate weights at `p`, comes from a cuspidal eigenform
up to twist. The conclusion is in trace form: some normalized eigenform `g`, continuous `ψ` and
embeddings with `tr ρ(Frob_q) = ψ(Frob_q) ι(a_q(g))` for almost all `q`. Every reading of
"comes from … up to twist" implies it, in either Frobenius normalization, since
`U^∨ ≅ U ⊗ det U⁻¹` in dimension 2 (h-trust C8; pkg-I4 note §2.1). -/
def PanFor (IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    ρ.DistinctHTWeights p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl p) (S : Finset ℕ),
        ρ.AttachedUpToTwist ψ ιC ιL g S

/-- **I4-L7′. Pan∘Berger — statable now, over genuine definitions.** Pan's Theorem 1.0.4
(`PanFor`, `p ≥ 5`) with "de Rham at `p`" (`LocalIsDeRham`, built in §1b on Mathlib's `BDeRham`)
in place of "potentially semistable at `p`". It is a consequence of Pan 2022 Thm 1.0.4 together
with Berger 2002 Thm 0.7 (de Rham ⇒ pst), and it is the form N5 uses (N5 L734-741 proves de Rham
and then applies Berger). Needs no `B_st`. -/
def PanBerger : Prop :=
  PanFor fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ

/-- **Template for I4-L8, Berger's theorem** (Invent. Math. 148 (2002), Théorème 0.7 in the
published numbering (ASTRA-READ), = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3 (VERIFIED by
rv-h-a011)): de Rham ⇒ potentially semistable. -/
def BergerFor (IsDR IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)),
    Continuous ρ → IsDR p n ρ → IsPst p n ρ

/-- **I4-L8′. Berger with the genuine de Rham predicate** (template only in `IsPst`). -/
def BergerDR (IsPst : LocalPred) : Prop :=
  BergerFor (fun (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) =>
    LocalIsDeRham p n ρ) IsPst

/-- A conductor-exponent function: `a ℓ ρ p` is the Artin conductor exponent at `p ≠ ℓ` of the
`ℓ`-adic representation `ρ` (Weil–Deligne / Serre's definition). Missing in every library. -/
abbrev CondExp := ∀ (ℓ : ℕ) [Fact ℓ.Prime], GaloisRep ℓ 2 → ℕ → ℕ

/-- **Template for I4-L9, Carayol's Théorème (A)** at `F = ℚ`, weight 2 (the case N5 uses):
for a newform `f` of level `N` and a semisimple `ρ` attached to it, `v_p(N) = a(ρ, p)` for every
prime `p ≠ ℓ`. -/
def CarayolFor (a : CondExp) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ),
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    p.Prime → p ≠ ℓ → a ℓ ρ p = N.factorization p

/-! ## §5. Glue facts, proved -/

/-- **C8 weight comparison** (Tate normalization). If `ρ ≅ ρ_g ⊗ ψ` with `ψ` Hodge–Tate of
weight `n`, the weights of `ρ` are `{n, n + 1 − k}`; if they are `{0, −1}` and `k ≥ 1`, then
`n = 0` and `k = 2`. Stated on multisets. -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + 1 - k} : Multiset ℤ) = {0, -1}) : n = 0 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + 1 - k} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

/-- The same comparison in Pan's cohomological normalization (weights of `ρ_g` are `{0, k−1}`):
`{n, n + k − 1} = {0, −1}` with `k ≥ 1` forces `k = 2`, `n = −1` (twist by `χ¹`; h-trust C8,
rv-h-c8 `weights.py`). -/
theorem weight_match_coh (n k : ℤ) (hk : 1 ≤ k)
    (h : ({n, n + k - 1} : Multiset ℤ) = {0, -1}) : n = -1 ∧ k = 2 := by
  have h0 : (0 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  have h1 : (-1 : ℤ) ∈ ({n, n + k - 1} : Multiset ℤ) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0 h1
  omega

end PkgI4

end


end PkgI4Sec

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

section DescProjRepSec
/-! ### Copied from `scratch/glue-descent/ProjRep.lean` (compiled there). -/

/-!
# glue-descent: the algebraic core of B1 and C1 (N5 L632-664, L719-731)

All statements are over arbitrary groups, fields, vector spaces and algebras (genuine Mathlib
definitions). They are the steps of Glazer's scalar descent after the abelian surface has been
replaced by its Tate realization:

* `G` stands for `G_ℚ`, `E` for a finite extension of `ℚ_ℓ` containing the image of the
  coefficient field `C`, and `V` for `V_ℓ(A) ⊗ E`;
* `T σ = μ_σ ∘ σ ∈ GL(V)` (the Tate action of `σ` followed by the `B`-linear isogeny
  `μ_σ : ^σA → A`), so that `T σ * T τ = c(σ,τ) • T (σ τ)` with `c(σ,τ) ∈ ℚ^×` (N5 L640-644);
* `a σ = (deg μ_σ)^{-1/4}` and `ε = sign c` (N5 L645-664);
* `β` the cochain of B2-B3 with `β σ β τ = ε(σ,τ) β(στ)`.

The instantiation (Tate modules, the Galois action, `End⁰(A) = B`, Skolem–Noether) is not in
Mathlib; see `docs/research/glue-descent.md`.
-/

namespace GlueDescent

open scoped BigOperators

section Cocycle

variable {G : Type*} [Group G] {E : Type*} [Field E] {A : Type*} [Ring A] [Algebra E A]
  [Nontrivial A]

/-- **B1, cocycle identity.** A projective representation with scalar discrepancy `c`
(`T g * T h = c(g,h) • T(gh)`, with `T` valued in units) has `c` a 2-cocycle for the trivial
action: `c(gh,k) c(g,h) = c(h,k) c(g,hk)`. -/
theorem cocycle_of_projective (T : G → Aˣ) (c : G → G → E)
    (hT : ∀ g h, (T g : A) * T h = c g h • (T (g * h) : A)) (g h k : G) :
    c (g * h) k * c g h = c h k * c g (h * k) := by
  have h1 : ((T g : A) * T h) * T k = (c g h * c (g * h) k) • (T (g * h * k) : A) := by
    rw [hT, smul_mul_assoc, hT, smul_smul]
  have h2 : (T g : A) * (T h * T k) = (c h k * c g (h * k)) • (T (g * (h * k)) : A) := by
    rw [hT, mul_smul_comm, hT, smul_smul, mul_comm (c h k)]
  rw [mul_assoc, h2, mul_assoc g h k] at h1
  have hu : IsUnit (T (g * (h * k)) : A) := (T _).isUnit
  have key : ((c h k * c g (h * k)) - (c g h * c (g * h) k)) • (T (g * (h * k)) : A) = 0 := by
    rw [sub_smul, h1, sub_self]
  rw [smul_eq_zero] at key
  rcases key with key | key
  · rw [mul_comm (c (g * h) k)]; exact (sub_eq_zero.mp key).symm
  · exact absurd key hu.ne_zero

end Cocycle

section Sign

/-- **B1, sign normalization (real arithmetic).** If positive degrees satisfy
`deg σ · deg τ = c⁴ · deg(στ)` (multiplicativity of degree, `deg [c] = c⁴` on an abelian
surface) and `a = deg^{-1/4}`, then `a σ · a τ · c = sign(c) · a(στ)`. -/
theorem sign_normalization {dσ dτ dστ c : ℝ} (hσ : 0 < dσ) (hτ : 0 < dτ) (hστ : 0 < dστ)
    (hc : c ≠ 0) (hdeg : dσ * dτ = c ^ 4 * dστ) :
    dσ ^ (-(1 / 4 : ℝ)) * dτ ^ (-(1 / 4 : ℝ)) * c = SignType.sign c * dστ ^ (-(1 / 4 : ℝ)) := by
  have hc4 : (0 : ℝ) < c ^ 4 := by positivity
  have habs : (c ^ 4) ^ (-(1 / 4 : ℝ)) = |c|⁻¹ := by
    have h1 : c ^ 4 = |c| ^ (4 : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (Even.pow_abs ⟨2, rfl⟩ c).symm
    rw [h1, ← Real.rpow_mul (abs_nonneg c)]
    norm_num [Real.rpow_neg_one]
  rw [← Real.mul_rpow hσ.le hτ.le, hdeg, Real.mul_rpow hc4.le hστ.le, habs]
  have hsign : (SignType.sign c : ℝ) = c / |c| := by
    rcases lt_or_gt_of_ne hc with h | h
    · rw [sign_neg h, abs_of_neg h]; field_simp; simp
    · rw [sign_pos h, abs_of_pos h]; field_simp; simp
  rw [hsign]
  have : |c| ≠ 0 := abs_ne_zero.mpr hc
  field_simp

/-- The sign of a nonzero real is `±1`. -/
theorem sign_sq_eq_one {c : ℝ} (hc : c ≠ 0) : (SignType.sign c : ℝ) ^ 2 = 1 := by
  rcases lt_or_gt_of_ne hc with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- **B1, `ε` is a normalized cocycle.** If `c` is a 2-cocycle with values in `ℝ^×` (trivial
action) normalized by `c(1,·) = c(·,1) = 1`, then so is `ε = sign ∘ c`. -/
theorem sign_cocycle {G : Type*} [Group G] (c : G → G → ℝ)
    (hcoc : ∀ g h k, c (g * h) k * c g h = c h k * c g (h * k)) (g h k : G) :
    (SignType.sign (c (g * h) k) : ℝ) * SignType.sign (c g h) =
      SignType.sign (c h k) * SignType.sign (c g (h * k)) := by
  have := congrArg (fun x : ℝ => (SignType.sign x : ℝ)) (hcoc g h k)
  simpa [sign_mul] using this

end Sign

section Rho

variable {G : Type*} [Group G] {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- The descended operator `ρ(g) = β(g)⁻¹ a(g) T(g)`. -/
def rho (T : G → Module.End E V) (a β : G → E) (g : G) : Module.End E V :=
  ((β g)⁻¹ * a g) • T g

/-- **C1, `ρ` is a representation.** With `T g * T h = c(g,h) • T(gh)`, scalars `a` with
`a g · a h · c(g,h) = ε(g,h) · a(gh)` and a cochain `β` with `β g · β h = ε(g,h) · β(gh)`
(`β` nonzero), `ρ(g) = β(g)⁻¹ a(g) T(g)` is multiplicative (N5 L723-729). -/
theorem rho_map_mul (T : G → Module.End E V) (c ε : G → G → E) (a β : G → E)
    (hT : ∀ g h, T g * T h = c g h • T (g * h))
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h))
    (hβ0 : ∀ g, β g ≠ 0) (g h : G) :
    rho T a β g * rho T a β h = rho T a β (g * h) := by
  unfold rho
  rw [smul_mul_smul_comm, hT, smul_smul]
  congr 1
  have hgh : β (g * h) ≠ 0 := hβ0 _
  have hg := hβ0 g
  have hh := hβ0 h
  have hε : ε g h ≠ 0 := by
    intro h0; apply mul_ne_zero hg hh; rw [hβ, h0, zero_mul]
  have key : (β g)⁻¹ * a g * ((β h)⁻¹ * a h) * c g h = (β g * β h)⁻¹ * (a g * a h * c g h) := by
    field_simp
  rw [key, ha, hβ]
  field_simp

/-- `ρ` as a group representation, given `ρ(1) = 1` (which holds when `T 1 = 1`, `a 1 = 1`,
`β 1 = 1`). -/
def rhoRep (T : G → Module.End E V) (c ε : G → G → E) (a β : G → E)
    (hT : ∀ g h, T g * T h = c g h • T (g * h))
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h))
    (hβ0 : ∀ g, β g ≠ 0) (h1 : rho T a β 1 = 1) : Representation E G V where
  toFun := rho T a β
  map_one' := h1
  map_mul' g h := (rho_map_mul T c ε a β hT ha hβ hβ0 g h).symm

/-- **C1, `ρ` commutes with `B`.** If every `T g` commutes with an endomorphism `b` (the
`B`-linearity of `μ_σ`), so does `ρ g`. -/
theorem rho_commute (T : G → Module.End E V) (a β : G → E) (b : Module.End E V)
    (hb : ∀ g, Commute (T g) b) (g : G) : Commute (rho T a β g) b :=
  (hb g).smul_left _

/-- **C1, `ρ` is the Tate action on `G_{L'}`.** On the elements where `μ_σ = 1` (so `T` is the
Tate action `act`), `a = 1` and `β = 1` (the kernel of `β|_{G_L}`), `ρ = act`. -/
theorem rho_eq_act (T act : G → Module.End E V) (a β : G → E) (g : G)
    (hT : T g = act g) (ha : a g = 1) (hβ : β g = 1) : rho T a β g = act g := by
  simp [rho, hT, ha, hβ]

end Rho

section Split

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- A system of `2 × 2` matrix units in `End_E(V)` (the image of `M₂(E) ≅ B ⊗ E`). -/
structure MatrixUnits2 (E V : Type*) [Field E] [AddCommGroup V] [Module E V] where
  e : Fin 2 → Fin 2 → Module.End E V
  mul_e : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum_diag : e 0 0 + e 1 1 = 1

namespace MatrixUnits2

variable (u : MatrixUnits2 E V)

/-- `W = e₀₀ V`. -/
def W : Submodule E V := LinearMap.range (u.e 0 0)

theorem e00_of_mem {w : V} (hw : w ∈ u.W) : u.e 0 0 w = w := by
  obtain ⟨v, rfl⟩ := hw
  have := u.mul_e 0 0 0 0
  simp only [ite_true] at this
  rw [← Module.End.mul_apply, this]

theorem e_apply_e (i j k l : Fin 2) (v : V) :
    u.e i j (u.e k l v) = if j = k then u.e i l v else 0 := by
  rw [← Module.End.mul_apply, u.mul_e]
  split_ifs <;> simp

theorem mem_W_of_e0 (j : Fin 2) (v : V) : u.e 0 j v ∈ u.W :=
  ⟨u.e 0 j v, by rw [u.e_apply_e]; simp⟩

/-- The linear isomorphism `V ≃ W × W`, `v ↦ (e₀₀ v, e₀₁ v)`, inverse `(w₁, w₂) ↦ w₁ + e₁₀ w₂`. -/
noncomputable def splitEquiv : V ≃ₗ[E] u.W × u.W :=
  LinearEquiv.ofLinearMap
    (LinearMap.prod ((u.e 0 0).codRestrict u.W (fun v => u.mem_W_of_e0 0 v))
      ((u.e 0 1).codRestrict u.W (fun v => u.mem_W_of_e0 1 v)))
    (LinearMap.coprod u.W.subtype (u.e 1 0 ∘ₗ u.W.subtype))
    (by
      ext ⟨w, hw⟩ <;> simp [u.e00_of_mem hw, u.e_apply_e]
      · obtain ⟨v, rfl⟩ := hw; simp [u.e_apply_e])
    (by
      ext v
      change u.e 0 0 v + u.e 1 0 (u.e 0 1 v) = v
      rw [u.e_apply_e]
      simp only [ite_true]
      have := congrArg (fun f : Module.End E V => f v) u.sum_diag
      simpa using this)

/-- A representation commuting with the matrix units preserves `W`. -/
theorem mapsTo_W {G : Type*} [Monoid G] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) {w : V} (hw : w ∈ u.W) : ρ g w ∈ u.W := by
  obtain ⟨v, rfl⟩ := hw
  exact ⟨ρ g v, by rw [← Module.End.mul_apply, ← (hc g 0 0).eq, Module.End.mul_apply]⟩

/-- **C1, `ρ ≅ r ⊕ r`.** If `ρ` commutes with the matrix units, the isomorphism `V ≃ W × W`
intertwines `ρ g` with `ρ g|_W × ρ g|_W`. (N5 L729-730: "matrix units give
`ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`".) -/
theorem splitEquiv_intertwines {G : Type*} [Monoid G] (ρ : Representation E G V)
    (hc : ∀ g i j, Commute (ρ g) (u.e i j)) (g : G) (v : V) :
    u.splitEquiv (ρ g v) =
      (⟨ρ g (u.splitEquiv v).1, u.mapsTo_W ρ hc g (u.splitEquiv v).1.2⟩,
       ⟨ρ g (u.splitEquiv v).2, u.mapsTo_W ρ hc g (u.splitEquiv v).2.2⟩) := by
  ext <;> simp [splitEquiv, LinearEquiv.coe_ofLinearMap, ← Module.End.mul_apply,
    (hc g 0 0).eq, (hc g 0 1).eq]

/-- **C1, `dim r = 2`.** If `dim V = 4` then `dim W = 2`. -/
theorem finrank_W (h4 : Module.finrank E V = 4) [FiniteDimensional E V] :
    Module.finrank E u.W = 2 := by
  have := u.splitEquiv.finrank_eq
  rw [Module.finrank_prod, h4] at this
  omega

end MatrixUnits2

end Split

section Span

variable {E : Type*} [Field E] {V : Type*} [AddCommGroup V] [Module E V]

/-- **C1, from `B` to `B ⊗ E`.** An endomorphism commuting with every element of `S` (the image
of `B`) commutes with the `E`-subalgebra generated by `S` (the image of `B ⊗_ℚ E ≅ M₂(E)`,
which contains the matrix units). -/
theorem commute_adjoin (f : Module.End E V) (S : Set (Module.End E V))
    (hS : ∀ s ∈ S, Commute f s) {x : Module.End E V} (hx : x ∈ Algebra.adjoin E S) :
    Commute f x := by
  have hle : Algebra.adjoin E S ≤ Subalgebra.centralizer E {f} := by
    apply Algebra.adjoin_le
    intro s hs
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (hS s hs).eq
  have := hle hx
  rw [Subalgebra.mem_centralizer_iff] at this
  exact this f rfl

end Span

end GlueDescent


end DescProjRepSec

section DescB1QuatSec
/-! ### Copied from `scratch/glue-descent/B1Quat.lean` (compiled there). -/

/-!
# glue-descent: the quaternion algebra of B1 (N5 L637-644)

N5's `B = (2, -3)` is Mathlib's `ℍ[ℚ, 2, -3] = QuaternionAlgebra ℚ 2 0 (-3)` (`i² = 2`,
`j² = -3`, `ij = -ji = k`).

* `B6_commute_i_j`: an element commuting with `i` and `j` is a rational scalar. This is the step
  "`c(σ,τ)` commutes with `B`, hence belongs to `ℚ^×`" (N5 L640-644), given `End⁰(A_ℚ̄) = B`.
* `B6_isCentral`: `Algebra.IsCentral ℚ B6`.
* `LeafSkolemNoether`: the Skolem–Noether theorem (automorphism case) over Mathlib's central
  simple algebras, the literature input of B1 (Reiner, *Maximal orders*, Thm 7.21; formalized in
  Tau Ceti, not in Mathlib v4.35).
-/

namespace GlueDescent

open Quaternion

/-- N5's quaternion algebra `B = (2, -3)` of discriminant 6. -/
abbrev B6 := ℍ[ℚ, 2, -3]

/-- `i ∈ B`. -/
def qi : B6 := ⟨0, 1, 0, 0⟩
/-- `j ∈ B`. -/
def qj : B6 := ⟨0, 0, 1, 0⟩

/-- **B1, the discrepancy is a scalar.** An element of `B` commuting with `i` and `j` lies in `ℚ`. -/
theorem B6_commute_i_j (x : B6) (hi : x * qi = qi * x) (hj : x * qj = qj * x) :
    x = algebraMap ℚ B6 x.re := by
  have e1 := congrArg QuaternionAlgebra.imI hi
  have e2 := congrArg QuaternionAlgebra.imJ hi
  have e3 := congrArg QuaternionAlgebra.imK hi
  have f1 := congrArg QuaternionAlgebra.imI hj
  have f2 := congrArg QuaternionAlgebra.imJ hj
  have f3 := congrArg QuaternionAlgebra.imK hj
  simp [qi, qj, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] at e1 e2 e3 f1 f2 f3
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- `B` is central over `ℚ`. -/
instance B6_isCentral : Algebra.IsCentral ℚ B6 where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    exact ⟨x.re, (B6_commute_i_j x (hx qi).symm (hx qj).symm).symm⟩

/-- **Leaf L-B1 (Skolem–Noether, automorphism case).** Every `K`-algebra automorphism of a
finite-dimensional central simple `K`-algebra is inner. -/
def LeafSkolemNoether : Prop :=
  ∀ (K : Type) [Field K] (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (φ : A ≃ₐ[K] A),
    ∃ u : Aˣ, ∀ a : A, φ a = u * a * (u⁻¹ : Aˣ)

/-! ### `B` is a division algebra, hence simple (so `LeafSkolemNoether` applies to it) -/

theorem zmod3_aniso : ∀ x y : ZMod 3, x ^ 2 - 2 * y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

theorem three_dvd_of_form {a b e : ℤ} (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : ((a : ZMod 3)) ^ 2 - 2 * (b : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at this
    have h30 : (3 : ZMod 3) = 0 := by decide
    rw [h30, zero_mul, add_zero] at this
    exact this
  obtain ⟨ha, hb⟩ := zmod3_aniso _ _ h3
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb⟩

/-- The norm form `a² - 2b² + 3c² - 6d²` of `B` is anisotropic over `ℤ` (descent mod 3). -/
theorem aniso_int : ∀ (n : ℕ) (a b c d : ℤ), a.natAbs + b.natAbs + c.natAbs + d.natAbs ≤ n →
    a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c d hn h
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ :=
    three_dvd_of_form (a := a) (b := b) (e := c ^ 2 - 2 * d ^ 2) (by linear_combination h)
  have h' : c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2) = 0 := by
    have : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := three_dvd_of_form (a := c) (b := d) h'
  have h'' : a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2 = 0 := by
    have : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  by_cases hz : a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hz; simp
  · exfalso
    apply hz
    have hsum : a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs < n := by
      simp only [Int.natAbs_mul, show (3 : ℤ).natAbs = 3 from rfl] at hn
      have : 0 < a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs := by
        by_contra h0
        apply hz
        omega
      omega
    exact ih _ hsum a' b' c' d' le_rfl h''

/-- Anisotropy over `ℚ`. -/
theorem aniso_rat (a b c d : ℚ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  set D : ℚ := (a.den : ℚ) * b.den * c.den * d.den with hD
  have hD0 : D ≠ 0 := by positivity
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * q.den := fun q =>
    (div_eq_iff (by positivity)).mp (Rat.num_div_den q)
  have ha : a * D = ((a.num * (b.den * c.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum a]; ring
  have hb : b * D = ((b.num * (a.den * c.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum b]; ring
  have hc : c * D = ((c.num * (a.den * b.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum c]; ring
  have hd : d * D = ((d.num * (a.den * b.den * c.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum d]; ring
  set A := a.num * (b.den * c.den * d.den)
  set B := b.num * (a.den * c.den * d.den)
  set C := c.num * (a.den * b.den * d.den)
  set E := d.num * (a.den * b.den * c.den)
  have hint : A ^ 2 - 2 * B ^ 2 + 3 * C ^ 2 - 6 * E ^ 2 = 0 := by
    have : ((A ^ 2 - 2 * B ^ 2 + 3 * C ^ 2 - 6 * E ^ 2 : ℤ) : ℚ) = 0 := by
      push_cast
      rw [← ha, ← hb, ← hc, ← hd]
      linear_combination D ^ 2 * h
    exact_mod_cast this
  obtain ⟨h1, h2, h3, h4⟩ := aniso_int _ A B C E le_rfl hint
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ha; rw [h1] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hb; rw [h2] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hc; rw [h3] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hd; rw [h4] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0

/-- `star x * x` is the scalar `x.re² - 2 x.imI² + 3 x.imJ² - 6 x.imK²`. -/
theorem B6_star_mul (x : B6) :
    star x * x = algebraMap ℚ B6 (x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]
  congr 1
  simp [QuaternionAlgebra.re_mul]
  ring

/-- **`B` is simple** (it is a division algebra: the norm form is anisotropic). -/
instance B6_isSimpleRing : IsSimpleRing B6 := by
  rw [isSimpleRing_iff_isTwoSided_imp]
  refine ⟨inferInstance, fun I _ => ?_⟩
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hmem : star x * x ∈ I := I.mul_mem_left _ hxI
    rw [B6_star_mul] at hmem
    set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2
    have hn : n ≠ 0 := by
      intro h0
      obtain ⟨h1, h2, h3, h4⟩ := aniso_rat _ _ _ _ h0
      exact hx0 (QuaternionAlgebra.ext h1 h2 h3 h4)
    exact Ideal.eq_top_of_isUnit_mem I hmem
      ((IsUnit.mk0 n hn).map (algebraMap ℚ B6))

/-- **B1, Skolem–Noether at `B`**: from the leaf, every `ℚ`-automorphism of `B` is inner. -/
theorem B6_inner (hSN : LeafSkolemNoether) (φ : B6 ≃ₐ[ℚ] B6) :
    ∃ u : B6ˣ, ∀ a : B6, φ a = u * a * (u⁻¹ : B6ˣ) :=
  hSN ℚ B6 φ

end GlueDescent


end DescB1QuatSec

section DescCochainSec
/-! ### Copied from `scratch/glue-descent/Cochain.lean` (compiled there). -/

/-!
# glue-descent: the group theory of B2-B3 (N5 L693-716)

`G` stands for `G_ℚ` (or the finite quotient `Gal(L'/ℚ)` through which everything factors),
`H` for `G_L` (normal, of index `d = [L:ℚ]`), `ε` for the sign cocycle inflated from
`Gal(L/ℚ) = G/H` and normalized, `U` for the coefficient group (`E^×` for a field `E`), and
`β : G → U` for the cochain with `β σ β τ = ε(σ,τ) β(στ)`.

Proved here, over arbitrary groups (genuine Mathlib definitions):

* `β|_H` is a homomorphism and is invariant under conjugation by `G` (N5 L701);
* `K' = ker β|_H` is normal in `G`, and `β` is constant on its cosets, so `β` factors
  through `G/K' = Gal(L'/ℚ)` (implicit in N5);
* if `β^{2m} = 1` on `H` with values in a field, `[H : K'] ≤ 2m`, hence
  `[G : K'] ≤ 2m [G : H]` (N5 L711-714: `[L':ℚ] ≤ 2md`);
* twisting by a character `η` with `η² = 1` changes neither `β² = χ` nor `dβ = ε`
  (N5 L707-709);
* the cohomological core of B2: if `ε · (dβ₀)⁻¹ = dγ` with `β₀² = χ` and `γ` valued in `±1`,
  then `β = β₀ γ⁻¹` has `β² = χ` and `dβ = ε` (N5 L694-700).
-/

namespace GlueDescent

section Basic

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

/-- The coboundary relation `β σ β τ = ε(σ,τ) β(στ)` (N5 L698). -/
def IsCochainFor (ε : G → G → U) (β : G → U) : Prop :=
  ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ)

/-- `ε` is inflated from `G/H` and normalized: it is `1` as soon as one argument lies in `H`.
(This is what "inflated from `Gal(L/ℚ)`" with `μ₁ = 1` gives: `ε(σ,τ)` depends only on the
classes of `σ, τ` mod `H` and vanishes when one class is trivial.) -/
def InflatedNormalized (H : Subgroup G) (ε : G → G → U) : Prop :=
  ∀ σ τ, (σ ∈ H ∨ τ ∈ H) → ε σ τ = 1

variable {H : Subgroup G} {ε : G → G → U} {β : G → U}

theorem cochain_one (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : β 1 = 1 := by
  have h := hβ 1 1
  rw [hε 1 1 (Or.inl H.one_mem), one_mul, mul_one] at h
  exact mul_eq_left.mp h

theorem cochain_mul_right (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (σ * s) = β σ * β s := by
  rw [hβ, hε σ s (Or.inr hs), one_mul]

theorem cochain_mul_left (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (s * σ) = β s * β σ := by
  rw [hβ, hε s σ (Or.inl hs), one_mul]

/-- **B3, `β|_H` is a homomorphism** (N5 L701: "Its restriction to `G_L` is a character"). -/
def restrictHom (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : H →* U where
  toFun s := β s
  map_one' := cochain_one hβ hε
  map_mul' s t := cochain_mul_right hβ hε s t.2

/-- **B3, invariance under `G`** (N5 L701: "invariant under `G_ℚ`"): for `s ∈ H` normal,
`β(σ s σ⁻¹) = β(s)`. -/
theorem cochain_conj [H.Normal] (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {s : G} (hs : s ∈ H) : β (σ * s * σ⁻¹) = β s := by
  have hc : σ * s * σ⁻¹ ∈ H := Subgroup.Normal.conj_mem inferInstance s hs σ
  have h1 : β (σ * s) = β σ * β s := cochain_mul_right hβ hε σ hs
  have h2 : β (σ * s) = β (σ * s * σ⁻¹) * β σ := by
    rw [← cochain_mul_left hβ hε σ hc]; group
  rw [h1, mul_comm (β (σ * s * σ⁻¹))] at h2
  exact (mul_left_cancel h2).symm

/-- `K' = ker(β|_H)`, as a subgroup of `G`. -/
def kernelSubgroup (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) : Subgroup G :=
  (restrictHom hβ hε).ker.map H.subtype

theorem mem_kernelSubgroup (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) {g : G} :
    g ∈ kernelSubgroup hβ hε ↔ g ∈ H ∧ β g = 1 := by
  constructor
  · rintro ⟨⟨s, hs⟩, hk, rfl⟩
    exact ⟨hs, hk⟩
  · rintro ⟨hs, hk⟩
    exact ⟨⟨g, hs⟩, hk, rfl⟩

/-- **B3, `L'/ℚ` is Galois** (N5 L712: "Conjugacy invariance shows that `L'/ℚ` is Galois"):
`K'` is normal in `G`. -/
theorem kernelSubgroup_normal [H.Normal] (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) :
    (kernelSubgroup hβ hε).Normal where
  conj_mem g hg σ := by
    rw [mem_kernelSubgroup] at hg ⊢
    exact ⟨Subgroup.Normal.conj_mem inferInstance g hg.1 σ, by rw [cochain_conj hβ hε σ hg.1, hg.2]⟩

/-- `β` is constant on the cosets of `K'`, so it factors through `G/K' = Gal(L'/ℚ)`. -/
theorem cochain_mul_kernel (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (σ : G)
    {k : G} (hk : k ∈ kernelSubgroup hβ hε) : β (σ * k) = β σ := by
  rw [mem_kernelSubgroup] at hk
  rw [cochain_mul_right hβ hε σ hk.1, hk.2, mul_one]

/-- `K' ≤ H`. -/
theorem kernelSubgroup_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) :
    kernelSubgroup hβ hε ≤ H := fun _ hg => ((mem_kernelSubgroup hβ hε).mp hg).1

/-- **B3, twisting.** If `η : G →* U` and `β` is a cochain for `ε` with `β² = χ`, and
`η² = 1`, then `β η` is a cochain for `ε` with `(β η)² = χ` (N5 L707-709: "changes neither
displayed identity"). -/
theorem twist (hβ : IsCochainFor ε β) (η : G →* U) :
    IsCochainFor ε (fun σ => β σ * η σ) := by
  intro σ τ
  show β σ * η σ * (β τ * η τ) = ε σ τ * (β (σ * τ) * η (σ * τ))
  calc β σ * η σ * (β τ * η τ) = (β σ * β τ) * (η σ * η τ) := by ac_rfl
    _ = _ := by rw [hβ, ← map_mul]; ac_rfl

theorem twist_sq (χ : G → U) (hχ : ∀ σ, β σ ^ 2 = χ σ) (η : G →* U) (hη : ∀ σ, η σ ^ 2 = 1)
    (σ : G) : (β σ * η σ) ^ 2 = χ σ := by
  rw [mul_pow, hχ, hη, mul_one]

/-- **B2, the cohomological core** (N5 L694-700). `β₀` is a pointwise square root of the
character `χ`; its coboundary `ε₀(σ,τ) = β₀ σ β₀ τ / β₀(στ)` differs from `ε` by the
coboundary of a sign cochain `γ` (this is the global equality `δχ = [ε]` in
`H²(G_ℚ, ±1)`). Then `β = β₀ γ⁻¹` satisfies `β² = χ` and `dβ = ε`. -/
theorem cochain_of_boundary_eq (χ : G → U) (β₀ γ : G → U) (hβ₀ : ∀ σ, β₀ σ ^ 2 = χ σ)
    (hγ : ∀ σ, γ σ ^ 2 = 1)
    (hdiff : ∀ σ τ, β₀ σ * β₀ τ * (β₀ (σ * τ))⁻¹ =
      ε σ τ * (γ σ * γ τ * (γ (σ * τ))⁻¹)) :
    IsCochainFor ε (fun σ => β₀ σ * (γ σ)⁻¹) ∧ ∀ σ, (β₀ σ * (γ σ)⁻¹) ^ 2 = χ σ := by
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · have h := hdiff σ τ
    have h' : β₀ σ * β₀ τ = ε σ τ * (γ σ * γ τ * (γ (σ * τ))⁻¹) * β₀ (σ * τ) := by
      rw [← h]; group
    calc β₀ σ * (γ σ)⁻¹ * (β₀ τ * (γ τ)⁻¹) = (β₀ σ * β₀ τ) * (γ σ * γ τ)⁻¹ := by
          rw [mul_inv]; ac_rfl
      _ = ε σ τ * (β₀ (σ * τ) * (γ (σ * τ))⁻¹) * ((γ σ * γ τ) * (γ σ * γ τ)⁻¹) := by
          rw [h']; ac_rfl
      _ = ε σ τ * (β₀ (σ * τ) * (γ (σ * τ))⁻¹) := by rw [mul_inv_cancel, mul_one]
  · rw [mul_pow, hβ₀, inv_pow, hγ, inv_one, mul_one]

/-- The coboundary of a square root of a character is a sign: if `β₀² = χ` with `χ`
multiplicative, then `(β₀ σ β₀ τ / β₀(στ))² = 1`. -/
theorem boundary_sq (χ : G →* U) (β₀ : G → U) (hβ₀ : ∀ σ, β₀ σ ^ 2 = χ σ) (σ τ : G) :
    (β₀ σ * β₀ τ * (β₀ (σ * τ))⁻¹) ^ 2 = 1 := by
  rw [mul_pow, mul_pow, inv_pow, hβ₀, hβ₀, hβ₀, map_mul, mul_inv_cancel]

end Basic

section Index

variable {G : Type*} [Group G] {E : Type*} [Field E]
variable {H : Subgroup G} {ε : G → G → Eˣ} {β : G → Eˣ}

/-- **B3, the degree bound** (N5 L711-714). If `β^n = 1` on `H` (`n = 2m`: `β² = χ` and
`χ^m = 1`), then `[H : K'] ≤ n`, because the image of `β|_H` lies in the `n`-th roots of unity
of a field. -/
theorem relindex_kernel_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (n : ℕ)
    (hn : 0 < n) (hpow : ∀ s ∈ H, β s ^ n = 1) : (restrictHom hβ hε).ker.index ≤ n := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have hrange : (restrictHom hβ hε).range ≤ rootsOfUnity n E := by
    rintro _ ⟨s, rfl⟩
    rw [mem_rootsOfUnity]
    exact hpow s s.2
  rw [Subgroup.index_ker]
  calc Nat.card (restrictHom hβ hε).range ≤ Nat.card (rootsOfUnity n E) :=
        Subgroup.card_le_of_le hrange
    _ ≤ n := card_rootsOfUnity E n

/-- **B3, `[L':ℚ] ≤ 2m d`** in group form: `[G : K'] ≤ n [G : H]`. -/
theorem index_kernel_le (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (n : ℕ)
    (hn : 0 < n) (hpow : ∀ s ∈ H, β s ^ n = 1) :
    (kernelSubgroup hβ hε).index ≤ n * H.index := by
  have h := relindex_kernel_le hβ hε n hn hpow
  have hrel : (kernelSubgroup hβ hε).relIndex H = (restrictHom hβ hε).ker.index := by
    rw [kernelSubgroup, Subgroup.relIndex]
    congr 1
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [← Subgroup.relIndex_mul_index (kernelSubgroup_le hβ hε), hrel]
  exact Nat.mul_le_mul_right _ h

end Index

section Inertia

variable {G : Type*} [Group G] {U : Type*} [CommGroup U]

/-- **B3, the twist kills inertia outside `T`** (N5 L702-709). `I v ≤ H` are the inertia groups
at the primes `v ∉ T` (contained in `G_L` since `L` is unramified there). On each, `β` is a
quadratic character (`β² = χ` and `χ` is unramified at `v`). `unique` is leaf L-B3a (at an
odd prime there is a unique nontrivial quadratic character of inertia), and `hηI` says that the
quadratic character `η` is ramified exactly where `β` is (leaf L-B3b for the Dirichlet
character of conductor `P`). Then `βη` is trivial on every `I v`. -/
theorem twist_kills_inertia {ι : Type*} (I : ι → Subgroup G) (β : G → U) (η : G →* U)
    (hmul : ∀ v, ∀ s ∈ I v, ∀ t ∈ I v, β (s * t) = β s * β t)
    (hquad : ∀ v, ∀ s ∈ I v, β s ^ 2 = 1) (hη2 : ∀ s, η s ^ 2 = 1)
    (unique : ∀ v, ∀ φ ψ : I v →* U, (∀ s, φ s ^ 2 = 1) → (∀ s, ψ s ^ 2 = 1) →
      φ ≠ 1 → ψ ≠ 1 → φ = ψ)
    (hηI : ∀ v, (∃ s ∈ I v, η s ≠ 1) ↔ (∃ s ∈ I v, β s ≠ 1)) :
    ∀ v, ∀ s ∈ I v, β s * η s = 1 := by
  intro v s hs
  by_cases hb : ∃ s ∈ I v, β s ≠ 1
  · let βv : I v →* U :=
      { toFun := fun t => β t
        map_one' := by
          have h := hmul v 1 (I v).one_mem 1 (I v).one_mem
          rw [one_mul] at h
          exact (mul_eq_left.mp h.symm)
        map_mul' := fun t u => hmul v t t.2 u u.2 }
    let ηv : I v →* U := η.comp (I v).subtype
    have hβne : βv ≠ 1 := by
      obtain ⟨t, ht, hne⟩ := hb
      intro h; apply hne; exact congrArg (fun f : I v →* U => f ⟨t, ht⟩) h
    have hηne : ηv ≠ 1 := by
      obtain ⟨t, ht, hne⟩ := (hηI v).mpr hb
      intro h; apply hne; exact congrArg (fun f : I v →* U => f ⟨t, ht⟩) h
    have heq := unique v βv ηv (fun t => hquad v t t.2) (fun t => hη2 t) hβne hηne
    have : β s = η s := congrArg (fun f : I v →* U => f ⟨s, hs⟩) heq
    rw [this, ← sq, hη2]
  · push_neg at hb
    have hη : ∀ s ∈ I v, η s = 1 := by
      by_contra h; push_neg at h
      obtain ⟨t, ht, hne⟩ := (hηI v).mp h
      exact hne (hb t ht)
    rw [hb s hs, hη s hs, one_mul]

/-- With `βη` trivial on `I v ≤ H`, the inertia group lies in `K' = ker(βη|_H)`:
`L'` is unramified at `v`. -/
theorem inertia_le_kernel {H : Subgroup G} {ε : G → G → U} {β : G → U}
    (hβ : IsCochainFor ε β) (hε : InflatedNormalized H ε) (Iv : Subgroup G) (hI : Iv ≤ H)
    (htriv : ∀ s ∈ Iv, β s = 1) : Iv ≤ kernelSubgroup hβ hε := fun s hs =>
  (mem_kernelSubgroup hβ hε).mpr ⟨hI hs, htriv s hs⟩

end Inertia

end GlueDescent

end DescCochainSec

section DescConstantsSec
/-! ### Copied from `scratch/glue-descent/Constants.lean` (compiled there). -/

/-!
# glue-descent: the constants of B2-B3 (N5 L674-677, L711-716)

Against the repository's own definitions (`ZInQKernel/Hypotheses/Height.lean`): `heightD = D`,
`heightE0 = E₀`, `heightQ R = Q_R = R^{R E₀}`, `contactSupport S u = M_S(u)`.

* `prod_odd_le`: `∏_{p ∈ T, p ≠ 2} (p - 1) ≤ R^R · M` for `T = S ∪ supp M`
  (N5 L676: `m ≤ 2 ∏_{p∈T, p≠2}(p-1) ≤ 2R^R M`);
* `degree_le_QM`: if `d ≤ D` and `m ≤ 2 ∏_{p ∈ T, p ≠ 2}(p-1)` then `2md ≤ Q_R · M`
  (N5 L713-716: `[L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM`).

The huge constants are never evaluated: only `1 ≤ D ≤ R`, `10¹² ≤ R` and `10 ≤ E₀` are used.
-/

namespace GlueDescent

open ZInQ

/-- `T = S ∪ supp M_S(u)`, the ramification set of `L` (N5 L528). -/
noncomputable def ramSet (S : Finset ℕ) (u : ℚ) : Finset ℕ :=
  S ∪ (contactSupport S u).primeFactors

theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem heightD_pos : 0 < heightD := by
  rw [ZInQ.Compiler.Precision.heightD_eq]
  exact Nat.mul_pos (Nat.factorial_pos 324) (by positivity)

theorem ten_le_heightE0 : 10 ≤ heightE0 := by
  rw [ZInQ.Compiler.Precision.heightE0_eq]
  have h1 : 0 < heightD * heightG0 := Nat.mul_pos heightD_pos (by unfold heightG0; norm_num)
  exact Nat.le_mul_of_pos_right 10 (pow_pos h1 2)

/-- `∏_{p ∈ S} (p - 1) ≤ R^R` when `S` consists of primes `≤ R` and `R ≥ 1`. -/
theorem prod_S_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) : ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) ≤ R ^ R := by
  have hcard : (S.card : ℝ) ≤ R := by
    have hsub : S ⊆ Finset.Icc 1 ⌊R⌋₊ := by
      intro p hp
      rw [Finset.mem_Icc]
      exact ⟨(hS p hp).one_lt.le, Nat.le_floor (hRS p hp)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    calc (S.card : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast this
      _ ≤ R := Nat.floor_le (by linarith)
  calc ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) = ∏ p ∈ S, (((p - 1 : ℕ)) : ℝ) := by push_cast [Nat.cast_prod]; rfl
    _ ≤ ∏ _p ∈ S, R := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro p hp
        have := hRS p hp
        have h1 : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
        linarith
    _ = R ^ S.card := Finset.prod_const R
    _ = R ^ (S.card : ℝ) := (Real.rpow_natCast R S.card).symm
    _ ≤ R ^ R := Real.rpow_le_rpow_of_exponent_le hR1 hcard

/-- Auxiliary form of `prod_odd_le` for an arbitrary positive `M`. -/
theorem prod_odd_le_aux (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (M : ℕ) (hM : 0 < M) :
    ((∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) ≤ R ^ R * M := by
  -- drop the filter: the factors are ≥ 1 on primes
  have hT : ∀ p ∈ S ∪ M.primeFactors, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  have h1 : (∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1)) ≤ ∏ p ∈ S ∪ M.primeFactors, (p - 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    intro p hp _
    have := (hT p hp).two_le
    omega
  -- union bound
  have h2 : (∏ p ∈ S ∪ M.primeFactors, (p - 1)) ≤
      (∏ p ∈ S, (p - 1)) * ∏ p ∈ M.primeFactors, (p - 1) := by
    rw [← Finset.prod_union_inter]
    apply Nat.le_mul_of_pos_right
    apply Finset.prod_pos
    intro p hp
    have := (hS p (Finset.mem_inter.mp hp).1).two_le
    omega
  have h3 : (∏ p ∈ M.primeFactors, (p - 1)) ≤ M :=
    calc (∏ p ∈ M.primeFactors, (p - 1)) ≤ ∏ p ∈ M.primeFactors, p :=
          Finset.prod_le_prod (fun p _ => Nat.sub_le p 1)
      _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)
  have hS' := prod_S_le S hS R hR1 hRS
  have hall : (∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1)) ≤
      (∏ p ∈ S, (p - 1)) * M := le_trans h1 (le_trans h2 (Nat.mul_le_mul_left _ h3))
  calc ((∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1) : ℕ) : ℝ)
      ≤ (((∏ p ∈ S, (p - 1)) * M : ℕ) : ℝ) := by exact_mod_cast hall
    _ = ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) * M := by push_cast; ring
    _ ≤ R ^ R * M := by
        apply mul_le_mul_of_nonneg_right hS' (by positivity)

/-- **B2's order bound, arithmetic part** (N5 L676): `∏_{p ∈ T, p ≠ 2} (p - 1) ≤ R^R · M`. -/
theorem prod_odd_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (u : ℚ) :
    ((∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) ≤ R ^ R * contactSupport S u :=
  prod_odd_le_aux S hS R hR1 hRS _ (contactSupport_pos S u)

/-- **B3, `[L':ℚ] ≤ QM`** (N5 L711-716). For an admissible `(S, R)` (the hypotheses of
`SixContactEstimate`), `d ≤ D` and `m ≤ 2 ∏_{p ∈ T, p ≠ 2}(p - 1)`, one has
`2 m d ≤ Q_R · M_S(u)`. -/
theorem degree_le_QM (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hRD : (heightD : ℝ) ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R) (u : ℚ) (d m : ℕ)
    (hd : d ≤ heightD) (hm : m ≤ 2 * ∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1)) :
    (2 * m * d : ℝ) ≤ heightQ R * contactSupport S u := by
  have hR4 : (4 : ℝ) ≤ R := le_trans (by norm_num) hR12
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hP := prod_odd_le S hS R hR1 hRS u
  have hM : (0 : ℝ) ≤ (contactSupport S u : ℝ) := Nat.cast_nonneg _
  generalize (contactSupport S u : ℝ) = M at hP hM ⊢
  have hm' : (m : ℝ) ≤ 2 * (R ^ R * M) := by
    have : (m : ℝ) ≤ 2 * ((∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast hm
    linarith
  have hd' : (d : ℝ) ≤ R := le_trans (by exact_mod_cast hd) hRD
  have hRR : (0 : ℝ) ≤ R ^ R := by positivity
  -- 2 m d ≤ 4 R^R M R ≤ R^R R^2 M = R^(R+2) M
  have step1 : (2 * m * d : ℝ) ≤ R ^ (R + 2) * M := by
    have hmd : (m : ℝ) * d ≤ 2 * (R ^ R * M) * R :=
      mul_le_mul hm' hd' (by positivity) (by positivity)
    rw [Real.rpow_add hR0, show (R ^ (2 : ℝ)) = R ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    have h4R : 4 * R ≤ R * R := mul_le_mul_of_nonneg_right hR4 hR0.le
    have hX : (0 : ℝ) ≤ R ^ R * M := mul_nonneg hRR hM
    calc (2 * m * d : ℝ) = 2 * ((m : ℝ) * d) := by ring
      _ ≤ 2 * (2 * (R ^ R * M) * R) := by linarith
      _ = (R ^ R * M) * (4 * R) := by ring
      _ ≤ (R ^ R * M) * (R * R) := mul_le_mul_of_nonneg_left h4R hX
      _ = R ^ R * R ^ 2 * M := by ring
  -- R + 2 ≤ R E₀
  have hE : (10 : ℝ) ≤ heightE0 := by exact_mod_cast ten_le_heightE0
  have step2 : R ^ (R + 2) ≤ heightQ R := by
    unfold heightQ
    apply Real.rpow_le_rpow_of_exponent_le hR1
    generalize (heightE0 : ℝ) = E at hE ⊢
    have : R * 10 ≤ R * E := mul_le_mul_of_nonneg_left hE hR0.le
    linarith
  calc (2 * m * d : ℝ) ≤ R ^ (R + 2) * M := step1
    _ ≤ heightQ R * M := mul_le_mul_of_nonneg_right step2 hM

end GlueDescent

end DescConstantsSec

section DescChiSec
/-! ### Copied from `scratch/glue-descent/Chi.lean` (compiled there). -/

/-!
# glue-descent: the Dirichlet character `χ` of B2 (N5 L671-677)

N5 takes `T₋` to be the finite primes where the invariant of `[ε]` is `1/2`, picks an odd
character of `(ℤ/p)^×` at each odd `p ∈ T₋` and the nontrivial character mod `4` if `2 ∈ T₋`,
multiplies them to `χ`, and bounds the order `m ≤ 2 ∏_{p∈T, p≠2}(p-1)` (paraphrase).

Proved here over Mathlib's `DirichletCharacter` (genuine definitions), for any finite set `T`
of primes and any subset `T₋ ⊆ T`:

* `exists_odd_char`: for `n > 2` there is a Dirichlet character mod `n` with `χ(-1) = -1`
  (at `n = 4` it is the nontrivial character mod four);
* `exists_chi`: the product `χ = ∏_{p ∈ T₋} χ_p` (each `χ_p` odd of level `p`, or `4` at `p = 2`,
  raised to the level `N = ∏_{p ∈ T₋} lev p`) has level supported in `T` and
  `orderOf χ ≤ 2 ∏_{p ∈ T, p ≠ 2} (p - 1)`.

Not here: that the local invariant of `δχ` at `p` is `1/2` exactly when `χ_p(-1) = -1` (local
class field theory; leaf L-B2c of `docs/research/glue-descent.md`).
-/

namespace GlueDescent

open scoped Nat

/-- The local level: `4` at `p = 2`, `p` at odd `p`. -/
def lev (p : ℕ) : ℕ := if p = 2 then 4 else p

theorem two_lt_lev {p : ℕ} (hp : p.Prime) : 2 < lev p := by
  unfold lev
  split_ifs with h
  · norm_num
  · have := hp.two_le; omega

theorem totient_lev {p : ℕ} (hp : p.Prime) : φ (lev p) = if p = 2 then 2 else p - 1 := by
  unfold lev
  split_ifs with h
  · decide
  · exact Nat.totient_prime hp

/-- For `n > 2` there is a Dirichlet character mod `n` that is odd: `χ(-1) = -1`. -/
theorem exists_odd_char (n : ℕ) (hn : 2 < n) : ∃ χ : DirichletCharacter ℂ n, χ (-1) = -1 := by
  haveI : Fact (2 < n) := ⟨hn⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero ((Monoid.exponent (ZMod n)ˣ : ℕ) : ℂ) :=
    ⟨by exact_mod_cast (Monoid.exponent_ne_zero_of_finite (G := (ZMod n)ˣ))⟩
  obtain ⟨χ, hχ⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod n) ℂ (ZMod.neg_one_ne_one (n := n))
  refine ⟨χ, ?_⟩
  have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · exact absurd h hχ
  · exact h

/-- The order of a Dirichlet character mod `n` divides `φ(n)`. -/
theorem orderOf_dvd_totient {n : ℕ} (χ : DirichletCharacter ℂ n) : orderOf χ ∣ φ n := by
  apply orderOf_dvd_of_pow_eq_one
  apply MulChar.ext
  intro a
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val,
    ZMod.pow_totient, Units.val_one, map_one]

/-- In a commutative monoid, the order of a finite product divides the product of the orders. -/
theorem orderOf_prod_dvd {M ι : Type*} [CommMonoid M] (s : Finset ι) (x : ι → M) :
    orderOf (∏ i ∈ s, x i) ∣ ∏ i ∈ s, orderOf (x i) := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun i => orderOf (x i)) hi
  rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]

/-- The chosen odd character of level `lev p`. -/
noncomputable def oddChar (p : ℕ) : DirichletCharacter ℂ (lev p) :=
  if h : 2 < lev p then Classical.choose (exists_odd_char _ h) else 1

theorem oddChar_neg_one {p : ℕ} (hp : p.Prime) : oddChar p (-1) = -1 := by
  unfold oddChar
  rw [dif_pos (two_lt_lev hp)]
  exact Classical.choose_spec (exists_odd_char _ (two_lt_lev hp))

/-- The level `N = ∏_{p ∈ T₋} lev p` of `χ`. -/
def chiLevel (Tm : Finset ℕ) : ℕ := ∏ p ∈ Tm, lev p

theorem lev_dvd_chiLevel {Tm : Finset ℕ} {p : ℕ} (hp : p ∈ Tm) : lev p ∣ chiLevel Tm :=
  Finset.dvd_prod_of_mem lev hp

/-- `χ = ∏_{p ∈ T₋} χ_p`, raised to level `N`. -/
noncomputable def chi (Tm : Finset ℕ) : DirichletCharacter ℂ (chiLevel Tm) :=
  ∏ p ∈ Tm.attach, DirichletCharacter.changeLevel (lev_dvd_chiLevel p.2) (oddChar p.1)

/-- The arithmetic of the order bound: `∏_{p ∈ T₋} φ(lev p) ≤ 2 ∏_{p ∈ T, p ≠ 2} (p - 1)`. -/
theorem prod_totient_lev_le (T Tm : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (hTm : Tm ⊆ T) :
    ∏ p ∈ Tm, φ (lev p) ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
  rw [Finset.prod_congr rfl (fun p hp => totient_lev (hT p (hTm hp))),
    ← Finset.prod_filter_mul_prod_filter_not Tm (· = 2)]
  apply Nat.mul_le_mul
  · -- the factor at 2 is at most 2
    have hsub : Tm.filter (· = 2) ⊆ {2} := by
      intro p hp; rw [Finset.mem_filter] at hp; simp [hp.2]
    calc ∏ p ∈ Tm.filter (· = 2), (if p = 2 then 2 else p - 1)
        = ∏ p ∈ Tm.filter (· = 2), 2 :=
          Finset.prod_congr rfl (fun p hp => by rw [if_pos (Finset.mem_filter.mp hp).2])
      _ ≤ ∏ p ∈ ({2} : Finset ℕ), 2 :=
          Finset.prod_le_prod_of_subset_of_one_le hsub (fun _ _ _ => by norm_num)
      _ = 2 := by simp
  · calc ∏ p ∈ Tm.filter (fun p => ¬ p = 2), (if p = 2 then 2 else p - 1)
        = ∏ p ∈ Tm.filter (fun p => ¬ p = 2), (p - 1) :=
          Finset.prod_congr rfl (fun p hp => by rw [if_neg (Finset.mem_filter.mp hp).2])
      _ ≤ ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
          apply Finset.prod_le_prod_of_subset_of_one_le
          · intro p hp
            rw [Finset.mem_filter] at hp ⊢
            exact ⟨hTm hp.1, hp.2⟩
          · intro p hp _
            have := (hT p (Finset.mem_filter.mp hp).1).two_le
            omega

/-- **B2, the character `χ`** (N5 L671-677). For a finite set `T` of primes and `T₋ ⊆ T`,
the character `χ = ∏_{p ∈ T₋} χ_p` with each `χ_p` odd of level `lev p` has level divisible
only by primes of `T`, and order at most `2 ∏_{p ∈ T, p ≠ 2} (p - 1)`. -/
theorem exists_chi (T Tm : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) (hTm : Tm ⊆ T) :
    (∀ p ∈ Tm, oddChar p (-1) = -1) ∧
    (∀ q : ℕ, q.Prime → q ∣ chiLevel Tm → q ∈ T) ∧
    orderOf (chi Tm) ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) := by
  refine ⟨fun p hp => oddChar_neg_one (hT p (hTm hp)), ?_, ?_⟩
  · intro q hq hdvd
    obtain ⟨p, hp, hqp⟩ := (Prime.dvd_finsetProd_iff hq.prime _).mp hdvd
    have hpT := hT p (hTm hp)
    unfold lev at hqp
    split_ifs at hqp with h2
    · subst h2
      have : q ∣ 2 := hq.prime.dvd_of_dvd_pow (show q ∣ 2 ^ 2 by norm_num at hqp ⊢; exact hqp)
      rw [(Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp this]
      exact hTm hp
    · rw [(Nat.prime_dvd_prime_iff_eq hq hpT).mp hqp]
      exact hTm hp
  · have hpos : 0 < ∏ p ∈ Tm, φ (lev p) := by
      apply Finset.prod_pos
      intro p hp
      exact Nat.totient_pos.mpr (by have := two_lt_lev (hT p (hTm hp)); omega)
    calc orderOf (chi Tm) ≤ ∏ p ∈ Tm, φ (lev p) := by
          apply Nat.le_of_dvd hpos
          refine (orderOf_prod_dvd _ _).trans ?_
          rw [← Finset.prod_attach Tm (fun p => φ (lev p))]
          apply Finset.prod_dvd_prod_of_dvd
          intro p _
          exact (orderOf_map_dvd _ _).trans (orderOf_dvd_totient _)
      _ ≤ _ := prod_totient_lev_le T Tm hT hTm

end GlueDescent


end DescChiSec

section DescB2GlueSec
/-! ### Copied from `scratch/glue-descent/B2Glue.lean` (compiled there). -/

/-!
# glue-descent: the deduction of B2 from its literature inputs (N5 L665-700)

An abstract but universally quantified form: `G` is any topological group (for the application,
`G_ℚ` with the Krull topology), `ι` any index type (the finite primes), `Gv v` any topological
groups with continuous homomorphisms `r v : Gv v →* G` (the decomposition groups
`G_{ℚ_p} → G_ℚ` along a chosen embedding `ℚ̄ → ℚ̄_p`), and `U` any commutative group (`ℂ^×`).
"Continuous with values in a discrete group" is `IsLocallyConstant`.

A sign 2-cocycle `η` is *trivial* (`SignCob`) if `η = dγ` for a locally constant sign cochain
`γ`. The hypotheses are exactly the inputs of N5's argument:

* `hasse` (leaf L-B2a): a locally constant sign 2-cocycle on `G` that is trivial at every finite
  place is trivial (injectivity of `H²(G_ℚ, ±1) → ∏_{p<∞} H²(G_{ℚ_p}, ±1)`: Kummer theory
  with Hilbert 90, Albert–Brauer–Hasse–Noether and reciprocity, with `Br(ℝ)[2] = ℤ/2`);
* `local_two` (leaf L-B2b): `H²(G_{ℚ_p}, ±1)` has at most two elements (`Br(ℚ_p)[2] = ℤ/2`);
* `agree` (the local analysis of B2, leaves L-B2c, L-B2d): at every finite place, `[ε]` and
  `δχ = [dβ₀]` are both trivial or both nontrivial.

Conclusion: a locally constant `β` with `β² = χ` and `β σ β τ = ε(σ,τ) β(στ)`.
-/

namespace GlueDescent.B2

variable {U : Type*} [CommGroup U]

/-- `d β (σ, τ) = β σ β τ / β (στ)`. -/
def dB {Γ : Type*} [Mul Γ] (β : Γ → U) (x y : Γ) : U := β x * β y * (β (x * y))⁻¹

/-- `η` is a locally constant sign 2-cocycle (trivial action). -/
def IsSignCocycle {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] (η : Γ → Γ → U) : Prop :=
  IsLocallyConstant (Function.uncurry η) ∧ (∀ x y, η x y ^ 2 = 1) ∧
    ∀ x y z, η (x * y) z * η x y = η y z * η x (y * z)

/-- `η` is the coboundary of a locally constant sign cochain. -/
def SignCob {Γ : Type*} [Mul Γ] [TopologicalSpace Γ] (η : Γ → Γ → U) : Prop :=
  ∃ γ : Γ → U, IsLocallyConstant γ ∧ (∀ x, γ x ^ 2 = 1) ∧ ∀ x y, η x y = dB γ x y

section Pullback

variable {Γ Δ : Type*} [Group Γ] [Group Δ] [TopologicalSpace Γ] [TopologicalSpace Δ]

/-- Pull back a 2-cochain along a homomorphism. -/
def pull (r : Δ →* Γ) (η : Γ → Γ → U) : Δ → Δ → U := fun x y => η (r x) (r y)

theorem pull_dB (r : Δ →* Γ) (β : Γ → U) : pull r (dB β) = dB (β ∘ r) := by
  funext x y; simp [pull, dB, map_mul]

theorem isSignCocycle_pull (r : Δ →* Γ) (hr : Continuous r) {η : Γ → Γ → U}
    (hη : IsSignCocycle η) : IsSignCocycle (pull r η) := by
  refine ⟨?_, fun x y => hη.2.1 _ _, fun x y z => by simp only [pull, map_mul]; exact hη.2.2 _ _ _⟩
  have : Function.uncurry (pull r η) = Function.uncurry η ∘ (Prod.map r r) := by
    funext ⟨x, y⟩; rfl
  rw [this]
  exact hη.1.comp_continuous (hr.prodMap hr)

end Pullback

section Algebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

theorem dB_mul (β γ : Γ → U) : dB (fun x => β x * γ x) = fun x y => dB β x y * dB γ x y := by
  funext x y; simp only [dB, mul_inv]; ac_rfl

theorem dB_inv (γ : Γ → U) : dB (fun x => (γ x)⁻¹) = fun x y => (dB γ x y)⁻¹ := by
  funext x y; simp only [dB, mul_inv, inv_inv]

theorem signCob_mul {η₁ η₂ : Γ → Γ → U} (h₁ : SignCob η₁) (h₂ : SignCob η₂) :
    SignCob (fun x y => η₁ x y * η₂ x y) := by
  obtain ⟨γ₁, hl₁, hs₁, he₁⟩ := h₁
  obtain ⟨γ₂, hl₂, hs₂, he₂⟩ := h₂
  refine ⟨fun x => γ₁ x * γ₂ x, hl₁.mul hl₂, fun x => by rw [mul_pow, hs₁, hs₂, mul_one], ?_⟩
  intro x y
  show η₁ x y * η₂ x y = _
  rw [he₁, he₂, dB_mul]

theorem signCob_inv {η : Γ → Γ → U} (h : SignCob η) : SignCob (fun x y => (η x y)⁻¹) := by
  obtain ⟨γ, hl, hs, he⟩ := h
  refine ⟨fun x => (γ x)⁻¹, hl.inv, fun x => by rw [inv_pow, hs, inv_one], ?_⟩
  intro x y
  show (η x y)⁻¹ = _
  rw [he, dB_inv]

theorem isSignCocycle_mul {η₁ η₂ : Γ → Γ → U} (h₁ : IsSignCocycle η₁) (h₂ : IsSignCocycle η₂) :
    IsSignCocycle (fun x y => η₁ x y * η₂ x y) := by
  refine ⟨?_, fun x y => by rw [mul_pow, h₁.2.1, h₂.2.1, mul_one], fun x y z => ?_⟩
  · have : Function.uncurry (fun x y => η₁ x y * η₂ x y) =
        Function.uncurry η₁ * Function.uncurry η₂ := by funext ⟨x, y⟩; rfl
    rw [this]; exact h₁.1.mul h₂.1
  · have e1 := h₁.2.2 x y z
    have e2 := h₂.2.2 x y z
    show η₁ (x * y) z * η₂ (x * y) z * (η₁ x y * η₂ x y) =
      η₁ y z * η₂ y z * (η₁ x (y * z) * η₂ x (y * z))
    calc η₁ (x * y) z * η₂ (x * y) z * (η₁ x y * η₂ x y)
        = (η₁ (x * y) z * η₁ x y) * (η₂ (x * y) z * η₂ x y) := by ac_rfl
      _ = (η₁ y z * η₁ x (y * z)) * (η₂ y z * η₂ x (y * z)) := by rw [e1, e2]
      _ = _ := by ac_rfl

theorem isSignCocycle_inv {η : Γ → Γ → U} (h : IsSignCocycle η) :
    IsSignCocycle (fun x y => (η x y)⁻¹) := by
  refine ⟨?_, fun x y => by rw [inv_pow, h.2.1, inv_one], fun x y z => ?_⟩
  · have : Function.uncurry (fun x y => (η x y)⁻¹) = (Function.uncurry η)⁻¹ := by
      funext ⟨x, y⟩; rfl
    rw [this]; exact h.1.inv
  · show (η (x * y) z)⁻¹ * (η x y)⁻¹ = (η y z)⁻¹ * (η x (y * z))⁻¹
    rw [← mul_inv, ← mul_inv, h.2.2 x y z]

/-- The coboundary of a locally constant pointwise square root of a locally constant
character is a sign 2-cocycle. -/
theorem isSignCocycle_dB [IsTopologicalGroup Γ] (χ : Γ →* U) (β₀ : Γ → U)
    (hβ₀ : ∀ x, β₀ x ^ 2 = χ x) (hl : IsLocallyConstant β₀) : IsSignCocycle (dB β₀) := by
  refine ⟨?_, fun x y => ?_, fun x y z => ?_⟩
  · have hm : Continuous (fun p : Γ × Γ => p.1 * p.2) := continuous_mul
    have h1 : IsLocallyConstant (fun p : Γ × Γ => β₀ p.1) := hl.comp_continuous continuous_fst
    have h2 : IsLocallyConstant (fun p : Γ × Γ => β₀ p.2) := hl.comp_continuous continuous_snd
    have h3 : IsLocallyConstant (fun p : Γ × Γ => (β₀ (p.1 * p.2))⁻¹) :=
      (hl.comp_continuous hm).inv
    have : Function.uncurry (dB β₀) = ((fun p : Γ × Γ => β₀ p.1) * fun p => β₀ p.2) *
        fun p => (β₀ (p.1 * p.2))⁻¹ := by funext ⟨x, y⟩; rfl
    rw [this]; exact (h1.mul h2).mul h3
  · simp only [dB, mul_pow, inv_pow, hβ₀, map_mul, mul_inv_cancel]
  · simp only [dB]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, mul_assoc]
    abel

end Algebra

/-- **B2, the deduction** (N5 L665-700). See the module docstring for the hypotheses. -/
theorem exists_beta {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {ι : Type*} (Gv : ι → Type*) [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
    (r : ∀ v, Gv v →* G) (hr : ∀ v, Continuous (r v))
    (hasse : ∀ η : G → G → U, IsSignCocycle η → (∀ v, SignCob (pull (r v) η)) → SignCob η)
    (local_two : ∀ v, ∀ η₁ η₂ : Gv v → Gv v → U, IsSignCocycle η₁ → IsSignCocycle η₂ →
      ¬ SignCob η₁ → ¬ SignCob η₂ → SignCob (fun x y => η₁ x y * (η₂ x y)⁻¹))
    (ε : G → G → U) (hε : IsSignCocycle ε)
    (χ : G →* U) (β₀ : G → U) (hβ₀ : ∀ x, β₀ x ^ 2 = χ x) (hl : IsLocallyConstant β₀)
    (agree : ∀ v, SignCob (pull (r v) ε) ↔ SignCob (pull (r v) (dB β₀))) :
    ∃ β : G → U, IsLocallyConstant β ∧ (∀ x, β x ^ 2 = χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  have hd : IsSignCocycle (dB β₀) := isSignCocycle_dB χ β₀ hβ₀ hl
  -- η = ε · (dβ₀)⁻¹
  set η : G → G → U := fun x y => ε x y * (dB β₀ x y)⁻¹ with hηdef
  have hη : IsSignCocycle η := isSignCocycle_mul hε (isSignCocycle_inv hd)
  have hloc : ∀ v, SignCob (pull (r v) η) := by
    intro v
    have hpε := isSignCocycle_pull (r v) (hr v) hε
    have hpd := isSignCocycle_pull (r v) (hr v) hd
    have e : pull (r v) η = fun x y => pull (r v) ε x y * (pull (r v) (dB β₀) x y)⁻¹ := rfl
    rw [e]
    by_cases h : SignCob (pull (r v) ε)
    · exact signCob_mul h (signCob_inv ((agree v).mp h))
    · exact local_two v _ _ hpε hpd h (fun h' => h ((agree v).mpr h'))
  obtain ⟨γ, hγl, hγs, hγe⟩ := hasse η hη hloc
  -- β = β₀ γ
  refine ⟨fun x => β₀ x * γ x, hl.mul hγl, fun x => by rw [mul_pow, hβ₀, hγs, mul_one], ?_⟩
  intro x y
  have hxy := hγe x y
  simp only [hηdef, dB] at hxy
  -- from ε · (dβ₀)⁻¹ = dγ:  β₀x γx β₀y γy = ε (β₀ (xy) γ (xy))
  have key : ε x y = (β₀ x * β₀ y * (β₀ (x * y))⁻¹) * (γ x * γ y * (γ (x * y))⁻¹) := by
    rw [← hxy]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  show β₀ x * γ x * (β₀ y * γ y) = ε x y * (β₀ (x * y) * γ (x * y))
  rw [key]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel


/-- **B2, the cohomological form of the square-root criterion** (N5 L680-683, the exact sequence
`1 → ±1 → μ_∞ → μ_∞ → 1`). For a character `ψ` with a locally constant pointwise square root
`β₀`, the boundary `δψ = [dβ₀]` is trivial iff `ψ` has a locally constant square-root
character. (Which characters of `G_{ℚ_p}` have square roots is local class field theory:
leaf L-B2c.) -/
theorem signCob_dB_iff {Γ : Type*} [Group Γ] [TopologicalSpace Γ] (ψ : Γ →* U) (β₀ : Γ → U)
    (hβ₀ : ∀ x, β₀ x ^ 2 = ψ x) (hl : IsLocallyConstant β₀) :
    SignCob (dB β₀) ↔ ∃ φ : Γ →* U, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = ψ x := by
  constructor
  · rintro ⟨γ, hγl, hγs, hγe⟩
    refine ⟨{ toFun := fun x => β₀ x * (γ x)⁻¹, map_one' := ?_, map_mul' := ?_ },
      hl.mul hγl.inv, fun x => ?_⟩
    · have h := hγe 1 1
      simp only [dB, one_mul] at h
      have h' : β₀ 1 * (γ 1)⁻¹ * (β₀ 1 * (γ 1)⁻¹) = β₀ 1 * (γ 1)⁻¹ := by
        have : β₀ 1 * β₀ 1 * (β₀ 1)⁻¹ * (γ 1 * γ 1 * (γ 1)⁻¹)⁻¹ = 1 := by
          rw [h, mul_inv_cancel]
        apply Additive.ofMul.injective
        have := congrArg Additive.ofMul this
        simp only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢
        rw [← sub_eq_zero]; rw [← this]; abel
      exact mul_eq_left.mp h'
    · intro x y
      have h := hγe x y
      simp only [dB] at h
      have : β₀ x * β₀ y * (β₀ (x * y))⁻¹ * (γ x * γ y * (γ (x * y))⁻¹)⁻¹ = 1 := by
        rw [h, mul_inv_cancel]
      show β₀ (x * y) * (γ (x * y))⁻¹ = β₀ x * (γ x)⁻¹ * (β₀ y * (γ y)⁻¹)
      apply Additive.ofMul.injective
      have := congrArg Additive.ofMul this
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at this ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← this]; abel
    · show (β₀ x * (γ x)⁻¹) ^ 2 = ψ x
      rw [mul_pow, hβ₀, inv_pow, hγs, inv_one, mul_one]
  · rintro ⟨φ, hφl, hφs⟩
    refine ⟨fun x => β₀ x * (φ x)⁻¹, hl.mul hφl.inv, fun x => ?_, fun x y => ?_⟩
    · rw [mul_pow, hβ₀, inv_pow, hφs, mul_inv_cancel]
    · simp only [dB, map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel

end GlueDescent.B2

/-!
## The leaves of B2 over genuine Mathlib objects

`G_ℚ = Field.absoluteGaloisGroup ℚ` and `G_{ℚ_p} = Field.absoluteGaloisGroup ℚ_[p]` with their
Krull topologies; `resp p : G_{ℚ_p} →* G_ℚ` is Mathlib's `absoluteGaloisGroup.map` along
`ℚ → ℚ_p` (it depends on a choice of embedding `ℚ̄ → ℚ̄_p`; the vanishing of a class does not).
Sign-valued cochains are `ℂ^×`-valued with square `1`. `cyc N : G_ℚ →* (ℤ/N)^×` is Mathlib's
`modularCyclotomicCharacter` on `ℚ̄`.
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

/-- `G_ℚ`. -/
abbrev GQ := Field.absoluteGaloisGroup ℚ

instance : IsTopologicalGroup GQ :=
  inferInstanceAs (IsTopologicalGroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- `G_{ℚ_p}`. -/
abbrev GQp (p : Nat.Primes) := Field.absoluteGaloisGroup ℚ_[p]

/-- The decomposition-group map `G_{ℚ_p} → G_ℚ`. -/
noncomputable def resp (p : Nat.Primes) : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).toMonoidHom

theorem resp_continuous (p : Nat.Primes) : Continuous (resp p) :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

/-- The forgetful map `Gal(ℚ̄/ℚ) → Aut(ℚ̄)` as a monoid homomorphism. -/
noncomputable def toRingAut : GQ →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The cyclotomic character `G_ℚ → (ℤ/N)^×`. -/
noncomputable def cyc (N : ℕ) [NeZero N] : GQ →* (ZMod N)ˣ :=
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  (modularCyclotomicCharacter (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)).comp toRingAut

/-- A Dirichlet character as a character of `G_ℚ`. -/
noncomputable def galChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : GQ →* ℂˣ :=
  χ.toUnitHom.comp (cyc N)

/-- **Leaf L-B2a** (Hasse principle for `H²(G_ℚ, ±1)` at the finite places). A continuous sign
2-cocycle of `G_ℚ` whose restriction to every `G_{ℚ_p}` is a coboundary is a coboundary.
Consequence of: `H²(G_K, μ₂) = Br(K)[2]` (Kummer theory, Hilbert 90), the
Albert–Brauer–Hasse–Noether theorem `Br(ℚ) ↪ ⊕_v Br(ℚ_v)` with `∑_v inv_v = 0`, and
`Br(ℝ) = ℤ/2` (so a class trivial at all finite places is trivial at `∞`). -/
def LeafHasse : Prop :=
  ∀ η : GQ → GQ → ℂˣ, IsSignCocycle η →
    (∀ p : Nat.Primes, SignCob (pull (resp p) η)) → SignCob η

/-- **Leaf L-B2b** (`H²(G_{ℚ_p}, ±1)` has at most two elements). Consequence of
`H²(G_{ℚ_p}, μ₂) = Br(ℚ_p)[2] ≅ ℤ/2` (local class field theory). -/
def LeafLocalTwo : Prop :=
  ∀ p : Nat.Primes, ∀ η₁ η₂ : GQp p → GQp p → ℂˣ, IsSignCocycle η₁ → IsSignCocycle η₂ →
    ¬ SignCob η₁ → ¬ SignCob η₂ → SignCob (fun x y => η₁ x y * (η₂ x y)⁻¹)

/-- **Leaf L-B2c** (explicit local square-root criterion for Dirichlet characters). For a
Dirichlet character `χ` mod `N` and a prime `p` with `N = p^k N'`, `p ∤ N'`, let `u ∈ (ℤ/N)^×`
be `≡ -1 mod p^k` and `≡ 1 mod N'`. Then `χ|_{G_{ℚ_p}}` has a continuous square-root
character iff `χ(u) = 1`. Consequence of local class field theory for `ℚ_p` with its explicit
(Lubin–Tate / cyclotomic) reciprocity law — the local Artin map sends `-1 ∈ ℤ_p^×` to an element
acting on `μ_N` through `u^{±1} = u` — together with the structure of `ℚ_p^×` (N5 L683-689: a
finite-order character of `ℚ_p^×` has a square root iff its value at `-1` is `1`). -/
def LeafSqrtCrit : Prop :=
  ∀ (p : Nat.Primes) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ),
    ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1 →
    ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1 →
    ((∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1)

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def act (σ : GQ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ

/-- `ε : G_ℚ × G_ℚ → ℂ^×` is inflated from `Gal(L/ℚ)`. -/
def InflatedFrom (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (ε : GQ → GQ → ℂˣ) : Prop :=
  ∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) → ε σ τ = ε σ' τ'

/-- `L` is unramified at `p`: every prime of `𝓞 L` above `p` has ramification index `1`. -/
def UnramifiedAt (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → ((p : ℤ) : 𝓞 L) ∈ P →
    P.ramificationIdx ℤ = 1

/-- **Leaf L-B2d** (unramified classes vanish locally). If `ε` is inflated from `Gal(L/ℚ)` for
a finite Galois `L` unramified at `p`, its restriction to `G_{ℚ_p}` is a coboundary.
Consequence of: the restriction is inflated from `Gal(ℚ_p^{ur}/ℚ_p) ≅ ℤ̂`, and
`H²(ℤ̂, ℤ/2) = 0` (`cd ℤ̂ = 1`). -/
def LeafUnramified : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
    ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)

end GlueDescent.B2Q

/-!
## Toward the assembly of B2 over `G_ℚ`: continuity of the cyclotomic character
-/

namespace GlueDescent.B2Q

open GlueDescent.B2 NumberField

/-- A function on a topological group that is invariant under right translation by an open
subgroup is locally constant. -/
theorem isLocallyConstant_of_openSubgroup {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) (f : G → X)
    (hf : ∀ g, ∀ k ∈ U, f (g * k) = f g) : IsLocallyConstant f := by
  refine IsLocallyConstant.iff_isOpen_fiber.2 fun y => isOpen_iff_forall_mem_open.2 fun x hx =>
    ⟨(x * ·) '' U, ?_, isOpenMap_mul_left x _ hU, ⟨1, U.one_mem, mul_one x⟩⟩
  rintro _ ⟨k, hk, rfl⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
  rw [hf x k hk, hx]

theorem act_mul (σ τ : GQ) (x : AlgebraicClosure ℚ) : act (σ * τ) x = act σ (act τ x) := rfl

/-- `cyc N σ` depends only on the action of `σ` on the `N`-th roots of unity. -/
theorem cyc_eq_of_agree (N : ℕ) [NeZero N] (σ τ : GQ)
    (h : ∀ t ∈ rootsOfUnity N (AlgebraicClosure ℚ),
      act σ (t : AlgebraicClosure ℚ) = act τ (t : AlgebraicClosure ℚ)) :
    cyc N σ = cyc N τ := by
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N
  apply Units.ext
  show ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut σ) : (ZMod N)ˣ) : ZMod N) =
    ((modularCyclotomicCharacter (AlgebraicClosure ℚ) hn (toRingAut τ) : (ZMod N)ˣ) : ZMod N)
  apply modularCyclotomicCharacter.unique _ hn
  intro t ht
  rw [← modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn (toRingAut σ) ht]
  exact (h t ht).symm

/-- **The cyclotomic character is continuous** (locally constant): it is invariant under the
open subgroup fixing `ℚ(μ_N)`. -/
theorem cyc_isLocallyConstant (N : ℕ) [NeZero N] : IsLocallyConstant (cyc N) := by
  let S : Set (AlgebraicClosure ℚ) :=
    (fun t : (AlgebraicClosure ℚ)ˣ => (t : AlgebraicClosure ℚ)) ''
      (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ)
  have hfin : Finite (rootsOfUnity N (AlgebraicClosure ℚ) : Set (AlgebraicClosure ℚ)ˣ) :=
    (inferInstance : Finite (rootsOfUnity N (AlgebraicClosure ℚ)))
  haveI : Finite S := ((Set.toFinite _).image _).to_subtype
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ S
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  refine isLocallyConstant_of_openSubgroup (G := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    K.fixingSubgroup K.fixingSubgroup_isOpen (fun g => cyc N g) ?_
  intro g k hk
  apply cyc_eq_of_agree
  intro t ht
  have hfix : act k (t : AlgebraicClosure ℚ) = t :=
    (IntermediateField.mem_fixingSubgroup_iff K k).mp hk _
      (IntermediateField.subset_adjoin ℚ S ⟨t, ht, rfl⟩)
  show g (k (t : AlgebraicClosure ℚ)) = g (t : AlgebraicClosure ℚ)
  exact congrArg g hfix

theorem galChar_isLocallyConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsLocallyConstant (galChar χ) :=
  show IsLocallyConstant (χ.toUnitHom ∘ cyc N) from (cyc_isLocallyConstant N).comp _

/-- A square-root choice function on `ℂ^×`. -/
noncomputable def sqrtU (z : ℂˣ) : ℂˣ :=
  have h : ∃ w : ℂ, w ^ 2 = z := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (by norm_num)
  Units.mk0 (Classical.choose h) (by
    intro h0
    have := Classical.choose_spec h
    rw [h0] at this
    exact z.ne_zero (by rw [← this]; ring))

theorem sqrtU_sq (z : ℂˣ) : sqrtU z ^ 2 = z := by
  apply Units.ext
  simp only [sqrtU, Units.val_pow_eq_pow_val, Units.val_mk0]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (z : ℂ) (by norm_num : 0 < 2))

end GlueDescent.B2Q

end DescB2GlueSec

section DescB2AssemblySec
/-! ### Copied from `scratch/glue-descent/B2Assembly.lean` (compiled there). -/

/-!
# glue-descent: B2 over `G_ℚ` from the four leaves L-B2a..d (N5 L665-700)

`b2_of_leaves`: for a finite Galois `L ⊂ ℚ̄` unramified outside a finite set `T` of primes, and
a continuous sign 2-cocycle `ε` of `G_ℚ` inflated from `Gal(L/ℚ)`, the four leaves give a set
`T₋ ⊆ T`, the Dirichlet character `χ = ∏_{p ∈ T₋} χ_p` of `Chi.lean` (level supported in `T`,
order `≤ 2 ∏_{p∈T, p≠2}(p-1)`), and a continuous `β : G_ℚ → ℂ^×` with `β² = χ` and
`dβ = ε`. Everything is over Mathlib's genuine objects (`Field.absoluteGaloisGroup`, `ℚ_[p]`,
`modularCyclotomicCharacter`, `DirichletCharacter`, `𝓞 L`).

Compile (out of tree, one file at a time; `OUT = scratch/glue-descent/.lake/out`):
`lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean -o $OUT/GlueDescent/Chi.olean scratch/glue-descent/Chi.lean"`,
the same for `B2Glue`, then `lake env bash -c "LEAN_PATH=$OUT:\$LEAN_PATH lean scratch/glue-descent/B2Assembly.lean"`.
-/

namespace GlueDescent.B2Q

open GlueDescent GlueDescent.B2 NumberField

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

theorem chiLevel_pos (Tm : Finset ℕ) (h : ∀ p ∈ Tm, p.Prime) : 0 < chiLevel Tm :=
  Finset.prod_pos (fun p hp => by have := two_lt_lev (h p hp); omega)

/-- The unit `u ∈ (ℤ/N)^×` with `u ≡ -1 mod p^k`, `u ≡ 1 mod N'` (`N = p^k N'`). -/
theorem exists_crt_unit (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime) :
    ∃ u : (ZMod N)ˣ, ((u : ZMod N).cast : ZMod (p ^ N.factorization p)) = -1 ∧
      ((u : ZMod N).cast : ZMod (N / p ^ N.factorization p)) = 1 := by
  have hN : p ^ N.factorization p * (N / p ^ N.factorization p) = N :=
    Nat.ordProj_mul_ordCompl_eq_self N p
  have hcop : Nat.Coprime (p ^ N.factorization p) (N / p ^ N.factorization p) :=
    (Nat.coprime_ordCompl hp (NeZero.ne N)).pow_left _
  generalize N.factorization p = k at hN hcop ⊢
  generalize N / p ^ k = N' at hN hcop ⊢
  let e := ZMod.chineseRemainder hcop
  let φ : ZMod (p ^ k * N') →+* ZMod N := ZMod.castHom (dvd_of_eq hN.symm) (ZMod N)
  have h1 : ∀ z, (((φ z : ZMod N)).cast : ZMod (p ^ k)) = (e z).1 := by
    intro z
    have : (ZMod.castHom (Dvd.intro N' hN) (ZMod (p ^ k))).comp φ =
        (RingHom.fst _ _).comp e.toRingHom := Subsingleton.elim _ _
    simpa [ZMod.castHom_apply] using congrArg (fun f => f z) this
  have h2 : ∀ z, (((φ z : ZMod N)).cast : ZMod N') = (e z).2 := by
    intro z
    have : (ZMod.castHom (Dvd.intro_left _ hN) (ZMod N')).comp φ =
        (RingHom.snd _ _).comp e.toRingHom := Subsingleton.elim _ _
    simpa [ZMod.castHom_apply] using congrArg (fun f => f z) this
  let y := e.symm (-1, 1)
  have hyy : y * y = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    simp [y]
  refine ⟨⟨φ y, φ y, by rw [← map_mul, hyy, map_one], by rw [← map_mul, hyy, map_one]⟩, ?_, ?_⟩
  · show ((φ y : ZMod N).cast : ZMod (p ^ k)) = -1
    rw [h1]; simp [y]
  · show ((φ y : ZMod N).cast : ZMod N') = 1
    rw [h2]; simp [y]

theorem lev_eq_pow (p : ℕ) : ∃ j, 0 < j ∧ lev p = p ^ j := by
  unfold lev
  split_ifs with h
  · exact ⟨2, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, by norm_num, (pow_one p).symm⟩

/-- Casting through an intermediate level. -/
theorem cast_cast_of_dvd {a b c : ℕ} (hab : b ∣ a) (hbc : c ∣ b) (x : ZMod a) :
    (((x.cast : ZMod b)).cast : ZMod c) = (x.cast : ZMod c) := by
  have : (ZMod.castHom hbc (ZMod c)).comp (ZMod.castHom hab (ZMod b)) =
      ZMod.castHom (hbc.trans hab) (ZMod c) := Subsingleton.elim _ _
  have h := congrArg (fun f => f x) this
  simp only [RingHom.comp_apply, ZMod.castHom_apply] at h
  exact h

/-- **The value of `χ` at the CRT unit**: `χ(u_p) = -1` if `p ∈ T₋` and `1` otherwise. -/
theorem chi_toUnitHom_crt (Tm : Finset ℕ) (hTm : ∀ q ∈ Tm, q.Prime) (p : ℕ) (hp : p.Prime)
    (u : (ZMod (chiLevel Tm))ˣ)
    (hu1 : ((u : ZMod (chiLevel Tm)).cast :
      ZMod (p ^ (chiLevel Tm).factorization p)) = -1)
    (hu2 : ((u : ZMod (chiLevel Tm)).cast :
      ZMod (chiLevel Tm / p ^ (chiLevel Tm).factorization p)) = 1) :
    (chi Tm).toUnitHom u = if p ∈ Tm then -1 else 1 := by
  have hN0 : chiLevel Tm ≠ 0 := (chiLevel_pos Tm hTm).ne'
  have factor : ∀ q (hq : q ∈ Tm),
      (DirichletCharacter.changeLevel (lev_dvd_chiLevel hq) (oddChar q)).toUnitHom u =
        if q = p then -1 else 1 := by
    intro q hq
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_apply]
    split_ifs with hqp
    · subst hqp
      -- lev q ∣ q^k
      obtain ⟨j, hj, hlev⟩ := lev_eq_pow q
      have hdvdN : q ^ j ∣ chiLevel Tm := hlev ▸ lev_dvd_chiLevel hq
      have hjk : j ≤ (chiLevel Tm).factorization q :=
        (hp.pow_dvd_iff_le_factorization hN0).mp hdvdN
      have hlevk : lev q ∣ q ^ (chiLevel Tm).factorization q := hlev ▸ pow_dvd_pow q hjk
      have hval : (ZMod.unitsMap (lev_dvd_chiLevel hq) u : ZMod (lev q)) = -1 := by
        rw [ZMod.unitsMap_val, ← cast_cast_of_dvd (Nat.ordProj_dvd _ _) hlevk, hu1,
          ← ZMod.castHom_apply (h := hlevk) (R := ZMod (lev q)), map_neg, map_one]
      have hu : ZMod.unitsMap (lev_dvd_chiLevel hq) u = -1 := Units.ext (by rw [hval]; rfl)
      rw [hu]
      apply Units.ext
      rw [MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one]
      exact oddChar_neg_one hp
    · obtain ⟨j, hj, hlev⟩ := lev_eq_pow q
      have hq' := hTm q hq
      have hnd : ¬ p ∣ lev q := by
        rw [hlev]
        intro h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq').mp (hp.dvd_of_dvd_pow h)).symm
      have hlevN' : lev q ∣ chiLevel Tm / p ^ (chiLevel Tm).factorization p :=
        Nat.dvd_ordCompl_of_dvd_not_dvd (lev_dvd_chiLevel hq) hnd
      have hval : (ZMod.unitsMap (lev_dvd_chiLevel hq) u : ZMod (lev q)) = 1 := by
        rw [ZMod.unitsMap_val, ← cast_cast_of_dvd (Nat.ordCompl_dvd _ _) hlevN', hu2,
          ← ZMod.castHom_apply (h := hlevN') (R := ZMod (lev q)), map_one]
      have hu : ZMod.unitsMap (lev_dvd_chiLevel hq) u = 1 := Units.ext hval
      rw [hu, map_one]
  have hprod : (chi Tm).toUnitHom =
      ∏ q ∈ Tm.attach,
        (DirichletCharacter.changeLevel (lev_dvd_chiLevel q.2) (oddChar q.1)).toUnitHom := by
    have := map_prod (MulChar.mulEquivToUnitHom (R := ZMod (chiLevel Tm)) (R' := ℂ))
      (fun q : Tm => DirichletCharacter.changeLevel (lev_dvd_chiLevel q.2) (oddChar q.1))
      Tm.attach
    exact this
  rw [hprod, MonoidHom.finsetProd_apply]
  rw [Finset.prod_congr rfl (fun q _ => factor q.1 q.2)]
  rw [Finset.prod_attach Tm (fun q => if q = p then (-1 : ℂˣ) else 1)]
  rw [Finset.prod_ite_eq']

/-- **B2 over `G_ℚ`, from the four leaves** (N5 L665-700). -/
theorem b2_of_leaves (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, hsupp, hord, hβl, hβs, hβe⟩

end GlueDescent.B2Q


end DescB2AssemblySec

section DescB3AssemblySec
/-! ### Copied from `scratch/glue-descent/B3Assembly.lean` (compiled there). -/

/-!
# glue-descent: B3 over `G_ℚ` (N5 L701-716), from the leaves of B2

`b3_of_leaves`: with the hypotheses of `b2_of_leaves` and `ε` normalized (`ε(1,1) = 1`), there
are `χ`, `β` as in B2 and an intermediate field `L' ⊇ L` of `ℚ̄/ℚ` (the kernel field of
`β|_{G_L}`), Galois over `ℚ`, with `G_{L'} = ker(β|_{G_L})`, `β` constant on the cosets of
`G_{L'}`, and `[L' : ℚ] ≤ 2 · ord(χ) · [L : ℚ]`.

`b3_degree_le_QM`: if moreover `[L:ℚ] ≤ D` and `T = S ∪ supp M_S(u)` for an admissible `(S, R)`,
then `[L' : ℚ] ≤ Q_R · M_S(u)` (the repository's `heightQ`, `contactSupport`).

Not here: that `L'` is unramified outside `T` after the twist of N5 L702-709. Its group theory is
`twist_kills_inertia` and `inertia_le_kernel` (Cochain.lean); it needs inertia subgroups of
`G_ℚ` (absent from Mathlib) and leaves L-B3a, L-B3b.

Compile out of tree as in B2Assembly.lean (oleans for Cochain, Constants, Chi, B2Glue,
B2Assembly in `scratch/glue-descent/.lake/out/GlueDescent/`).
-/

namespace GlueDescent.B3Q

open GlueDescent GlueDescent.B2 GlueDescent.B2Q

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- `G_L ≤ G_ℚ`. -/
noncomputable def GQL (L : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup GQ := L.fixingSubgroup

theorem mem_GQL {L : IntermediateField ℚ (AlgebraicClosure ℚ)} {σ : GQ} :
    σ ∈ GQL L ↔ ∀ x ∈ L, act σ x = x :=
  IntermediateField.mem_fixingSubgroup_iff L σ

/-- A normalized cocycle inflated from `Gal(L/ℚ)` is `1` as soon as one argument is in `G_L`. -/
theorem inflatedNormalized_of (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1) :
    InflatedNormalized (GQL L) ε := by
  have hc := hε.2.2
  intro σ τ h
  rcases h with h | h
  · have e1 : ε σ τ = ε 1 τ :=
      hinf σ 1 τ τ (fun x hx => (mem_GQL.mp h x hx)) (fun _ _ => rfl)
    have e2 : ε 1 τ = ε 1 1 := by
      have := hc 1 1 τ
      simp only [one_mul] at this
      exact (mul_left_cancel this).symm
    rw [e1, e2, h11]
  · have e1 : ε σ τ = ε σ 1 :=
      hinf σ σ τ 1 (fun _ _ => rfl) (fun x hx => (mem_GQL.mp h x hx))
    have e2 : ε σ 1 = ε 1 1 := by
      have := hc σ 1 1
      simp only [mul_one] at this
      exact mul_right_cancel this
    rw [e1, e2, h11]

theorem orderOf_pos_dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 < orderOf χ := by
  have h := orderOf_dvd_totient χ
  have hφ : 0 < Nat.totient N := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  rcases Nat.eq_zero_or_pos (orderOf χ) with h0 | h0
  · rw [h0, zero_dvd_iff] at h; omega
  · exact h0

/-- **B3 over `G_ℚ`** (N5 L701-716). `η` is any continuous quadratic character (N5's twist
killing inertia outside `T`; take `η = 1` for the untwisted cochain): `β = β_{B2} · η`. -/
theorem b3_of_leaves (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
      (∀ σ k : GQ, k ∈ GQL L' → β (σ * k) = β σ) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  obtain ⟨N, hN, χ, β₁, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves hHasse hTwo hSq hUnr L ε hε hinf T hT hram
  -- the twist `β = β₁ η` (N5 L707-709; `η = 1` gives the untwisted cochain)
  let β : GQ → ℂˣ := fun x => β₁ x * η x
  have hβl : IsLocallyConstant β := hβl₁.mul hηl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ η hη
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ η
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  -- K' is open, hence closed
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  -- degree
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨N, hN, χ, β, L', hsupp, hord, hβl, hβs, hβe, hle, hfd, hgal, hGL', ?_, ?_⟩
  · intro σ k hk
    exact cochain_mul_kernel hβ hεN σ (show k ∈ K' from (hGL' k).mp hk |> (mem_kernelSubgroup hβ hεN).mpr)
  · rw [hL', hL]; exact hidx

/-- **B3 with the constants** (N5 L713-716): `[L' : ℚ] ≤ Q_R · M_S(u)` when `[L:ℚ] ≤ D`,
`T = S ∪ supp M_S(u)` and `(S, R)` is admissible. -/
theorem b3_degree_le_QM (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u := by
  have hT : ∀ p ∈ ramSet S u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β, L', _, hord, hβl, hβs, hβe, hle, hfd, hgal, hGL', _, hdeg⟩ :=
    b3_of_leaves hHasse hTwo hSq hUnr L ε hε hinf h11 (ramSet S u) hT hram η hη hηl
  refine ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd, hgal, hGL', ?_⟩
  have h := degree_le_QM S hS R hRD hRS hR12 u (Module.finrank ℚ L) (orderOf χ) hLD hord
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := h

end GlueDescent.B3Q


end DescB3AssemblySec

section RepoA1QuaternionSec
/-! ### Copied from `scratch/glue-repo/A1Quaternion.lean` (compiled there). -/

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

attribute [local simp] QuaternionAlgebra.re_ofNat QuaternionAlgebra.imI_ofNat QuaternionAlgebra.imJ_ofNat QuaternionAlgebra.imK_ofNat

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
    (Matrix.of fun a b => trd (e a * e b)) = !![2, 0, 1, 0; 0, 4, 0, 2; 1, 0, -1, 0; 0, 2, 0, 4] := by
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
    (Matrix.of fun a b => E (e a) (e b)) = !![0, 0, -1, 1; 0, 0, 1, -2; 1, -1, 0, 0; -1, 2, 0, 0] := by
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
  have h0 : a.re = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h1 : a.imI = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h3 : a.imK = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
  have h2 : a.imJ = 0 := by
    have : (3 * a.imJ - 4 * a.imK) = 0 := by nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg (3 * a.imJ - 4 * a.imK), sq_nonneg a.imK]
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
  have hn' : (n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * n 1 ^ 2 - 2 * n 1 * n 3 - 2 * n 3 ^ 2 : ℤ) = 3 := by
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


end RepoA1QuaternionSec

section RepoTorsionFreeSec
/-! ### Copied from `scratch/glue-repo/TorsionFree.lean` (compiled there). -/

/-!
# glue-repo, steps A6 and A8: `1 + 3 M_r(R)` is torsion-free; Minkowski's bound

* `CommCore.eq_one_of_pow_eq_one`: in a commutative ring in which `3` is a non-zero-divisor
  and `⋂ₙ 3ⁿ C = 0`, an element `A ≡ 1 (mod 3)` of finite order is `1`.
* `eq_one_of_pow_eq_one`: the same in any ring (applied in the commutative subalgebra `ℤ[y]`).
* `matrix_int_eq_one`, `matrix_padic_eq_one`: the same for `M_r(ℤ)` and `M_r(ℤ₃)` (N5 L468-470;
  h-b1 Lemma PR(ii) step 3: `ρ(I_v)` finite inside `1 + 3M₄(ℤ₃)` is trivial; A4's neatness).
* `injective_mod_three`, `card_le_three_pow`: a finite subgroup of `GL_r(ℤ)` injects into
  `GL_r(𝔽₃)`, so has order `≤ 3^(r²)` (N5 L551-553, step A8: `[E:ℚ] ≤ 3^{r²}`).
-/

namespace GlueRepo.TorsionFree

namespace CommCore

variable {C : Type*} [CommRing C]
variable (h3 : ∀ x : C, (3 : C) * x = 0 → x = 0)
variable (hsep : ∀ x : C, (∀ n : ℕ, ∃ y, x = (3 : C) ^ n * y) → x = 0)

theorem one_add_pow_expand (N : C) (m : ℕ) :
    ∃ Q : C, (1 + N) ^ m = 1 + (m : C) * N + N ^ 2 * Q := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨Q, hQ⟩ := ih
    exact ⟨(m : C) + Q + Q * N, by rw [pow_succ, hQ]; push_cast; ring⟩

include h3

theorem cancel_three_pow {n : ℕ} {x : C} (h : (3 : C) ^ n * x = 0) : x = 0 := by
  induction n with
  | zero => simpa using h
  | succ n ih => exact ih (h3 _ (by rw [← mul_assoc, ← pow_succ']; exact h))

/-- Step for `3 ∤ m`. -/
theorem step_coprime {m : ℕ} (hm : ¬ 3 ∣ m) {N : C} (hN : (1 + N) ^ m = 1) {k : ℕ} (hk : 1 ≤ k)
    {M : C} (hM : N = (3 : C) ^ k * M) : ∃ M', N = (3 : C) ^ (k + 1) * M' := by
  obtain ⟨Q, hQ⟩ := one_add_pow_expand N m
  rw [hN] at hQ
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : (m : C) * M + 3 * ((3 : C) ^ j * M ^ 2 * Q) = 0 := by
    apply cancel_three_pow h3 (n := j + 1)
    rw [hM] at hQ
    linear_combination (-1 : C) * hQ
  obtain ⟨q, hq⟩ : ∃ q, m = 3 * q + 1 ∨ m = 3 * q + 2 := ⟨m / 3, by omega⟩
  set Y := (3 : C) ^ j * M ^ 2 * Q
  rcases hq with hq | hq
  · subst hq
    refine ⟨-Y - (q : C) * M, ?_⟩
    rw [hM]; push_cast at h4
    linear_combination (3 : C) ^ (j + 1) * h4
  · subst hq
    refine ⟨M + Y + (q : C) * M, ?_⟩
    rw [hM]; push_cast at h4
    linear_combination (-(3 : C) ^ (j + 1)) * h4

/-- Step for `m = 3`. -/
theorem step_three {N : C} (hN : (1 + N) ^ 3 = 1) {k : ℕ} (hk : 1 ≤ k)
    {M : C} (hM : N = (3 : C) ^ k * M) : ∃ M', N = (3 : C) ^ (k + 1) * M' := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h4 : M + 3 * ((3 : C) ^ j * M ^ 2 + (3 : C) ^ j * (3 : C) ^ j * M ^ 3) = 0 := by
    apply cancel_three_pow h3 (n := j + 2)
    rw [hM] at hN
    linear_combination hN
  refine ⟨-((3 : C) ^ j * M ^ 2 + (3 : C) ^ j * (3 : C) ^ j * M ^ 3), ?_⟩
  rw [hM]
  linear_combination (3 : C) ^ (j + 1) * h4

include hsep in
omit h3 in
/-- If every `3^k`-divisibility of `N` (`k ≥ 1`) improves to `3^{k+1}`, and `3 ∣ N`, then `N = 0`. -/
theorem eq_zero_of_step {N : C} (h1 : ∃ y, N = 3 * y)
    (hstep : ∀ k, 1 ≤ k → ∀ M, N = (3 : C) ^ k * M → ∃ M', N = (3 : C) ^ (k + 1) * M') : N = 0 := by
  apply hsep
  intro n
  induction n with
  | zero => exact ⟨N, by simp⟩
  | succ n ih =>
    rcases n with _ | n
    · obtain ⟨y, hy⟩ := h1; exact ⟨y, by simpa using hy⟩
    · obtain ⟨M, hM⟩ := ih
      exact hstep (n + 1) (by omega) M hM

include hsep in
theorem eq_one_of_pow_eq_one {A : C} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m)
    (hAm : A ^ m = 1) : A = 1 := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' 3 (by norm_num)
  induction a generalizing A with
  | zero =>
    simp only [pow_zero, one_mul] at hAm
    obtain ⟨y, rfl⟩ := hA
    have : 3 * y = 0 := eq_zero_of_step hsep ⟨y, rfl⟩
      (fun k hk M hM => step_coprime h3 hb (by simpa using hAm) hk hM)
    rw [this, add_zero]
  | succ a ih =>
    have h3' : A ^ 3 = 1 := by
      apply ih
      · obtain ⟨y, rfl⟩ := hA
        exact ⟨3 * y + 9 * y ^ 2 + 9 * y ^ 3, by ring⟩
      · exact Nat.mul_pos (pow_pos (by norm_num) _) (Nat.pos_of_ne_zero (by rintro rfl; simp at hb))
      · rw [← pow_mul, ← hAm]; ring_nf
    obtain ⟨y, rfl⟩ := hA
    have : 3 * y = 0 := eq_zero_of_step hsep ⟨y, rfl⟩
      (fun k hk M hM => step_three h3 (by simpa using h3') hk hM)
    rw [this, add_zero]

end CommCore

section General

variable {S : Type*} [Ring S]

/-- The commutative subalgebra `ℤ[y]` of a ring. -/
instance adjoinCommRing (y : S) : CommRing (Algebra.adjoin ℤ ({y} : Set S)) :=
  { (inferInstance : Ring (Algebra.adjoin ℤ ({y} : Set S))) with
    mul_comm := fun a b => Subtype.ext <|
      (Algebra.commute_of_mem_adjoin_singleton_of_commute b.2
        (Algebra.commute_of_mem_adjoin_self a.2).symm).eq }

theorem eq_one_of_pow_eq_one
    (h3 : ∀ x : S, (3 : S) * x = 0 → x = 0)
    (hsep : ∀ x : S, (∀ n : ℕ, ∃ y, x = (3 : S) ^ n * y) → x = 0)
    {A : S} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 := by
  obtain ⟨y, rfl⟩ := hA
  let C := Algebra.adjoin ℤ ({y} : Set S)
  let y' : C := ⟨y, Algebra.self_mem_adjoin_singleton ℤ y⟩
  have h3c : ((3 : C) : S) = 3 := rfl
  have key : (1 + 3 * y' : C) = 1 := by
    apply CommCore.eq_one_of_pow_eq_one (C := C)
    · intro x hx
      exact Subtype.ext (h3 x (by simpa [h3c] using congrArg Subtype.val hx))
    · intro x hx
      refine Subtype.ext (hsep x fun n => ?_)
      obtain ⟨z, hz⟩ := hx n
      exact ⟨z, by simpa [h3c] using congrArg Subtype.val hz⟩
    · exact ⟨y', rfl⟩
    · exact hm
    · exact Subtype.ext (by simpa [y', h3c] using hAm)
  simpa [y', h3c] using congrArg Subtype.val key

end General

section Matrices

variable {r : ℕ} {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem three_pow_mul (n : ℕ) (y : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    ((3 : Matrix (Fin r) (Fin r) R) ^ n * y) i j = (3 : R) ^ n * y i j := by
  have : (3 : Matrix (Fin r) (Fin r) R) ^ n * y = (3 ^ n : ℕ) • y := by
    rw [nsmul_eq_mul]; push_cast; rfl
  rw [this, Matrix.smul_apply, nsmul_eq_mul]; push_cast; rfl

/-- `M_r(R)` satisfies the hypotheses of `eq_one_of_pow_eq_one` when `R` is a Noetherian domain
in which `3` is a nonzero nonunit (Krull's intersection theorem). -/
theorem matrix_eq_one (hR : (3 : R) ≠ 0) (hu : ¬ IsUnit (3 : R))
    {A : Matrix (Fin r) (Fin r) R} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ} (hm : 0 < m)
    (hAm : A ^ m = 1) : A = 1 := by
  refine eq_one_of_pow_eq_one ?_ ?_ hA hm hAm
  · intro x hx
    ext i j
    have := congrFun (congrFun hx i) j
    rw [show (3 : Matrix (Fin r) (Fin r) R) * x = (3 : Matrix (Fin r) (Fin r) R) ^ 1 * x by
      rw [pow_one], three_pow_mul] at this
    simpa [hR] using this
  · intro x hx
    ext i j
    have hI : Ideal.span {(3 : R)} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hmem : x i j ∈ ⨅ n : ℕ, Ideal.span {(3 : R)} ^ n := by
      rw [Ideal.mem_iInf]
      intro n
      obtain ⟨y, hy⟩ := hx n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hy, three_pow_mul]
      exact dvd_mul_right _ _
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {(3 : R)}) hI, Ideal.mem_bot] at hmem
    simpa using hmem

/-- `1 + 3M_r(ℤ)` is torsion-free. -/
theorem matrix_int_eq_one {A : Matrix (Fin r) (Fin r) ℤ} (hA : ∃ y, A = 1 + 3 * y) {m : ℕ}
    (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 :=
  matrix_eq_one (by norm_num) (by rw [Int.isUnit_iff]; norm_num) hA hm hAm

/-- `1 + 3M_r(ℤ₃)` is torsion-free (N5 L468-470). -/
theorem matrix_padic_eq_one {A : Matrix (Fin r) (Fin r) ℤ_[3]} (hA : ∃ y, A = 1 + 3 * y)
    {m : ℕ} (hm : 0 < m) (hAm : A ^ m = 1) : A = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine matrix_eq_one (by norm_num) ?_ hA hm hAm
  rw [PadicInt.isUnit_iff, show ((3 : ℤ_[3])) = ((3 : ℕ) : ℤ_[3]) by norm_cast,
    PadicInt.norm_p]
  norm_num

/-- A subgroup of `GL_r(ℤ₃)` all of whose elements are `≡ 1 (mod 3)` and of finite order is
trivial (h-b1 Lemma PR(ii) step 3, with `H = ρ(I_v)`). -/
theorem padic_subgroup_trivial (H : Subgroup (GL (Fin r) ℤ_[3])) [Finite H]
    (hH : ∀ g ∈ H, ∃ y, (g : Matrix (Fin r) (Fin r) ℤ_[3]) = 1 + 3 * y) : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have hpow : (⟨g, hg⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  have hm : 0 < Nat.card H := Nat.card_pos
  have h1 : g ^ Nat.card H = 1 := by
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hpow
  apply Units.ext
  refine matrix_padic_eq_one (hH g hg) hm ?_
  simpa using congrArg Units.val h1

/-- Minkowski: a finite subgroup of `GL_r(ℤ)` injects into `GL_r(𝔽₃)`. -/
theorem injective_mod_three (G : Subgroup (GL (Fin r) ℤ)) [Finite G] :
    Function.Injective
      ((Matrix.GeneralLinearGroup.map (n := Fin r) (Int.castRingHom (ZMod 3))).comp G.subtype) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hdvd : ∀ i j, ∃ c : ℤ, ((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) i j
      = (1 : Matrix (Fin r) (Fin r) ℤ) i j + 3 * c := by
    intro i j
    have := congrArg (fun h : GL (Fin r) (ZMod 3) => (h : Matrix (Fin r) (Fin r) (ZMod 3)) i j) hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Units.val_one] at this
    have h2 : ((((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) i j : ℤ) : ZMod 3)
        = (((1 : Matrix (Fin r) (Fin r) ℤ) i j : ℤ) : ZMod 3) := by
      by_cases hij : i = j <;> simpa [Matrix.GeneralLinearGroup.map, Matrix.one_apply, hij] using this
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨-c, by push_cast at hc; linarith⟩
  choose c hc using hdvd
  have hA : ∃ y, ((g : GL (Fin r) ℤ) : Matrix (Fin r) (Fin r) ℤ) = 1 + 3 * y := by
    refine ⟨Matrix.of c, ?_⟩
    ext i j
    rw [Matrix.add_apply, show (3 : Matrix (Fin r) (Fin r) ℤ) * Matrix.of c
      = (3 : Matrix (Fin r) (Fin r) ℤ) ^ 1 * Matrix.of c by rw [pow_one], three_pow_mul]
    simpa using hc i j
  have hpow : g ^ Nat.card G = 1 := pow_card_eq_one'
  have h1 : (g : GL (Fin r) ℤ) ^ Nat.card G = 1 := by
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val hpow
  apply Subtype.ext
  apply Units.ext
  simp only [OneMemClass.coe_one, Units.val_one]
  refine matrix_int_eq_one hA (Nat.card_pos (α := G)) ?_
  simpa using congrArg Units.val h1

/-- Minkowski's bound used in step A8: a finite subgroup of `GL_r(ℤ)` has order `≤ 3^(r²)`. -/
theorem card_le_three_pow (G : Subgroup (GL (Fin r) ℤ)) [Finite G] :
    Nat.card G ≤ 3 ^ (r ^ 2) := by
  have hinj : Function.Injective fun g : G =>
      (((Matrix.GeneralLinearGroup.map (n := Fin r) (Int.castRingHom (ZMod 3))).comp G.subtype) g :
        Matrix (Fin r) (Fin r) (ZMod 3)) :=
    fun a b h => injective_mod_three G (Units.ext h)
  calc Nat.card G ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod 3)) :=
        Nat.card_le_card_of_injective _ hinj
    _ = 3 ^ (r ^ 2) := by
        show Nat.card (Fin r → Fin r → ZMod 3) = _
        simp [Nat.card_fun, Nat.card_zmod, ← pow_mul, sq]

end Matrices

end GlueRepo.TorsionFree


end RepoTorsionFreeSec

section RepoPRArithSec
/-! ### Copied from `scratch/glue-repo/PRArith.lean` (compiled there). -/

/-!
# glue-repo, steps A5 and A7: the arithmetic of Lemma PR(i) (h-b1 §4) and of the fibre point

For `u ∈ ℚ ∖ 𝒞`, `j₀ = J(u) = −57600 F(u)²/G(u)⁶`. Prop. TS (h-b1 §1.2, a published theorem)
says: at a prime `p` where the cover `Y₃ → P¹_j` is tame with no vertical ramification
(Lemma NV, `p ≥ 5`), the inertia of the fibre field at `p` has order `e_b / gcd(e_b, m_b)`, where
`m_b` is the intersection multiplicity of `j₀` with the branch point `b ∈ {0, ∞, −16/27}`,
`(e₀, e_∞, e_{−16/27}) = (4, 6, 2)` (A2). Here we prove the elementary half of Lemma PR(i):

* `inertia_trivial_iff` : for every prime `p ≥ 17` and `u ∈ ℚ ∖ 𝒞`,
  `4 ∣ m₀ ∧ 6 ∣ m_∞ ∧ 2 ∣ m_{−16/27}` (i.e. all three predicted inertia orders are 1)
  iff no `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd; with `m₀ = v_p(j₀)⁺`,
  `m_∞ = (−v_p(j₀))⁺`, `m_{−16/27} = v_p(j₀ + 16/27)⁺`.
* `inertia_trivial_of_not_dvd` : the same in terms of `M_S(u) = ZInQ.contactSupport S u`.
* `Hq_ne_zero`, `J_ne_zero`, `J_ne_branch` : `j₀` is finite, nonzero and `≠ −16/27`
  (h-b1 M7; A7 "j = J(u) is rational, finite and nonzero").
* `G6_sub_F2`, `J_add`, `t_eq`, `t_sub_one` : N5 L510-516 and rv-h-cm §1.4.
-/

open ZInQ

namespace GlueRepo.PR

/-- The rational functions of N5 L377-386, L510-516. -/
def Fq (u : ℚ) : ℚ := u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)
def Gq (u : ℚ) : ℚ := 7 * u ^ 2 + 300 * u + 3600
def Hq (u : ℚ) : ℚ :=
  (u ^ 2 - 60 * u - 1800) * (13 * u ^ 2 + 480 * u + 3600) * (11 * u ^ 2 + 600 * u + 7200)
/-- `H` in homogeneous form. -/
def Hh (a b : ℤ) : ℤ :=
  (a ^ 2 - 60 * a * b - 1800 * b ^ 2) * (13 * a ^ 2 + 480 * a * b + 3600 * b ^ 2) *
    (11 * a ^ 2 + 600 * a * b + 7200 * b ^ 2)

/-- `J(u)`, verbatim copy of `ZInQ.JHeight.Jmap` (`ZInQKernel/Hypotheses/JHeight.lean`, which
scratch files cannot import in this worktree). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

theorem Jmap_eq (u : ℚ) : Jmap u = -57600 * Fq u ^ 2 / Gq u ^ 6 := rfl

/-- `G⁶ − 97200 F² = H²` (N5 L513-515). -/
theorem G6_sub_F2 (u : ℚ) : Gq u ^ 6 - 97200 * Fq u ^ 2 = Hq u ^ 2 := by
  unfold Gq Fq Hq; ring

theorem Gq_ne_zero (u : ℚ) : Gq u ≠ 0 := by
  unfold Gq; nlinarith [sq_nonneg (7 * u + 150)]

/-- `J + 16/27 = 16 H² / (27 G⁶)` (h-b1 M7). -/
theorem J_add (u : ℚ) : Jmap u + 16 / 27 = 16 * Hq u ^ 2 / (27 * Gq u ^ 6) := by
  have hG := Gq_ne_zero u
  rw [Jmap_eq]
  field_simp
  linear_combination (16 : ℚ) * G6_sub_F2 u

/-- Elkies' coordinate `t = 1 + 27 j / 16` (rv-h-cm §1.3). -/
def tq (u : ℚ) : ℚ := 1 + 27 * Jmap u / 16

theorem t_eq (u : ℚ) : tq u = Hq u ^ 2 / Gq u ^ 6 := by
  have hG := Gq_ne_zero u
  unfold tq; rw [Jmap_eq]; field_simp
  linear_combination (16 : ℚ) * G6_sub_F2 u

theorem t_sub_one (u : ℚ) : tq u - 1 = -3 * (180 * Fq u / Gq u ^ 3) ^ 2 := by
  have hG := Gq_ne_zero u
  unfold tq; rw [Jmap_eq]; field_simp; ring

/-! ### Nonvanishing -/

/-- A rational square has even `3`-adic valuation. -/
theorem not_sq_of_odd_val {x d : ℚ} (hx : x ^ 2 = d) (hd : d ≠ 0)
    (hodd : Odd (padicValRat 3 d)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← hx, padicValRat.pow] at hodd
  exact (Int.not_even_iff_odd.mpr hodd) ⟨padicValRat 3 x, by push_cast; ring⟩

theorem quad_ne_zero {α β γ : ℚ} (hα : α ≠ 0) (hΔ : β ^ 2 - 4 * α * γ ≠ 0)
    (hodd : Odd (padicValRat 3 (β ^ 2 - 4 * α * γ))) (u : ℚ) : α * u ^ 2 + β * u + γ ≠ 0 := by
  intro h
  exact not_sq_of_odd_val (x := 2 * α * u + β) (by linear_combination 4 * α * h) hΔ hodd

theorem val3_43200 : padicValRat 3 (43200 : ℚ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (43200 : ℚ) = ((3 ^ 3 * 1600 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rfl

theorem val3_10800 : padicValRat 3 (10800 : ℚ) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [show (10800 : ℚ) = ((3 ^ 3 * 400 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rfl

/-- `H` has no rational root: its quadratic factors have discriminants `10800, 43200, 43200`,
of odd `3`-adic valuation (h-b1 M7). -/
theorem Hq_ne_zero (u : ℚ) : Hq u ≠ 0 := by
  have h1 : (1 : ℚ) * u ^ 2 + (-60) * u + (-1800) ≠ 0 :=
    quad_ne_zero one_ne_zero (by norm_num) (by norm_num [val3_10800]) u
  have h2 : (13 : ℚ) * u ^ 2 + 480 * u + 3600 ≠ 0 :=
    quad_ne_zero (by norm_num) (by norm_num) (by norm_num [val3_43200]) u
  have h3 : (11 : ℚ) * u ^ 2 + 600 * u + 7200 ≠ 0 :=
    quad_ne_zero (by norm_num) (by norm_num) (by norm_num [val3_43200]) u
  unfold Hq
  refine mul_ne_zero (mul_ne_zero ?_ h2) h3
  intro h; apply h1; linear_combination h

theorem Fq_ne_zero {u : ℚ} (hu : u ∉ contactSet) : Fq u ≠ 0 := by
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
  unfold Fq
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 ?_) ?_) ?_) ?_) ?_
  all_goals intro h
  exacts [h1 (by linarith), h2 (by linarith), h3 (by linarith), h4 (by linarith), h5 (by linarith)]

/-- `j₀ = J(u)` is finite and nonzero for `u ∉ 𝒞` (A7). -/
theorem J_ne_zero {u : ℚ} (hu : u ∉ contactSet) : Jmap u ≠ 0 := by
  rw [Jmap_eq]
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (Fq_ne_zero hu)))
    (pow_ne_zero _ (Gq_ne_zero u))

/-- `j₀ ≠ −16/27`: `J(u)` is not a branch value (h-b1 M7). -/
theorem J_ne_branch (u : ℚ) : Jmap u ≠ -16 / 27 := by
  intro h
  have h1 := J_add u
  rw [h] at h1
  have hH := Hq_ne_zero u
  have hG := Gq_ne_zero u
  have h2 : 16 * Hq u ^ 2 / (27 * Gq u ^ 6) ≠ 0 := by positivity
  exact h2 (by rw [← h1]; norm_num)

/-! ### The valuation case analysis of Lemma PR(i) -/

section Valuation

variable {p : ℕ} [hp : Fact p.Prime]

/-- A `{2,3,5,7,11,13}`-smooth number bound. -/
def smoothBound : ℕ := 2 ^ 60 * 3 ^ 40 * 5 ^ 40 * 7 ^ 6 * 11 ^ 6 * 13 ^ 6

theorem not_dvd_smoothBound (h17 : 17 ≤ p) : ¬ p ∣ smoothBound := by
  have hpp := hp.out.prime
  intro h
  simp only [smoothBound, hpp.dvd_mul] at h
  rcases h with (((((h | h) | h) | h) | h) | h) <;>
    have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h) <;> omega

theorem smooth_ne_zero (h17 : 17 ≤ p) (N : ℕ) (hN : N ∣ smoothBound) : (N : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => not_dvd_smoothBound h17 (h.trans hN)

theorem vpos_iff {z : ℤ} (hz : z ≠ 0) : 0 < padicValInt p z ↔ (z : ZMod p) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← pow_one (p : ℤ), padicValInt_dvd_iff]
  simp [hz, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]

theorem pair_not {x y b : ℤ} {d : ℕ} (hd : (d : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (h : y = x + d * b) : ¬ ((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
  rintro ⟨hx, hy⟩
  rw [h] at hy; push_cast at hy; rw [hx, zero_add] at hy
  exact (mul_ne_zero hd hb) hy

theorem bezout_not {x y b s t : ℤ} {N k : ℕ} (hN : (N : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0)
    (h : s * x + t * y = N * b ^ k) : ¬ ((x : ZMod p) = 0 ∧ (y : ZMod p) = 0) := by
  rintro ⟨hx, hy⟩
  have := congrArg (fun z : ℤ => (z : ZMod p)) h
  push_cast at this
  rw [hx, hy, mul_zero, mul_zero, add_zero] at this
  exact (mul_ne_zero hN (pow_ne_zero _ hb)) this.symm

/-- `F`, `G` in homogeneous form (copies of `ZInQ.JHeight.Fh`, `Gh`). -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- Homogeneous Bezout certificates (`scratch/glue-repo/bezout.py`). -/
theorem bez_FG (a b : ℤ) :
    (-1001 * a - 37650 * b) * Fh a b + (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2
      + 20691900 * a ^ 2 * b ^ 3 + 133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b
      = (104976000000 : ℕ) * b ^ 7 := by
  unfold Fh Gh; push_cast; ring

theorem bez_FH (a b : ℤ) :
    (16823807 * a ^ 5 + 168910350 * a ^ 4 * b - 76576533600 * a ^ 3 * b ^ 2
      - 3442684140000 * a ^ 2 * b ^ 3 - 52460404920000 * a * b ^ 4 - 259773966000000 * b ^ 5) * Fh a b
    + (-117649 * a ^ 5 - 15008651 * a ^ 4 * b - 649710600 * a ^ 3 * b ^ 2
      - 11566268700 * a ^ 2 * b ^ 3 - 72155790000 * a * b ^ 4 - 14580000 * b ^ 5) * Hh a b
      = (680244480000000000 : ℕ) * b ^ 11 := by
  unfold Fh Hh; push_cast; ring

theorem bez_GH (a b : ℤ) :
    (-858 * a ^ 5 - 5693 * a ^ 4 * b + 3924600 * a ^ 3 * b ^ 2 + 161087400 * a ^ 2 * b ^ 3
      + 2164860000 * a * b ^ 4 + 9985680000 * b ^ 5) * Gh a b + (42 * a + 757 * b) * Hh a b
      = (629856000000 : ℕ) * b ^ 7 := by
  unfold Gh Hh; push_cast; ring

theorem padicValRat_int_eq_zero (h17 : 17 ≤ p) {z : ℤ} (N : ℕ) (hz : z.natAbs = N)
    (hN : N ∣ smoothBound) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd]
  · rfl
  · rw [Int.natCast_dvd, hz]
    exact fun h => not_dvd_smoothBound h17 (h.trans hN)

/-- The final case analysis of Lemma PR(i) over the naturals (`p ∤ b`). -/
theorem final_nat {v0 v1 v2 v3 v4 v5 vF vG vH vb : ℕ}
    (hF : (vF : ℤ) = v0 + v1 + v2 + v3 + v4 + v5) (hb : vb = 0)
    (q01 : ¬ (0 < v0 ∧ 0 < v1))
    (q02 : ¬ (0 < v0 ∧ 0 < v2))
    (q03 : ¬ (0 < v0 ∧ 0 < v3))
    (q04 : ¬ (0 < v0 ∧ 0 < v4))
    (q05 : ¬ (0 < v0 ∧ 0 < v5))
    (q12 : ¬ (0 < v1 ∧ 0 < v2))
    (q13 : ¬ (0 < v1 ∧ 0 < v3))
    (q14 : ¬ (0 < v1 ∧ 0 < v4))
    (q15 : ¬ (0 < v1 ∧ 0 < v5))
    (q23 : ¬ (0 < v2 ∧ 0 < v3))
    (q24 : ¬ (0 < v2 ∧ 0 < v4))
    (q25 : ¬ (0 < v2 ∧ 0 < v5))
    (q34 : ¬ (0 < v3 ∧ 0 < v4))
    (q35 : ¬ (0 < v3 ∧ 0 < v5))
    (q45 : ¬ (0 < v4 ∧ 0 < v5))
    (bFG : ¬ (0 < vF ∧ 0 < vG)) (bFH : ¬ (0 < vF ∧ 0 < vH)) (bGH : ¬ (0 < vG ∧ 0 < vH)) :
    (4 ∣ (2 * (vF : ℤ) - 6 * (vG : ℤ)).toNat ∧ 6 ∣ (-(2 * (vF : ℤ) - 6 * (vG : ℤ))).toNat ∧
      2 ∣ (2 * (vH : ℤ) - 6 * (vG : ℤ)).toNat) ↔
      ¬ ((0 < (v0 : ℤ) - vb ∧ ((v0 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v1 : ℤ) - vb ∧ ((v1 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v2 : ℤ) - vb ∧ ((v2 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v3 : ℤ) - vb ∧ ((v3 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v4 : ℤ) - vb ∧ ((v4 : ℤ) - vb) % 2 = 1) ∨
        (0 < (v5 : ℤ) - vb ∧ ((v5 : ℤ) - vb) % 2 = 1)) := by
  subst hb
  rcases Nat.eq_zero_or_pos vF with hF0 | hF0
  · clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH
    have e0 : v0 = 0 := by omega
    have e1 : v1 = 0 := by omega
    have e2 : v2 = 0 := by omega
    have e3 : v3 = 0 := by omega
    have e4 : v4 = 0 := by omega
    have e5 : v5 = 0 := by omega
    omega
  · have hG0 : vG = 0 := by by_contra h; exact bFG ⟨hF0, Nat.pos_of_ne_zero h⟩
    have hH0 : vH = 0 := by by_contra h; exact bFH ⟨hF0, Nat.pos_of_ne_zero h⟩
    rcases Nat.eq_zero_or_pos v0 with h0 | h0
    ·
      rcases Nat.eq_zero_or_pos v1 with h1 | h1
      ·
        rcases Nat.eq_zero_or_pos v2 with h2 | h2
        ·
          rcases Nat.eq_zero_or_pos v3 with h3 | h3
          ·
            rcases Nat.eq_zero_or_pos v4 with h4 | h4
            ·
              rcases Nat.eq_zero_or_pos v5 with h5 | h5
              ·
                clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
                omega
              · have z0 : v0 = 0 := by by_contra h; exact q05 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z1 : v1 = 0 := by by_contra h; exact q15 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z2 : v2 = 0 := by by_contra h; exact q25 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z3 : v3 = 0 := by by_contra h; exact q35 ⟨(Nat.pos_of_ne_zero h), h5⟩
                have z4 : v4 = 0 := by by_contra h; exact q45 ⟨(Nat.pos_of_ne_zero h), h5⟩
                clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
                omega
            · have z0 : v0 = 0 := by by_contra h; exact q04 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z1 : v1 = 0 := by by_contra h; exact q14 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z2 : v2 = 0 := by by_contra h; exact q24 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z3 : v3 = 0 := by by_contra h; exact q34 ⟨(Nat.pos_of_ne_zero h), h4⟩
              have z5 : v5 = 0 := by by_contra h; exact q45 ⟨h4, (Nat.pos_of_ne_zero h)⟩
              clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
              omega
          · have z0 : v0 = 0 := by by_contra h; exact q03 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z1 : v1 = 0 := by by_contra h; exact q13 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z2 : v2 = 0 := by by_contra h; exact q23 ⟨(Nat.pos_of_ne_zero h), h3⟩
            have z4 : v4 = 0 := by by_contra h; exact q34 ⟨h3, (Nat.pos_of_ne_zero h)⟩
            have z5 : v5 = 0 := by by_contra h; exact q35 ⟨h3, (Nat.pos_of_ne_zero h)⟩
            clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
            omega
        · have z0 : v0 = 0 := by by_contra h; exact q02 ⟨(Nat.pos_of_ne_zero h), h2⟩
          have z1 : v1 = 0 := by by_contra h; exact q12 ⟨(Nat.pos_of_ne_zero h), h2⟩
          have z3 : v3 = 0 := by by_contra h; exact q23 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          have z4 : v4 = 0 := by by_contra h; exact q24 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          have z5 : v5 = 0 := by by_contra h; exact q25 ⟨h2, (Nat.pos_of_ne_zero h)⟩
          clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
          omega
      · have z0 : v0 = 0 := by by_contra h; exact q01 ⟨(Nat.pos_of_ne_zero h), h1⟩
        have z2 : v2 = 0 := by by_contra h; exact q12 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z3 : v3 = 0 := by by_contra h; exact q13 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z4 : v4 = 0 := by by_contra h; exact q14 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        have z5 : v5 = 0 := by by_contra h; exact q15 ⟨h1, (Nat.pos_of_ne_zero h)⟩
        clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
        omega
    · have z1 : v1 = 0 := by by_contra h; exact q01 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z2 : v2 = 0 := by by_contra h; exact q02 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z3 : v3 = 0 := by by_contra h; exact q03 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z4 : v4 = 0 := by by_contra h; exact q04 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      have z5 : v5 = 0 := by by_contra h; exact q05 ⟨h0, (Nat.pos_of_ne_zero h)⟩
      clear q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH
      omega


/-- **Lemma PR(i), elementary half.** For a prime `p ≥ 17` and `u ∈ ℚ ∖ 𝒞`, the three
predicted inertia orders `e_b / gcd(e_b, m_b)` of Prop. TS are all `1` (equivalently
`e_b ∣ m_b`) iff no `v_p(u − c)`, `c ∈ 𝒞`, is positive and odd. -/
theorem inertia_trivial_iff (h17 : 17 ≤ p) {u : ℚ} (hu : u ∉ contactSet) :
    (4 ∣ (padicValRat p (Jmap u)).toNat ∧ 6 ∣ (-padicValRat p (Jmap u)).toNat ∧
      2 ∣ (padicValRat p (Jmap u + 16 / 27)).toNat) ↔
    ¬ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)) := by
  set a : ℤ := u.num
  set b : ℤ := (u.den : ℤ)
  have hbq : (b : ℚ) ≠ 0 := by simp [b]
  have hb0 : b ≠ 0 := by simp [b]
  have hu_eq : u = (a : ℚ) / b := by simp [a, b, Rat.num_div_den]
  have hFq := Fq_ne_zero hu
  have hGq := Gq_ne_zero u
  have hHq := Hq_ne_zero u
  -- homogeneous forms
  have eF : Fq u = (Fh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Fq Fh; push_cast; field_simp
  have eG : Gq u = (Gh a b : ℚ) / (b : ℚ) ^ 2 := by
    rw [hu_eq]; unfold Gq Gh; push_cast; field_simp
  have eH : Hq u = (Hh a b : ℚ) / (b : ℚ) ^ 6 := by
    rw [hu_eq]; unfold Hq Hh; push_cast; field_simp
  have hFh : (Fh a b : ℚ) ≠ 0 := by
    intro h; apply hFq; rw [eF, h, zero_div]
  have hGh : (Gh a b : ℚ) ≠ 0 := by
    intro h; apply hGq; rw [eG, h, zero_div]
  have hHh : (Hh a b : ℚ) ≠ 0 := by
    intro h; apply hHq; rw [eH, h, zero_div]
  have hFh' : Fh a b ≠ 0 := by exact_mod_cast hFh
  have hGh' : Gh a b ≠ 0 := by exact_mod_cast hGh
  have hHh' : Hh a b ≠ 0 := by exact_mod_cast hHh
  have eJ : Jmap u = ((-57600 : ℤ) : ℚ) * (Fh a b : ℚ) ^ 2 / (Gh a b : ℚ) ^ 6 := by
    rw [Jmap_eq, eF, eG]; push_cast; field_simp
  have eJ' : Jmap u + 16 / 27 = ((16 : ℤ) : ℚ) * (Hh a b : ℚ) ^ 2 / (((27 : ℤ) : ℚ) * (Gh a b : ℚ) ^ 6) := by
    rw [J_add, eH, eG]; push_cast; field_simp
  -- valuations of J and J + 16/27
  have v57600 : padicValRat p (((-57600 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 57600 (by norm_num) (by unfold smoothBound; norm_num)
  have v16 : padicValRat p (((16 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 16 (by norm_num) (by unfold smoothBound; norm_num)
  have v27 : padicValRat p (((27 : ℤ) : ℚ)) = 0 :=
    padicValRat_int_eq_zero h17 27 (by norm_num) (by unfold smoothBound; norm_num)
  have hJv : padicValRat p (Jmap u) = 2 * padicValInt p (Fh a b) - 6 * padicValInt p (Gh a b) := by
    rw [eJ, padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hFh)) (pow_ne_zero _ hGh),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hFh), padicValRat.pow, padicValRat.pow,
      v57600, padicValRat.of_int, padicValRat.of_int]
    push_cast; ring
  have hJv' : padicValRat p (Jmap u + 16 / 27)
      = 2 * padicValInt p (Hh a b) - 6 * padicValInt p (Gh a b) := by
    rw [eJ', padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hHh))
        (mul_ne_zero (by norm_num) (pow_ne_zero _ hGh)),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hHh),
      padicValRat.mul (by norm_num) (pow_ne_zero _ hGh), padicValRat.pow, padicValRat.pow,
      v16, v27, padicValRat.of_int, padicValRat.of_int]
    push_cast; ring
  -- the six contact factors
  have hX : ∀ c : ℤ, (c : ℚ) ∈ contactSet → ((a - c * b : ℤ) : ℚ) ≠ 0 ∧
      u - c = ((a - c * b : ℤ) : ℚ) / b := by
    intro c hc
    have e : u - c = ((a - c * b : ℤ) : ℚ) / b := by rw [hu_eq]; push_cast; field_simp
    refine ⟨fun h => ?_, e⟩
    rw [h, zero_div, sub_eq_zero] at e
    exact hu (e ▸ hc)
  have vX : ∀ c : ℤ, (c : ℚ) ∈ contactSet →
      padicValRat p (u - c) = padicValInt p (a - c * b) - padicValInt p b := by
    intro c hc
    rw [(hX c hc).2, padicValRat.div (hX c hc).1 hbq, padicValRat.of_int, padicValRat.of_int]
  have m0 : ((0 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m1 : ((-15 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m2 : ((-20 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m3 : ((-24 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m4 : ((-30 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have m5 : ((-60 : ℤ) : ℚ) ∈ contactSet := by simp [contactSet]
  have n0 := (hX 0 m0).1
  have n1 := (hX (-15) m1).1
  have n2 := (hX (-20) m2).1
  have n3 := (hX (-24) m3).1
  have n4 := (hX (-30) m4).1
  have n5 := (hX (-60) m5).1
  have hv0 := vX 0 m0
  have hv1 := vX (-15) m1
  have hv2 := vX (-20) m2
  have hv3 := vX (-24) m3
  have hv4 := vX (-30) m4
  have hv5 := vX (-60) m5
  push_cast at hv0 hv1 hv2 hv3 hv4 hv5
  -- v(F) is the sum
  have hFprod : Fh a b = (a - 0 * b) * (a - -15 * b) * (a - -20 * b) * (a - -24 * b)
      * (a - -30 * b) * (a - -60 * b) := by unfold Fh; ring
  have n0' : a - 0 * b ≠ 0 := by exact_mod_cast n0
  have n1' : a - -15 * b ≠ 0 := by exact_mod_cast n1
  have n2' : a - -20 * b ≠ 0 := by exact_mod_cast n2
  have n3' : a - -24 * b ≠ 0 := by exact_mod_cast n3
  have n4' : a - -30 * b ≠ 0 := by exact_mod_cast n4
  have n5' : a - -60 * b ≠ 0 := by exact_mod_cast n5
  have c0 : ((a - 0 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n0'
  have c1 : ((a - -15 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n1'
  have c2 : ((a - -20 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n2'
  have c3 : ((a - -24 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n3'
  have c4 : ((a - -30 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n4'
  have c5 : ((a - -60 * b : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr n5'
  have hvF : (padicValInt p (Fh a b) : ℤ) = padicValInt p (a - 0 * b) + padicValInt p (a - -15 * b)
      + padicValInt p (a - -20 * b) + padicValInt p (a - -24 * b) + padicValInt p (a - -30 * b)
      + padicValInt p (a - -60 * b) := by
    simp only [← padicValRat.of_int]
    have p1 := mul_ne_zero c0 c1
    have p2 := mul_ne_zero p1 c2
    have p3 := mul_ne_zero p2 c3
    have p4 := mul_ne_zero p3 c4
    rw [hFprod, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_mul,
      padicValRat.mul p4 c5, padicValRat.mul p3 c4, padicValRat.mul p2 c3, padicValRat.mul p1 c2,
      padicValRat.mul c0 c1]
  have hv0 := vX 0 m0
  have hv1 := vX (-15) m1
  have hv2 := vX (-20) m2
  have hv3 := vX (-24) m3
  have hv4 := vX (-30) m4
  have hv5 := vX (-60) m5
  simp only [Int.cast_zero, Int.cast_neg, Int.cast_ofNat] at hv0 hv1 hv2 hv3 hv4 hv5
  simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left]
  rw [hv0, hv1, hv2, hv3, hv4, hv5, hJv, hJv']
  simp only [Int.odd_iff]
  by_cases hbp : (b : ZMod p) = 0
  · -- `p ∣ b`: `u` is not `p`-integral; `j₀ ≡ J(∞)` meets no branch point
    have ha : (a : ZMod p) ≠ 0 := by
      intro ha
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hbp
      have h1 : p ∣ u.num.natAbs := Int.natCast_dvd.mp ha
      have h2 : p ∣ u.den := Int.natCast_dvd_natCast.mp hbp
      have h3 := Nat.dvd_gcd h1 h2
      rw [u.reduced] at h3
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp h3)
    have h7 : (7 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 7 (by unfold smoothBound; norm_num)
    have h11 : (11 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 11 (by unfold smoothBound; norm_num)
    have h13 : (13 : ZMod p) ≠ 0 := by
      simpa using smooth_ne_zero (p := p) h17 13 (by unfold smoothBound; norm_num)
    have z : ∀ c : ℤ, padicValInt p (a - c * b) = 0 := by
      intro c
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; rw [hbp]; simpa using ha
    have zF : padicValInt p (Fh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Fh; push_cast; rw [hbp]; simp [ha]
    have zG : padicValInt p (Gh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Gh; push_cast; rw [hbp]; simp [ha, h7]
    have zH : padicValInt p (Hh a b) = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Hh; push_cast; rw [hbp]; simp [ha, h11, h13]
    have vb : 0 < padicValInt p b := (vpos_iff hb0).mpr hbp
    simp only [z, zF, zG, zH]
    omega
  · -- `p ∤ b`
    have vb0 : padicValInt p b = 0 := by
      by_contra h
      exact hbp ((vpos_iff hb0).mp (Nat.pos_of_ne_zero h))
    have q01 := pair_not (p := p) (x := a - 0 * b) (y := a - -15 * b) (d := 15)
      (smooth_ne_zero h17 15 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n1'] at q01
    have q02 := pair_not (p := p) (x := a - 0 * b) (y := a - -20 * b) (d := 20)
      (smooth_ne_zero h17 20 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n2'] at q02
    have q03 := pair_not (p := p) (x := a - 0 * b) (y := a - -24 * b) (d := 24)
      (smooth_ne_zero h17 24 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n3'] at q03
    have q04 := pair_not (p := p) (x := a - 0 * b) (y := a - -30 * b) (d := 30)
      (smooth_ne_zero h17 30 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n4'] at q04
    have q05 := pair_not (p := p) (x := a - 0 * b) (y := a - -60 * b) (d := 60)
      (smooth_ne_zero h17 60 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n0', ← vpos_iff n5'] at q05
    have q12 := pair_not (p := p) (x := a - -15 * b) (y := a - -20 * b) (d := 5)
      (smooth_ne_zero h17 5 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n2'] at q12
    have q13 := pair_not (p := p) (x := a - -15 * b) (y := a - -24 * b) (d := 9)
      (smooth_ne_zero h17 9 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n3'] at q13
    have q14 := pair_not (p := p) (x := a - -15 * b) (y := a - -30 * b) (d := 15)
      (smooth_ne_zero h17 15 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n4'] at q14
    have q15 := pair_not (p := p) (x := a - -15 * b) (y := a - -60 * b) (d := 45)
      (smooth_ne_zero h17 45 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n1', ← vpos_iff n5'] at q15
    have q23 := pair_not (p := p) (x := a - -20 * b) (y := a - -24 * b) (d := 4)
      (smooth_ne_zero h17 4 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n3'] at q23
    have q24 := pair_not (p := p) (x := a - -20 * b) (y := a - -30 * b) (d := 10)
      (smooth_ne_zero h17 10 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n4'] at q24
    have q25 := pair_not (p := p) (x := a - -20 * b) (y := a - -60 * b) (d := 40)
      (smooth_ne_zero h17 40 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n2', ← vpos_iff n5'] at q25
    have q34 := pair_not (p := p) (x := a - -24 * b) (y := a - -30 * b) (d := 6)
      (smooth_ne_zero h17 6 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n3', ← vpos_iff n4'] at q34
    have q35 := pair_not (p := p) (x := a - -24 * b) (y := a - -60 * b) (d := 36)
      (smooth_ne_zero h17 36 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n3', ← vpos_iff n5'] at q35
    have q45 := pair_not (p := p) (x := a - -30 * b) (y := a - -60 * b) (d := 30)
      (smooth_ne_zero h17 30 (by unfold smoothBound; norm_num)) hbp (by push_cast; ring)
    rw [← vpos_iff n4', ← vpos_iff n5'] at q45
    have bFG := bezout_not (p := p) (smooth_ne_zero h17 104976000000
      (by unfold smoothBound; norm_num)) hbp (bez_FG a b)
    have bFH := bezout_not (p := p) (smooth_ne_zero h17 680244480000000000
      (by unfold smoothBound; norm_num)) hbp (bez_FH a b)
    have bGH := bezout_not (p := p) (smooth_ne_zero h17 629856000000
      (by unfold smoothBound; norm_num)) hbp (bez_GH a b)
    rw [← vpos_iff hFh', ← vpos_iff hGh'] at bFG
    rw [← vpos_iff hFh', ← vpos_iff hHh'] at bFH
    rw [← vpos_iff hGh', ← vpos_iff hHh'] at bGH
    exact final_nat hvF vb0 q01 q02 q03 q04 q05 q12 q13 q14 q15 q23 q24 q25 q34 q35 q45 bFG bFH bGH

/-- Lemma PR(i), elementary half, in terms of `M_S(u) = ZInQ.contactSupport S u`: for a prime
`p ∉ S` (`S ⊇ {primes ≤ 324}`), the predicted inertia orders at `p` are all `1` iff `p ∤ M_S(u)`. -/
theorem inertia_trivial_iff_not_dvd (S : Finset ℕ) (hS : ∀ q, q.Prime → q ≤ 324 → q ∈ S)
    (hpS : p ∉ S) {u : ℚ} (hu : u ∉ contactSet) :
    (4 ∣ (padicValRat p (Jmap u)).toNat ∧ 6 ∣ (-padicValRat p (Jmap u)).toNat ∧
      2 ∣ (padicValRat p (Jmap u + 16 / 27)).toNat) ↔ ¬ p ∣ contactSupport S u := by
  have h17 : 17 ≤ p := by
    by_contra h
    exact hpS (hS p hp.out (by omega))
  rw [inertia_trivial_iff h17 hu, prime_dvd_contactSupport_iff hu hp.out]
  simp [hpS]

theorem div_gcd_eq_one_iff {e m : ℕ} (he : 0 < e) : e / Nat.gcd e m = 1 ↔ e ∣ m := by
  constructor
  · intro h
    have hg : Nat.gcd e m ∣ e := Nat.gcd_dvd_left e m
    have he' : e = Nat.gcd e m := by
      have := Nat.div_mul_cancel hg
      rw [h, one_mul] at this
      exact this.symm
    rw [he']
    exact Nat.gcd_dvd_right e m
  · intro h
    rw [Nat.gcd_eq_left h, Nat.div_self he]

/-- Lemma PR(i), elementary half, with Prop. TS's inertia orders `e_b / gcd(e_b, m_b)` literally. -/
theorem inertia_orders_eq_one_iff (S : Finset ℕ) (hS : ∀ q, q.Prime → q ≤ 324 → q ∈ S)
    (hpS : p ∉ S) {u : ℚ} (hu : u ∉ contactSet) :
    (4 / Nat.gcd 4 (padicValRat p (Jmap u)).toNat = 1 ∧
      6 / Nat.gcd 6 (-padicValRat p (Jmap u)).toNat = 1 ∧
      2 / Nat.gcd 2 (padicValRat p (Jmap u + 16 / 27)).toNat = 1) ↔ ¬ p ∣ contactSupport S u := by
  rw [div_gcd_eq_one_iff (by norm_num), div_gcd_eq_one_iff (by norm_num),
    div_gcd_eq_one_iff (by norm_num)]
  exact inertia_trivial_iff_not_dvd S hS hpS hu

end Valuation

/-! ### NoCM: the fibre of `X⁶ → X*` over `t(u)` (A10; rv-h-cm §2.4, §7.2 step 3)

In Elkies' model `ℚ(X⁶) = ℚ(t)(y₁, y₂)`, `y₁² = −t`, `y₂² = 3(t − 1)` (rv-h-cm §2.3; `w₂`, `w₆`,
`w₃` negate `y₂`, `y₁`, both). Over `t(u)` the four points are `(±i h₁, ±i h₂)` with
`h₁ = H/G³`, `h₂ = 540F/G³`, both nonzero: a free `W`-orbit, with coordinates in `ℚ(i)`, no
coordinate real (so the residue field is not `ℚ`), and complex conjugation acting as `w₃`. -/

open Complex in
/-- The fibre over `t(u)`: exactly the four points `(±i h₁, ±i h₂)`. -/
theorem fibre_iff (u : ℚ) (Y₁ Y₂ : ℂ) :
    (Y₁ ^ 2 = -((tq u : ℚ) : ℂ) ∧ Y₂ ^ 2 = 3 * (((tq u : ℚ) : ℂ) - 1)) ↔
    (Y₁ = I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ) ∨ Y₁ = -(I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ))) ∧
    (Y₂ = I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ) ∨ Y₂ = -(I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ))) := by
  have hG := Gq_ne_zero u
  have e1 : -((tq u : ℚ) : ℂ) = (I * ((Hq u / Gq u ^ 3 : ℚ) : ℂ)) ^ 2 := by
    rw [t_eq]; push_cast; rw [mul_pow, I_sq]; ring
  have e2 : 3 * (((tq u : ℚ) : ℂ) - 1) = (I * ((540 * Fq u / Gq u ^ 3 : ℚ) : ℂ)) ^ 2 := by
    have := t_sub_one u
    rw [show ((tq u : ℚ) : ℂ) - 1 = ((tq u - 1 : ℚ) : ℂ) by push_cast; ring, this]
    push_cast; rw [mul_pow, I_sq]; ring
  rw [e1, e2, sq_eq_sq_iff_eq_or_eq_neg, sq_eq_sq_iff_eq_or_eq_neg]

theorem h₁_ne_zero (u : ℚ) : Hq u / Gq u ^ 3 ≠ 0 :=
  div_ne_zero (Hq_ne_zero u) (pow_ne_zero _ (Gq_ne_zero u))

theorem h₂_ne_zero {u : ℚ} (hu : u ∉ contactSet) : 540 * Fq u / Gq u ^ 3 ≠ 0 :=
  div_ne_zero (mul_ne_zero (by norm_num) (Fq_ne_zero hu)) (pow_ne_zero _ (Gq_ne_zero u))

open Complex in
/-- The four points are pairwise distinct, `W` acts freely (no point has a zero coordinate),
no point has a real (a fortiori rational) coordinate, and complex conjugation acts as `w₃`
(negates both coordinates). -/
theorem fibre_free {u : ℚ} (hu : u ∉ contactSet) (Y₁ Y₂ : ℂ)
    (h : Y₁ ^ 2 = -((tq u : ℚ) : ℂ) ∧ Y₂ ^ 2 = 3 * (((tq u : ℚ) : ℂ) - 1)) :
    Y₁ ≠ -Y₁ ∧ Y₂ ≠ -Y₂ ∧ Y₁.im ≠ 0 ∧ Y₂.im ≠ 0 ∧
      (starRingEnd ℂ Y₁ = -Y₁ ∧ starRingEnd ℂ Y₂ = -Y₂) := by
  have n1 := h₁_ne_zero u
  have n2 := h₂_ne_zero hu
  obtain ⟨h1, h2⟩ := (fibre_iff u Y₁ Y₂).mp h
  have k1 : Y₁.re = 0 ∧ Y₁.im ≠ 0 := by
    clear h h2
    generalize Hq u / Gq u ^ 3 = r at h1 n1
    rcases h1 with rfl | rfl <;> simp [n1]
  have k2 : Y₂.re = 0 ∧ Y₂.im ≠ 0 := by
    clear h h1 k1
    generalize 540 * Fq u / Gq u ^ 3 = r at h2 n2
    rcases h2 with rfl | rfl <;> simp [n2]
  refine ⟨fun e => k1.2 ?_, fun e => k2.2 ?_, k1.2, k2.2, ?_, ?_⟩
  · have := congrArg Complex.im e; simp at this; linarith
  · have := congrArg Complex.im e; simp at this; linarith
  · apply Complex.ext <;> simp [k1.1]
  · apply Complex.ext <;> simp [k2.1]

end GlueRepo.PR


end RepoPRArithSec

section RepoNumericsSec
/-! ### Copied from `scratch/glue-repo/Numerics.lean` (compiled there). -/

/-!
# glue-repo, steps A3, A5 and A8: the numerical bookkeeping

* `a3_numerals`: `4·|(𝒪/3𝒪)^*| = 4·72 ≤ 4·81 = 324`, and `|Γ'| = 4·72/2 = 144 = 2⁴3²`
  (N5 L436-441; h-b1 M3). The count `|(𝒪/3𝒪)^*| = 72` is `GlueRepo.A1.card_units_mod3`.
* `splitting_degree_le`: a separable polynomial over `ℚ` of degree `≤ 324` has splitting field of
  degree `≤ 324! = F₀` (N5 L524-526: `[K:ℚ] ≤ F₀`).
* `a8_rank`, `a8_degree`, `a8_field`: `r ≤ 16F₀²` and `[EK:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D`
  (N5 L544-555), for variables `F₀`, `D = F₀·3^{256F₀⁴}` (the bodies of `ZInQ.heightF0`,
  `ZInQ.heightD`; the kernel cannot unfold those constants, see `HeightConstant.lean`).
-/

open ZInQ Module Polynomial

namespace GlueRepo.Numerics

theorem a3_numerals : 4 * 72 ≤ 4 * 81 ∧ 4 * 81 = 324 ∧ 4 * 72 / 2 = 144 ∧ 144 = 2 ^ 4 * 3 ^ 2 := by
  norm_num

/-- `[K:ℚ] ≤ F₀`: the Galois group of a separable polynomial of degree `≤ 324` embeds in the
permutations of its roots. -/
theorem splitting_degree_le (f : ℚ[X]) (hs : f.Separable) (hd : f.natDegree ≤ 324) :
    finrank ℚ f.SplittingField ≤ Nat.factorial 324 := by
  rw [← Polynomial.Gal.card_of_separable hs]
  have : Fact ((f.map (algebraMap ℚ f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
        Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
    _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
    _ ≤ Nat.factorial 324 := by
        apply Nat.factorial_le
        rw [Nat.card_coe_set_eq]
        exact (Polynomial.ncard_rootSet_le f _).trans hd

/-- `r ≤ 16F₀²`: `W₀ = Res_{K/ℚ} A` has `[K:ℚ]² ≤ F₀²` ordered Hom groups between conjugates,
each of rank `≤ 4·dim·dim = 16` (Mumford §19 Thm 3). Stated for a variable `F₀` (the kernel
must not evaluate `324!`); apply with `F₀ = ZInQ.heightF0`. -/
theorem a8_rank {F0 d r : ℕ} (hd : d ≤ F0) (hr : r ≤ d ^ 2 * (4 * 2 * 2)) :
    r ≤ 16 * F0 ^ 2 := by
  calc r ≤ d ^ 2 * (4 * 2 * 2) := hr
    _ ≤ F0 ^ 2 * 16 := Nat.mul_le_mul (Nat.pow_le_pow_left hd 2) (by norm_num)
    _ = 16 * F0 ^ 2 := by ring

/-- `F₀·3^{r²} ≤ D` when `r ≤ 16F₀²`, for `D = F₀·3^{256F₀⁴}` (`ZInQ.heightD`'s body). -/
theorem a8_degree {F0 D k e r : ℕ} (hD : D = F0 * 3 ^ (256 * F0 ^ 4)) (hk : k ≤ F0)
    (he : e ≤ 3 ^ (r ^ 2)) (hr : r ≤ 16 * F0 ^ 2) : k * e ≤ D := by
  rw [hD]
  have h2 : r ^ 2 ≤ 256 * F0 ^ 4 :=
    calc r ^ 2 ≤ (16 * F0 ^ 2) ^ 2 := Nat.pow_le_pow_left hr 2
      _ = 256 * F0 ^ 4 := by ring
  calc k * e ≤ F0 * 3 ^ (r ^ 2) := Nat.mul_le_mul hk he
    _ ≤ F0 * 3 ^ (256 * F0 ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h2)

/-- `[L:ℚ] ≤ D` for the Hom field `L = EK` (N5 L554-555). -/
theorem a8_field {M : Type*} [Field M] [Algebra ℚ M] (E K : IntermediateField ℚ M)
    {F0 D r : ℕ} (hD : D = F0 * 3 ^ (256 * F0 ^ 4))
    (hK : finrank ℚ K ≤ F0) (hE : finrank ℚ E ≤ 3 ^ (r ^ 2))
    (hr : r ≤ 16 * F0 ^ 2) : finrank ℚ ↥(E ⊔ K) ≤ D :=
  (IntermediateField.finrank_sup_le E K).trans (by rw [mul_comm]; exact a8_degree hD hK hE hr)

end GlueRepo.Numerics


end RepoNumericsSec

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

/-- **T29. Local normalizers of maximal orders.** For a quaternion algebra `B_p` over `ℚ_p` and a
maximal order `𝒪_p`, the group `N(𝒪_p)/ℚ_p^×𝒪_p^×` has order 2 if `B_p` is a division algebra
(generated by a uniformizer of `B_p`) and order 1 if `B_p ≅ M₂(ℚ_p)` (`N(M₂(ℤ_p)) = ℚ_p^×GL₂(ℤ_p)`);
for `B = (2,−3)` (ramified at 2, 3) this gives the normalizer index 4 of A3 (Vignéras, LNM 800,
Ch. II, UNVERIFIED). Statable over Mathlib's quaternion algebras (pkg-I1 I1-f), not drafted. -/
opaque T29_LocalNormalizers : Prop

/-- **T32. Tame inertia and quadratic characters** (glue-descent L-B3a, L-B3b). (a) The tame
inertia group of `ℚ_p`, `p` odd, has a unique continuous character of order 2; (b) a quadratic
Dirichlet character is ramified exactly at the primes dividing its conductor (Serre, *Local fields*
IV §2; Neukirch; UNVERIFIED). Used only for the unramifiedness of `L'`. Missing: inertia subgroups
of `G_ℚ` as subgroups of `Field.absoluteGaloisGroup ℚ` (cheap). -/
opaque T32_TameQuadratic : Prop

/-! ## §3. Glue -/

/-- **G12, weight arithmetic** (N5 L763-764, Tate normalization; from the hdec-faithful draft). -/
theorem weight_match (n k : ℤ) (hk : 1 ≤ k)
    (h : (n = 0 ∧ n + 1 - k = -1) ∨ (n = -1 ∧ n + 1 - k = 0)) : n = 0 ∧ k = 2 := by
  omega

/-- **G15 (D3), pkg-I6's `sq_principalUnits` proved** from glue-conductor's
`exists_sq_eq_one_add` (same statement as `PkgI6.sq_principalUnits`, which is `sorry` there). -/
theorem sq_principalUnits_proved (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] (e : ℕ) (_he1 : 1 ≤ e)
    (he : Ideal.span {(2 : B)} = IsLocalRing.maximalIdeal B ^ e) (r : ℕ) (hr : e < r)
    (y : B) (hy : y ∈ IsLocalRing.maximalIdeal B ^ (r + e)) :
    ∃ x ∈ IsLocalRing.maximalIdeal B ^ r, (1 + x) ^ 2 = 1 + y := by
  obtain ⟨w, hw, h⟩ := GlueConductor.exists_sq_eq_one_add e (r - e) (by omega) he y
    (by rwa [show 2 * e + (r - e) = r + e by omega])
  exact ⟨w, by rwa [show e + (r - e) = r by omega] at hw, h⟩

/-- **The research-level leaves of route P** (note §2.1), bundled. Placeholders are
uninterpreted. Genuine statements: `R4` (pkg-I1), `R6`, `R7` (pkg-I2), `R9` (pkg-I3), `R10`,
`R11`+`R12`, `R13` (pkg-I4), `R14`, `R15` (§1 here). -/
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
  r10 : PkgI4.DeRhamComparison
  /-- R11 (Berger) and R12 (Pan) enter through their joint consequence: Pan's theorem with "de Rham
  at `p`" in place of "potentially semistable at `p`" (pkg-I4). `B_st` is not needed by the glue.
  Both theorems remain separate leaves in the count. -/
  r11r12 : PkgI4.PanBerger
  r13 : PkgI4.EigenformHT
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
  t25 : PkgI4.NewformOfEigenform
  t26 : PkgI3.TateModuleFree
  t27 : PkgI3.QMDichotomy
  t28 : PkgI1.IgusaClebschSeparation
  t29 : T29_LocalNormalizers
  t30 : GlueDescent.B2Q.LeafSqrtCrit
  t31 : GlueDescent.B2Q.LeafUnramified
  t32 : T32_TameQuadratic

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
#print axioms GlueDescent.B3Q.b3_degree_le_QM
#print axioms GlueRepo.PR.inertia_orders_eq_one_iff
#print axioms GlueRepo.PR.fibre_free
#print axioms HSyn.sq_principalUnits_proved
#print axioms HSyn.sixContactMin_of_leaves

/-! rv-hsyn: extra axiom checks for theorems the note calls proved but the file does not print,
and confirmation of the sorry locations. -/
#print axioms PkgI1.gram_det
#print axioms PkgI1.cm4
#print axioms PkgI1.cm24
#print axioms PkgI1.G6_sub_F2
#print axioms PkgI1.Ju_ne_branch
#print axioms PkgI1.elkies_t
#print axioms PkgI1.elkies_t_sub_one
#print axioms PkgI1.thetaRatio_invariant
#print axioms GlueAssembly.logHeight_Phi_le
#print axioms GlueAssembly.transfer_of_level
#print axioms GlueAssembly.weight_match_coh
#print axioms GlueAssembly.sixContactMinAt_of_glueOutputs
#print axioms PkgI3.range_tateHomZl_subset
#print axioms GlueDescent.B2Q.b2_of_leaves
#print axioms GlueConductor.exists_sq_eq_one_add
#print axioms PkgI2.goodReduction_of_QM_rational3
#print axioms PkgI6.artinConductor_le_of_upper
#print axioms PkgI6.sq_principalUnits
#print axioms HSyn.glueOutputs_of_leaves
example : HSyn.ResearchLeaves → HSyn.TextbookLeaves → ZInQ.SixContactMin := HSyn.sixContactMin_of_leaves
