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

The only `sorry` in the file is `glueOutputs_of_leaves` (hsyn-fix, after the reviews): A6
(`PkgI2.goodReduction_of_QM_rational3`, rv-a6-route), D4 (`PkgI6.artinConductor_le_of_upper`,
glue-I6-rest) and D3 (`PkgI6.sq_principalUnits`) are now proved. Their remaining assumptions are
explicit hypotheses: the glue Prop `PkgI2.QuatUnipotentTrivial` (pure algebra, paper proof in
rv-a6-route §3) for A6, and the glue Prop `GlueI3.SemisimpleBaseChange` (standard algebra) for
glue-I3-linalg's `PkgI3.C2_absolutelyIrreducible` and `PkgI3.E1_exists_hom_ne_zero`.
`scratch/hsyn/assemble.py` no longer reproduces this file (hsyn-fix edited it by hand).

hsyn-fold (2026-11-12) added, each in its own section: `GlueA6Alg.Alg` and
`PkgI2.quatUnipotentTrivial` (glue-a6-alg; A6 now needs only its three leaves, and
`PkgI2.QuatUnipotentTrivial` is no longer a hypothesis anywhere), `PkgI3.trace_indep_of_ell` and
`GlueC10` (glue-c10), `GlueD1Local` (glue-d1-local), `LeafPush` and `PkgI4.T23_FontaineClosure`
(leaf-push; the five placeholders R8, T9, T23, T29, T32 are replaced in the bundles), and
obj-bridge's §C-§E as `ObjBridge` (its §F does not compile here; see the comment there). The
paragraph above is otherwise as hsyn-fix left it: the only remaining glue Prop hypothesis is
`GlueI3.SemisimpleBaseChange`.

leaf-adopt (2026-11-12) added, each in its own section after `LeafPushSec`: `GlueT32aSec`
(glue-t32a with glue-b3b: T32 is proved glue, `HSyn.t32a_glue`, `t32b_glue`), `LeafQMSec`
(leaf-qm-fp: R1 (a), (c), (d), R2, R5 in field-point form), `LeafModCurvesSec` (leaf-modcurves: R16,
`JacobianExists` = T33, `DimJ1Genus` = T34), `DefFaltingsSec` (def-faltings: the stable Faltings
height, R19-R21), and `LeafAdoptSec` (rv-blueprints' repairs Q2, Q4, Q5, M1, F2: `R1R2fpRep`,
`R1pi0Props`, `R2X6PropsIff`, `R5fpStrong`, `H5`, and the bridge `abVarEquiv`). The placeholders
are now R1(b), R3, R17, R18, R22, T10-T12 (8 `opaque`). The Shimura-curve leaves rest on the
SPECULATIVE premise bp-qmmoduli §2.2, and the height leaves are not yet known to be non-vacuous
(AN3 open); see the docstrings and `docs/research/leaf-adopt.md`.

No `axiom` declarations. Leaf numbering (R1-R22 and H5 research-level, T1-T34 textbook, T32 now
glue) is that of the note's §2.
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

section GlueA6AlgSec
/-! ### Copied from `scratch/glue-a6-alg/A6.lean` lines 47-521 (compiled there; hsyn-fold). -/

namespace GlueA6Alg.Alg

lemma three_prime : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three

lemma dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (3 : ℤ) ∣ 2 * a * y) : (3 : ℤ) ∣ y := by
  rcases three_prime.dvd_or_dvd h with h' | h'
  · rcases three_prime.dvd_or_dvd h' with h'' | h''
    · norm_num at h''
    · exact absurd h'' ha
  · exact h'

lemma nine_dvd_of_dvd_two_mul {a y : ℤ} (ha : ¬ (3 : ℤ) ∣ a) (h : (9 : ℤ) ∣ 2 * a * y) :
    (9 : ℤ) ∣ y := by
  have h3 : (3 : ℤ) ∣ y := dvd_of_dvd_two_mul ha (dvd_trans ⟨3, by norm_num⟩ h)
  obtain ⟨y', rfl⟩ := h3
  have h' : (3 : ℤ) ∣ 2 * a * y' := by
    have : (3 : ℤ) * 3 ∣ 3 * (2 * a * y') := by
      have e : (3 : ℤ) * (2 * a * y') = 2 * a * (3 * y') := by ring
      rw [e]; simpa using h
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have := dvd_of_dvd_two_mul ha h'
  obtain ⟨z, rfl⟩ := this
  exact ⟨z, by ring⟩

lemma zmod3_aniso : ∀ x y : ZMod 3, 2 * y ^ 2 - x ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

/-- Base case: `9 ∣` every coordinate of `x²` implies `3 ∣` every coordinate of `x`. -/
lemma quat_base (a b c d : ℤ) (h1 : (9 : ℤ) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2)
    (h2 : (9 : ℤ) ∣ 2 * a * b) (h3 : (9 : ℤ) ∣ 2 * a * c) (h4 : (9 : ℤ) ∣ 2 * a * d) :
    (3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b ∧ (3 : ℤ) ∣ c ∧ (3 : ℤ) ∣ d := by
  have ha : (3 : ℤ) ∣ a := by
    by_contra ha
    have hb := nine_dvd_of_dvd_two_mul ha h2
    have hc := nine_dvd_of_dvd_two_mul ha h3
    have hd := nine_dvd_of_dvd_two_mul ha h4
    have e : a ^ 2 = (a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - (2 * b) * b + (3 * c) * c
        - (6 * d) * d := by ring
    have h9 : (9 : ℤ) ∣ a ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub h1 (Dvd.dvd.mul_left hb _)) (Dvd.dvd.mul_left hc _))
        (Dvd.dvd.mul_left hd _)
    exact ha (three_prime.dvd_of_dvd_pow (dvd_trans ⟨3, by norm_num⟩ h9))
  obtain ⟨a', rfl⟩ := ha
  have hb : (3 : ℤ) ∣ b := by
    have e : 2 * b ^ 2 = ((3 * a') ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2) - 3 * (3 * a' ^ 2)
        + 3 * (c ^ 2) - 3 * (2 * d ^ 2) := by ring
    have h3b : (3 : ℤ) ∣ 2 * b ^ 2 := by
      rw [e]
      exact dvd_sub (dvd_add (dvd_sub (dvd_trans ⟨3, by norm_num⟩ h1) (dvd_mul_right _ _))
        (dvd_mul_right _ _)) (dvd_mul_right _ _)
    rcases three_prime.dvd_or_dvd h3b with h | h
    · norm_num at h
    · exact three_prime.dvd_of_dvd_pow h
  obtain ⟨b', rfl⟩ := hb
  have hcd : (3 : ℤ) ∣ 2 * d ^ 2 - c ^ 2 := by
    have e : (3 : ℤ) * (2 * d ^ 2 - c ^ 2) = ((3 * a') ^ 2 + 2 * (3 * b') ^ 2 - 3 * c ^ 2
        + 6 * d ^ 2) - 9 * (a' ^ 2 + 2 * b' ^ 2) := by ring
    have : (3 : ℤ) * 3 ∣ 3 * (2 * d ^ 2 - c ^ 2) := by
      rw [e]; exact dvd_sub (by simpa using h1) (dvd_mul_right _ _)
    exact (mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0)).mp this
  have hz : (((2 * d ^ 2 - c ^ 2 : ℤ)) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast hcd)
  push_cast at hz
  obtain ⟨hc0, hd0⟩ := zmod3_aniso _ _ hz
  refine ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ?_, ?_⟩
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd c 3).mp hc0
  · exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd d 3).mp hd0

/-- **Valuation step (proved).** If `3^{2k}` divides every coordinate of
`(a + bi + cj + d·ij)²` in `Λ = ℤ⟨i,j⟩`, then `3^k` divides `a, b, c, d`. -/
theorem quat_sq_dvd (k : ℕ) : ∀ a b c d : ℤ,
    (3 : ℤ) ^ (2 * k) ∣ a ^ 2 + 2 * b ^ 2 - 3 * c ^ 2 + 6 * d ^ 2 →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * b → (3 : ℤ) ^ (2 * k) ∣ 2 * a * c →
    (3 : ℤ) ^ (2 * k) ∣ 2 * a * d →
    (3 : ℤ) ^ k ∣ a ∧ (3 : ℤ) ^ k ∣ b ∧ (3 : ℤ) ^ k ∣ c ∧ (3 : ℤ) ^ k ∣ d := by
  induction k with
  | zero => intros; simp
  | succ k ih =>
    intro a b c d h1 h2 h3 h4
    have e9 : (3 : ℤ) ^ (2 * (k + 1)) = 9 * 3 ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]; norm_num; ring
    rw [e9] at h1 h2 h3 h4
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩ :=
      quat_base a b c d (dvd_of_mul_right_dvd h1) (dvd_of_mul_right_dvd h2)
        (dvd_of_mul_right_dvd h3) (dvd_of_mul_right_dvd h4)
    have cancel : ∀ z : ℤ, 9 * 3 ^ (2 * k) ∣ 9 * z → 3 ^ (2 * k) ∣ z := fun z hz =>
      (mul_dvd_mul_iff_left (by norm_num : (9 : ℤ) ≠ 0)).mp hz
    have := ih a' b' c' d'
      (cancel _ (by convert h1 using 1; ring)) (cancel _ (by convert h2 using 1; ring))
      (cancel _ (by convert h3 using 1; ring)) (cancel _ (by convert h4 using 1; ring))
    obtain ⟨⟨a'', rfl⟩, ⟨b'', rfl⟩, ⟨c'', rfl⟩, ⟨d'', rfl⟩⟩ := this
    exact ⟨⟨a'', by ring⟩, ⟨b'', by ring⟩, ⟨c'', by ring⟩, ⟨d'', by ring⟩⟩


/-! ## 2. Independence over `𝔽₃` -/

lemma f3_aniso : ∀ a b : ZMod 3, a ^ 2 - 2 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide

/-- Over `𝔽₃`: if `I² = 2`, `J² = 0`, `JI = -IJ` and `Jx ≠ 0`, then `x, Ix, Jx, IJx` are
linearly independent (because `a² - 2b²` is anisotropic mod 3). -/
lemma f3_indep {M : Type*} [AddCommGroup M] [Module (ZMod 3) M] (I J : M →ₗ[ZMod 3] M)
    (hI : ∀ y, I (I y) = (2 : ZMod 3) • y) (hJ : ∀ y, J (J y) = 0)
    (hIJ : ∀ y, J (I y) = -I (J y)) (x : M) (hx : J x ≠ 0) :
    LinearIndependent (ZMod 3) ![x, I x, J x, I (J x)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hg
  have h1 : g 0 • J x - g 1 • I (J x) = 0 := by
    have := congrArg J hg
    simp only [map_add, map_smul, hJ, hIJ, map_zero, smul_neg, smul_zero,
      add_zero] at this
    linear_combination (norm := module) this
  have h2 : g 0 • I (J x) - g 1 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I h1
    simp only [map_sub, map_smul, hI, map_zero] at this
    exact this
  have k1 : (g 0 ^ 2 - 2 * g 1 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 0 • h1 + g 1 • h2
  obtain ⟨g0, g1⟩ := f3_aniso _ _ ((smul_eq_zero.mp k1).resolve_right hx)
  rw [g0, g1, zero_smul, zero_smul, zero_add, zero_add] at hg
  have h3 : g 2 • I (J x) + g 3 • (2 : ZMod 3) • J x = 0 := by
    have := congrArg I hg
    simp only [map_add, map_smul, hI, map_zero] at this
    exact this
  have k2 : (g 2 ^ 2 - 2 * g 3 ^ 2) • J x = 0 := by
    linear_combination (norm := module) g 2 • hg - g 3 • h3
  obtain ⟨g2, g3⟩ := f3_aniso _ _ ((smul_eq_zero.mp k2).resolve_right hx)
  intro i
  fin_cases i <;> assumption

/-! ## 3. The core: `T ≅ (ℤ/3^{2k})⁴` is cyclic over `Λ`, and `S - 1` is divisible by `3^k` -/

section Core

variable (k : ℕ)

abbrev Q : ℕ := 3 ^ (2 * k)

instance : NeZero (Q k) := ⟨by positivity⟩

abbrev R := ZMod (Q k)

abbrev V := Fin 4 → R k

variable {k}

/-- `φ y a = a₀ y + a₁ I y + a₂ J y + a₃ I J y`: the orbit map `Λ/q → T` at `y`. -/
def φ (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) : V k :=
  a 0 • y + a 1 • I y + a 2 • J y + a 3 • I (J y)

lemma φ_add_smul (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) (c : R k) :
    φ I J y (a + c • b) = φ I J y a + c • φ I J y b := by
  simp only [φ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; module

lemma φ_smul (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J y (c • a) = c • φ I J y a := by
  simp only [φ, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub (I J : V k →ₗ[R k] V k) (y : V k) (a b : Fin 4 → R k) :
    φ I J y (a - b) = φ I J y a - φ I J y b := by
  simp only [φ, Pi.sub_apply]; module

lemma φ_zero (I J : V k →ₗ[R k] V k) (y : V k) : φ I J y 0 = 0 := by
  simp [φ]

lemma φ_smul_left (I J : V k →ₗ[R k] V k) (y : V k) (a : Fin 4 → R k) (c : R k) :
    φ I J (c • y) a = φ I J y (c • a) := by
  simp only [φ, map_smul, Pi.smul_apply, smul_eq_mul]; module

lemma φ_sub_left (I J : V k →ₗ[R k] V k) (y z : V k) (a : Fin 4 → R k) :
    φ I J (y - z) a = φ I J y a - φ I J z a := by
  simp only [φ, map_sub]; module

lemma Q_natCast : ((Q k : ℕ) : R k) = 0 := ZMod.natCast_self _

lemma three_pow_eq_zero : (3 : R k) ^ (2 * k) = 0 := by
  have := Q_natCast (k := k); push_cast [Q] at this; exact this

lemma three_dvd_Q (hk : 1 ≤ k) : 3 ∣ Q k := dvd_pow_self 3 (by omega)

lemma nine_dvd_Q (hk : 1 ≤ k) : 9 ∣ Q k := by
  have : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [this]; exact pow_dvd_pow 3 (by omega)

/-- If `z ≡ 0 (mod 3)` then `z = 3y`. -/
lemma eq_three_mul_of_cast_eq_zero (hk : 1 ≤ k) (z : R k)
    (hz : ZMod.castHom (three_dvd_Q hk) (ZMod 3) z = 0) : ∃ y : R k, z = 3 * y := by
  have h0 : ((z.val : ℕ) : ZMod 3) = 0 := by
    rw [← map_natCast (ZMod.castHom (three_dvd_Q hk) (ZMod 3)), ZMod.natCast_zmod_val]; exact hz
  obtain ⟨m, hm⟩ := (ZMod.natCast_eq_zero_iff _ _).mp h0
  refine ⟨(m : R k), ?_⟩
  rw [← ZMod.natCast_zmod_val z, hm]; push_cast; ring

/-- Coordinatewise reduction mod 3. -/
def red (hk : 1 ≤ k) (v : V k) : Fin 4 → ZMod 3 := fun i => ZMod.castHom (three_dvd_Q hk) (ZMod 3) (v i)

lemma red_add (hk : 1 ≤ k) (v w : V k) : red hk (v + w) = red hk v + red hk w := by
  funext i; simp only [red, Pi.add_apply, map_add]

lemma red_sub (hk : 1 ≤ k) (v w : V k) : red hk (v - w) = red hk v - red hk w := by
  funext i; simp only [red, Pi.sub_apply, map_sub]

lemma red_neg (hk : 1 ≤ k) (v : V k) : red hk (-v) = -red hk v := by
  funext i; simp only [red, Pi.neg_apply, map_neg]

lemma red_smul (hk : 1 ≤ k) (c : R k) (v : V k) :
    red hk (c • v) = ZMod.castHom (three_dvd_Q hk) (ZMod 3) c • red hk v := by
  funext i; simp only [red, Pi.smul_apply, smul_eq_mul, map_mul]

lemma eq_three_smul_of_red_eq_zero (hk : 1 ≤ k) (v : V k) (hv : red hk v = 0) :
    ∃ u : V k, v = (3 : R k) • u := by
  have h := fun i => eq_three_mul_of_cast_eq_zero hk (v i) (congrFun hv i)
  choose u hu using h
  exact ⟨u, funext fun i => by simpa using hu i⟩

/-- Lift of a vector mod 3. -/
def lift3 (y : Fin 4 → ZMod 3) : V k := fun i => ((y i).val : R k)

lemma red_lift3 (hk : 1 ≤ k) (y : Fin 4 → ZMod 3) : red hk (lift3 y) = y := by
  funext i; simp [red, lift3]

/-- The reduction of a linear map, as a matrix over `𝔽₃`. -/
noncomputable def redMap (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) :
    (Fin 4 → ZMod 3) →ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.mulVecLin ((LinearMap.toMatrix' f).map (ZMod.castHom (three_dvd_Q hk) (ZMod 3)))

lemma red_map (hk : 1 ≤ k) (f : V k →ₗ[R k] V k) (v : V k) :
    red hk (f v) = redMap hk f (red hk v) := by
  funext i
  simp only [red, redMap, Matrix.mulVecLin_apply]
  rw [← LinearMap.toMatrix'_mulVec f v, RingHom.map_mulVec]
  rfl

/-- **Core (proved).** On `V = (ℤ/3^{2k})⁴` (`k ≥ 1`), let `I, J, S` be endomorphisms with
`I² = 2`, `J² = -3`, `JI = -IJ`, `S` commuting with `I, J` and `(S - 1)² = 0`. Then `S` is the
identity on the `3^k`-torsion. (rv-a6-route §3 steps 1-5: `V` is cyclic over `Λ` with generator
`x` (any `x` with `Jx ≢ 0 mod 3`), `S x - x = c·x` with `c² = 0` in `Λ/3^{2k}`, so `c ∈ 3^kΛ`.) -/
theorem core (hk : 1 ≤ k) (I J S : V k →ₗ[R k] V k)
    (hI : ∀ v, I (I v) = (2 : R k) • v) (hJ : ∀ v, J (J v) = (-3 : R k) • v)
    (hIJ : ∀ v, J (I v) = -I (J v))
    (hSI : ∀ v, S (I v) = I (S v)) (hSJ : ∀ v, S (J v) = J (S v))
    (hS : ∀ v, S (S v) - (2 : R k) • S v + v = 0) :
    ∀ v, (3 : R k) ^ k • v = 0 → S v = v := by
  -- the reduced relations over `𝔽₃`
  have hIb : ∀ y, redMap hk I (redMap hk I y) = (2 : ZMod 3) • y := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hI, red_smul, map_ofNat]
  have hJb : ∀ y, redMap hk J (redMap hk J y) = 0 := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, hJ, red_smul]
    have : ZMod.castHom (three_dvd_Q hk) (ZMod 3) (-3 : R k) = 0 := by
      rw [map_neg, map_ofNat]; decide
    rw [this, zero_smul]
  have hIJb : ∀ y, redMap hk J (redMap hk I y) = -redMap hk I (redMap hk J y) := by
    intro y
    rw [← red_lift3 hk y, ← red_map, ← red_map, ← red_map, ← red_map, hIJ, red_neg]
  -- step 1: some `x` has `J x ≢ 0 (mod 3)`
  have hex : ∃ x : V k, red hk (J x) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu⟩ := eq_three_smul_of_red_eq_zero hk _ (h (Pi.single (0 : Fin 4) (1 : R k)))
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ (h u)
    have e := hJ (Pi.single (0 : Fin 4) (1 : R k))
    rw [hu, map_smul, hu', smul_smul] at e
    have e0 := congrFun e 0
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at e0
    have e9 := congrArg (ZMod.castHom (nine_dvd_Q hk) (ZMod 9)) e0
    simp only [map_mul, map_neg, map_ofNat] at e9
    have h9 : ∀ z : ZMod 9, 3 * 3 * z ≠ -3 := by decide
    exact h9 _ e9
  obtain ⟨x, hx⟩ := hex
  have hx' : redMap hk J (red hk x) ≠ 0 := by rwa [← red_map]
  -- step 2: `x, Ix, Jx, IJx` span `V/3V`
  have hli := f3_indep (redMap hk I) (redMap hk J) hIb hJb hIJb (red hk x) hx'
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp)
  have mod3 : ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k, u = φ I J x a + (3 : R k) • u' := by
    intro u
    have hu : red hk u ∈ Submodule.span (ZMod 3) (Set.range ![red hk x, redMap hk I (red hk x),
        redMap hk J (red hk x), redMap hk I (redMap hk J (red hk x))]) := by
      rw [hspan]; trivial
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hu
    refine ⟨fun i => ((g i).val : R k), ?_⟩
    have hred : red hk (u - φ I J x (fun i => ((g i).val : R k))) = 0 := by
      rw [red_sub, ← hg, sub_eq_zero]
      simp only [φ, red_add, red_smul, red_map, Fin.sum_univ_four, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
        Matrix.tail_cons, map_natCast, ZMod.natCast_zmod_val]
    obtain ⟨u', hu'⟩ := eq_three_smul_of_red_eq_zero hk _ hred
    exact ⟨u', by rw [← hu']; abel⟩
  -- step 2': Nakayama, `V = Λ x`
  have nak : ∀ n : ℕ, ∀ u : V k, ∃ a : Fin 4 → R k, ∃ u' : V k,
      u = φ I J x a + (3 : R k) ^ n • u' := by
    intro n
    induction n with
    | zero => intro u; exact ⟨0, u, by rw [φ_zero, pow_zero, one_smul, zero_add]⟩
    | succ n ih =>
      intro u
      obtain ⟨a, u', h⟩ := ih u
      obtain ⟨b, u'', h'⟩ := mod3 u'
      refine ⟨a + (3 : R k) ^ n • b, u'', ?_⟩
      rw [φ_add_smul, h, h', pow_succ]; module
  have hsurj : Function.Surjective (φ I J x) := by
    intro u
    obtain ⟨a, u', h⟩ := nak (2 * k) u
    exact ⟨a, by rw [h, three_pow_eq_zero, zero_smul, add_zero]⟩
  have hinj : Function.Injective (φ I J x) := Finite.injective_iff_surjective.mpr hsurj
  have hinj0 : ∀ a, φ I J x a = 0 → a = 0 := fun a ha => hinj (by rw [ha, φ_zero])
  -- step 3: `S x - x = c x` with `c² = 0`
  have hSφ : ∀ y a, S (φ I J y a) = φ I J (S y) a := by
    intro y a; simp only [φ, map_add, map_smul, hSI, hSJ]
  obtain ⟨a, ha⟩ := hsurj (S x - x)
  have hsq : φ I J (φ I J x a) a = φ I J x ![a 0 ^ 2 + 2 * a 1 ^ 2 - 3 * a 2 ^ 2 + 6 * a 3 ^ 2,
      2 * a 0 * a 1, 2 * a 0 * a 2, 2 * a 0 * a 3] := by
    simp only [φ, map_add, map_smul, map_neg, hI, hJ, hIJ, smul_neg, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    module
  have hNN : φ I J (φ I J x a) a = 0 := by
    rw [ha, φ_sub_left, ← hSφ, ha, map_sub]
    linear_combination (norm := module) hS x
  have hc := hinj0 _ (hsq ▸ hNN)
  have c0 := congrFun hc 0
  have c1 := congrFun hc 1
  have c2 := congrFun hc 2
  have c3 := congrFun hc 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply] at c0 c1 c2 c3
  -- step 4: `c ∈ 3^k Λ` (`quat_sq_dvd`)
  have hdvd : ∀ z : ℤ, (z : R k) = 0 → (3 : ℤ) ^ (2 * k) ∣ z := by
    intro z hz
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa [Q] using this
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, ⟨D, hD⟩⟩ := quat_sq_dvd k ((a 0).val : ℤ) ((a 1).val : ℤ)
    ((a 2).val : ℤ) ((a 3).val : ℤ)
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c0))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c1))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c2))
    (hdvd _ (by push_cast [ZMod.natCast_zmod_val]; exact c3))
  have lift : ∀ (i : Fin 4) (E : ℤ), ((a i).val : ℤ) = 3 ^ k * E → a i = (3 : R k) ^ k * (E : R k) := by
    intro i E h
    have := congrArg (fun z : ℤ => (z : R k)) h
    push_cast [ZMod.natCast_zmod_val] at this
    exact this
  have ha' : a = (3 : R k) ^ k • ![(A : R k), (B : R k), (C : R k), (D : R k)] := by
    funext i
    fin_cases i
    · simpa using lift 0 A hA
    · simpa using lift 1 B hB
    · simpa using lift 2 C hC
    · simpa using lift 3 D hD
  -- step 5: `S - 1` kills the `3^k`-torsion
  intro v hv
  obtain ⟨α, rfl⟩ := hsurj v
  have hα : (3 : R k) ^ k • α = 0 := hinj0 _ (by rw [φ_smul]; exact hv)
  have hNv : S (φ I J x α) - φ I J x α = 0 := by
    rw [hSφ, ← φ_sub_left, ← ha, ha', φ_smul, φ_smul_left, hα, φ_zero]
  exact sub_eq_zero.mp hNv

end Core


/-! ## 4. Transport from a commutative group with `G[3^{2k}] ≅ (ℤ/3^{2k})⁴` -/

section Transport

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*} [AddCommGroup M]
  (e : {x : G | x ^ q = 1} ≃ M)

open Classical in
/-- `e` extended by `0` off the `q`-torsion. -/
noncomputable def E (g : G) : M := if h : g ^ q = 1 then e ⟨g, h⟩ else 0

lemma E_mem (g : G) (h : g ^ q = 1) : E e g = e ⟨g, h⟩ := by
  simp only [E, h, dite_true]

lemma E_symm (v : M) : E e (e.symm v).1 = v := by
  rw [E_mem e _ (e.symm v).2]; simp

lemma symm_E (g : G) (h : g ^ q = 1) : (e.symm (E e g)).1 = g := by
  rw [E_mem e g h, Equiv.symm_apply_apply]

lemma E_inj (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) (h : E e a = E e b) : a = b := by
  rw [E_mem e a ha, E_mem e b hb] at h
  exact congrArg Subtype.val (e.injective h)

lemma mem_map (f : G →* G) (a : G) (ha : a ^ q = 1) : (f a) ^ q = 1 := by
  rw [← map_pow, ha, map_one]

lemma mem_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : (a * b) ^ q = 1 := by
  rw [mul_pow, ha, hb, one_mul]

lemma mem_inv (a : G) (ha : a ^ q = 1) : a⁻¹ ^ q = 1 := by
  rw [inv_pow, ha, inv_one]

lemma mem_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : (a ^ n) ^ q = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]

variable {e}
variable (he : ∀ x y : {x : G | x ^ q = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ q = 1},
  e ⟨x.1 * y.1, h⟩ = e x + e y)
include he

lemma E_mul (a b : G) (ha : a ^ q = 1) (hb : b ^ q = 1) : E e (a * b) = E e a + E e b := by
  rw [E_mem e _ (mem_mul a b ha hb), E_mem e _ ha, E_mem e _ hb]
  exact he ⟨a, ha⟩ ⟨b, hb⟩ (mem_mul a b ha hb)

lemma E_one : E e (1 : G) = 0 := by
  have h := E_mul he 1 1 (one_pow _) (one_pow _)
  rw [mul_one] at h
  simpa using h

lemma E_inv (a : G) (ha : a ^ q = 1) : E e a⁻¹ = -E e a := by
  have h := E_mul he a⁻¹ a (mem_inv a ha) ha
  rw [inv_mul_cancel, E_one he] at h
  exact eq_neg_of_add_eq_zero_left h.symm

lemma E_pow (a : G) (ha : a ^ q = 1) (n : ℕ) : E e (a ^ n) = n • E e a := by
  induction n with
  | zero => rw [pow_zero, E_one he, zero_smul]
  | succ n ih => rw [pow_succ, E_mul he _ _ (mem_pow a ha n) ha, ih, succ_nsmul]

/-- A group endomorphism, transported to an additive endomorphism of `M`. -/
noncomputable def endV (f : G →* G) : M →+ M where
  toFun v := E e (f (e.symm v).1)
  map_zero' := by
    rw [← E_one he, symm_E e 1 (one_pow _), map_one]
  map_add' v w := by
    have ha := (e.symm v).2
    have hb := (e.symm w).2
    have h1 : v + w = E e ((e.symm v).1 * (e.symm w).1) := by
      rw [E_mul he _ _ ha hb, E_symm, E_symm]
    show E e (f (e.symm (v + w)).1) = E e (f (e.symm v).1) + E e (f (e.symm w).1)
    rw [h1, symm_E e _ (mem_mul _ _ ha hb), map_mul,
      E_mul he _ _ (mem_map f _ ha) (mem_map f _ hb)]

lemma endV_E (f : G →* G) (g : G) (hg : g ^ q = 1) : endV he f (E e g) = E e (f g) := by
  show E e (f (e.symm (E e g)).1) = _
  rw [symm_E e g hg]

end Transport

/-- Extension of valuation rings (Chevalley; Mathlib `IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_valuationSubring_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (O : ValuationSubring K) :
    ∃ w : ValuationSubring L, w.comap (algebraMap K L) = O := by
  let f : O →+* L := (algebraMap K L).comp O.subtype
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  refine ⟨B, ?_⟩
  ext x
  rw [ValuationSubring.mem_comap]
  constructor
  · intro hx
    by_contra hxO
    have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
    apply hxO
    have hu : IsUnit ((f.codRestrict B.toSubring hB) ⟨x⁻¹, hinv⟩) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K L x, hx⟩, ?_⟩
      apply Subtype.ext
      simp only [f, RingHom.codRestrict_apply, RingHom.comp_apply, ValuationSubring.coe_subtype,
        Subring.coe_mul, Subring.coe_one, map_inv₀]
      exact inv_mul_cancel₀ ((map_ne_zero (algebraMap K L)).mpr hx0)
    obtain ⟨⟨u, v, huv, hvu⟩, hu'⟩ := hloc.map_nonunit _ hu
    have hv : (v : K) = x := by
      have h1 : ((u : K)) * (v : K) = 1 := congrArg Subtype.val huv
      have h2 : (u : K) = x⁻¹ := congrArg Subtype.val hu'
      rw [h2] at h1
      field_simp at h1
      exact h1
    exact hv ▸ v.2
  · intro hx
    exact hB ⟨x, hx⟩

end GlueA6Alg.Alg

end GlueA6AlgSec

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

-- Adopted from scratch/rv-a6-route/A6.lean §10 (hsyn-fix); replaces pkg-I2's `sorry` statement.
/-! ## 10. rv-a6-route: A6 (Lemma PR(ii)) by the Raynaud route, from the leaves plus one
pure-algebra glue statement -/

/-- **Glue (pure algebra, not a leaf; to be proved by the project).** Let `G` be a commutative
group whose `3^{2k}`-torsion `T` is isomorphic to `(ℤ/3^{2k})⁴` (`k ≥ 1`), with endomorphisms
`I, J` satisfying `I² = 2`, `J² = -3`, `IJ = -JI` (so `T` is a module over `Λ = ℤ⟨i,j⟩`, whose
`3`-adic completion is the maximal order of the quaternion division algebra over `ℚ₃`), and an
endomorphism `S` commuting with `I, J` with `(S - 1)² = 0` on `T`. Then `S` is the identity on
the `3^k`-torsion. Proof (docs/research/rv-a6-route.md §3): `T/JT` is an `𝔽₉`-space of dimension
1 (dimension 2 would force `J = 3J'` on the free `ℤ/3^{2k}`-module `T`, whence `3·unit = 0`), so
`T` is cyclic, hence free of rank one over `Λ/3^{2k}` by counting; `S - 1` is right
multiplication by some `c` with `c² = 0`, so `v_Π(c) ≥ 2k`, `c ∈ 3^kΛ`, and `S - 1` kills
`3^k T = G[3^k]`. -/
def QuatUnipotentTrivial : Prop :=
  ∀ (G : Type u) [CommGroup G] (k : ℕ), 1 ≤ k → ∀ (I J S : G →* G),
    (∀ x, I (I x) = x ^ 2) → (∀ x, J (J x) * x ^ 3 = 1) → (∀ x, J (I x) * I (J x) = 1) →
    (∀ x, S (I x) = I (S x)) → (∀ x, S (J x) = J (S x)) →
    (∃ e : {x : G | x ^ (3 ^ (2 * k)) = 1} ≃ (Fin (2 * 2) → ZMod (3 ^ (2 * k))),
      ∀ x y : {x : G | x ^ (3 ^ (2 * k)) = 1},
        ∀ h : x.1 * y.1 ∈ {x : G | x ^ (3 ^ (2 * k)) = 1}, e ⟨x.1 * y.1, h⟩ = e x + e y) →
    (∀ x, x ^ (3 ^ (2 * k)) = 1 → S (S x) * (S x)⁻¹ * (S x)⁻¹ * x = 1) →
    ∀ x, x ^ (3 ^ k) = 1 → S x = x

-- hsyn-fold: proved in scratch/glue-a6-alg/A6.lean (copied).
open GlueA6Alg.Alg in
/-- **`QuatUnipotentTrivial` (proved).** -/
theorem quatUnipotentTrivial : QuatUnipotentTrivial.{u} := by
  intro G _ k hk I J S hI hJ hIJ hSI hSJ ⟨e₀, he₀⟩ hS x hx
  let e : {x : G | x ^ (Q k) = 1} ≃ V k := e₀
  have he : ∀ x y : {x : G | x ^ (Q k) = 1}, ∀ h : x.1 * y.1 ∈ {x : G | x ^ (Q k) = 1},
      e ⟨x.1 * y.1, h⟩ = e x + e y := he₀
  -- every `v` is `E a` with `a ∈ G[q]`
  have hv : ∀ v : V k, ∃ a : G, a ^ (Q k) = 1 ∧ E e a = v :=
    fun v => ⟨_, (e.symm v).2, E_symm e v⟩
  let IV := (endV he I).toZModLinearMap (Q k)
  let JV := (endV he J).toZModLinearMap (Q k)
  let SV := (endV he S).toZModLinearMap (Q k)
  have hIV : ∀ g, g ^ (Q k) = 1 → IV (E e g) = E e (I g) := fun g hg => endV_E he I g hg
  have hJV : ∀ g, g ^ (Q k) = 1 → JV (E e g) = E e (J g) := fun g hg => endV_E he J g hg
  have hSV : ∀ g, g ^ (Q k) = 1 → SV (E e g) = E e (S g) := fun g hg => endV_E he S g hg
  have mI := mem_map (q := Q k) I
  have mJ := mem_map (q := Q k) J
  have mS := mem_map (q := Q k) S
  have key := core hk IV JV SV
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hIV _ (mI a ha), hI, E_pow he a ha, two_smul, two_smul])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hJV _ (mJ a ha)]
      have h := congrArg (E e) (hJ a)
      rw [E_mul he _ _ (mJ _ (mJ a ha)) (mem_pow a ha 3), E_pow he a ha, E_one he] at h
      rw [neg_smul, ofNat_smul_eq_nsmul]
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hJV _ (mI a ha), hJV a ha, hIV _ (mJ a ha)]
      have h := congrArg (E e) (hIJ a)
      rw [E_mul he _ _ (mJ _ (mI a ha)) (mI _ (mJ a ha)), E_one he] at h
      exact eq_neg_of_add_eq_zero_left h)
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hIV a ha, hSV _ (mI a ha), hSV a ha, hIV _ (mS a ha), hSI])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hJV a ha, hSV _ (mJ a ha), hSV a ha, hJV _ (mS a ha), hSJ])
    (by
      intro v; obtain ⟨a, ha, rfl⟩ := hv v
      rw [hSV a ha, hSV _ (mS a ha)]
      have h := congrArg (E e) (hS a ha)
      have m1 := mS _ (mS a ha)
      have m2 := mem_inv _ (mS a ha)
      rw [E_mul he _ _ (mem_mul _ _ (mem_mul _ _ m1 m2) m2) ha,
        E_mul he _ _ (mem_mul _ _ m1 m2) m2, E_mul he _ _ m1 m2, E_inv he _ (mS a ha),
        E_one he] at h
      rw [← h]; module)
  have hxq : x ^ (Q k) = 1 := by
    show x ^ (3 ^ (2 * k)) = 1
    rw [two_mul, pow_add, pow_mul, hx, one_pow]
  have h3 : (3 : R k) ^ k • E e x = 0 := by
    have : (3 : R k) ^ k = ((3 ^ k : ℕ) : R k) := by push_cast; rfl
    rw [this, Nat.cast_smul_eq_nsmul, ← E_pow he x hxq, hx, E_one he]
  have := key (E e x) h3
  rw [hSV x hxq] at this
  exact E_inj e _ _ (mS x hxq) hxq this

section A6

/-- The Galois action of `σ` as a group endomorphism of `A(L)`. -/
noncomputable def galHomPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (σ : L ≃ₐ[K] L) : Pts A L →* Pts A L where
  toFun := galAct A σ
  map_one' := galAct_one A σ
  map_mul' := galAct_mul A σ

/-- A homomorphism of group objects `f : A ⟶ A` as a group endomorphism of `A(L)`. -/
noncomputable def endPts (A : Grp (Over (Spec (.of K)))) {L : Type u} [CommRing L]
    [Algebra K L] (f : A ⟶ A) : Pts A L →* Pts A L where
  toFun x := x ≫ f.hom.hom
  map_one' := MonObj.one_comp _
  map_mul' x y := MonObj.mul_comp x y _

/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the leaves `NeronOggShafarevich`,
`RaynaudCriterion`, `TorsionStructure` and the pure-algebra glue `QuatUnipotentTrivial`.**
Same statement as `PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
theorem goodReduction_of_QM_rational3_of_alg (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (hAlg : QuatUnipotentTrivial.{u})
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
  have : IsProper A.X.hom := IsAbelianVariety.proper
  have : GeometricallyIntegral A.X.hom := IsAbelianVariety.geomIntegral
  have : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  have h3' : IsUnit ((3 : ℕ) : O) := by exact_mod_cast h3
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    intro h
    apply h3.ne_zero
    apply Subtype.val_injective
    have h' : (3 : K) = 0 := by exact_mod_cast h
    have e3 : ((3 : O) : K) = 3 := rfl
    rw [e3, h']
    rfl
  -- inertia acts trivially on `A[3^k]` for every `k ≥ 1`
  have key : ∀ k : ℕ, 1 ≤ k → InertiaTrivialOn A w (3 ^ k) := by
    intro k hk σ hσ x hx
    obtain ⟨e, he⟩ := hTors K A 2 (3 ^ (2 * k)) hdim (by positivity)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ h3K)
    exact hAlg (Pts A (AlgebraicClosure K)) k hk (endPts A I) (endPts A J) (galHomPts A σ)
      hI hJ hIJ (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      (fun x => by
        simp only [galHomPts, endPts, MonoidHom.coe_mk, OneHom.coe_mk, galAct, Category.assoc])
      ⟨e, he⟩ (fun y hy => hRay K O w hw A 3 le_rfl h3' hrat σ hσ 3 Nat.prime_three h3'
        (2 * k) y hy) x hx
  -- Néron–Ogg–Shafarevich (c) ⇒ (a)
  refine (hNOS K O w hw A).2.mpr ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 3 ^ (k + 1)) ?_ ?_
  · intro a b hab
    simpa using (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hab)
  · intro k
    refine ⟨by positivity, ?_, key (k + 1) (by omega)⟩
    rw [Nat.cast_pow]; exact h3'.pow _

-- hsyn-fold: from scratch/glue-a6-alg/A6.lean.
/-- **Glue A6 (Lemma PR(ii), Raynaud route), proved from the three I2 leaves
`NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure` alone** (the pure-algebra glue
`QuatUnipotentTrivial` is now a theorem). Same statement as
`PkgI2.goodReduction_of_QM_rational3` (scratch/pkg-I2/I2.lean). -/
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
    HasGoodReduction A O :=
  goodReduction_of_QM_rational3_of_alg hNOS hRay hTors quatUnipotentTrivial O w hw A hdim I J
    hI hJ hIJ h3 hrat

/-- **A6 without the auxiliary `w`**: the valuation subring of `K̄` over `O` exists
(`GlueA6Alg.Alg.exists_valuationSubring_comap_eq`), so it is not a hypothesis. -/
theorem goodReduction_of_QM_rational3' (hNOS : NeronOggShafarevich.{u})
    (hRay : RaynaudCriterion.{u}) (hTors : TorsionStructure.{u})
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
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
  obtain ⟨w, hw⟩ := GlueA6Alg.Alg.exists_valuationSubring_comap_eq (L := AlgebraicClosure K) O
  exact goodReduction_of_QM_rational3 hNOS hRay hTors O w hw A hdim I J hI hJ hIJ h3 hrat

end A6


end Glue

end PkgI2

end PkgI2Sec

section PkgI3Sec
/-! ### Copied from `scratch/pkg-I3/I3.lean` (compiled there). -/

noncomputable section

-- glue-I3-linalg (hsyn-fix): the linear-algebra glue of C2 and E1, from scratch/glue-I3-linalg/C2.lean §0.
/-! ## 0. Linear-algebra glue (copied from `scratch/glue-I3-linalg/Commutant.lean`, plus
`finrank_commOf_le_of_equiv` and `equivariantDescent`) -/

namespace GlueI3

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The projection onto a subrepresentation along an invariant complement is equivariant. -/
lemma projection_comm {ρ : Representation k G V} (W W' : Subrepresentation ρ)
    (h : IsCompl W.toSubmodule W'.toSubmodule) (g : G) :
    W.toSubmodule.projection W'.toSubmodule h ∘ₗ ρ g =
      ρ g ∘ₗ W.toSubmodule.projection W'.toSubmodule h := by
  apply LinearMap.ext
  intro v
  set p := W.toSubmodule.projection W'.toSubmodule h
  have hv := Submodule.projection_add_projection_eq_self h v
  set a := p v with ha
  set b := W'.toSubmodule.projection W.toSubmodule h.symm v
  have haW : a ∈ W.toSubmodule := by apply Submodule.projection_apply_mem
  have hbW : b ∈ W'.toSubmodule := by apply Submodule.projection_apply_mem
  simp only [LinearMap.coe_comp, Function.comp_apply]
  conv_lhs => rw [← hv, map_add, map_add]
  rw [Submodule.projection_apply_of_mem_right h (W'.apply_mem_toSubmodule g hbW), add_zero,
    Submodule.projection_apply_of_mem_left h (W.apply_mem_toSubmodule g haW)]

/-- **The commutant argument (GLUE, proved).** A semisimple representation on a nonzero space
whose `G`-equivariant endomorphisms are all scalars is irreducible. -/
theorem isIrreducible_of_commutant_scalar (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    (hcomm : ∀ φ : V →ₗ[k] V, (∀ g, φ ∘ₗ ρ g = ρ g ∘ₗ φ) → ∃ c : k, φ = c • LinearMap.id) :
    ρ.IsIrreducible := by
  refine { toNontrivial := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h] at this
    exact hx ((Submodule.mem_bot k).mp this)
  · intro W
    obtain ⟨W', hW'⟩ := hss.exists_isCompl W
    have h : IsCompl W.toSubmodule W'.toSubmodule := by
      constructor
      · rw [disjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
        simp only [Subrepresentation.toSubmodule_inf] at this
        exact this
      · rw [codisjoint_iff]
        have := congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
        simp only [Subrepresentation.toSubmodule_sup] at this
        exact this
    obtain ⟨c, hc⟩ := hcomm _ (projection_comm W W' h)
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    -- some nonzero `w ∈ W` gives `c = 1`
    have hne : W.toSubmodule ≠ ⊥ := by
      intro h0; apply hW; apply Subrepresentation.toSubmodule_injective; rw [h0]; rfl
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have h1 := congrArg (fun f => f w) hc
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [Submodule.projection_apply_of_mem_left h hwW] at h1
    have hc1 : c = 1 := by
      have : (c - 1) • w = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hw0)
    -- then `W' = 0`
    have hW'0 : W'.toSubmodule = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have h2 := congrArg (fun f => f y) hc
      simp only [LinearMap.id_apply, hc1, one_smul] at h2
      rw [Submodule.projection_apply_of_mem_right h hy] at h2
      exact (Submodule.mem_bot k).mpr h2.symm
    apply Subrepresentation.toSubmodule_injective
    have := h.sup_eq_top
    rw [hW'0, sup_bot_eq] at this
    exact this

/-- The commutant of a family of endomorphisms. -/
def commOf {W : Type*} [AddCommGroup W] [Module k W] (r : G → W →ₗ[k] W) :
    Submodule k (W →ₗ[k] W) where
  carrier := {φ | ∀ g, φ ∘ₗ r g = r g ∘ₗ φ}
  add_mem' := by
    intro φ ψ hφ hψ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, hφ g, hψ g]
  zero_mem' := by intro g; simp
  smul_mem' := by
    intro c φ hφ g
    simp only [Set.mem_ofPred_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hφ g]

/-- `(a, b, c, d) ↦ [[a, b], [c, d]]`, an injective linear map
`End_G(V)⁴ → End_G(V ⊕ V)`. -/
def blockMap (ρ : Representation k G V) :
    (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) ×
      (commOf (k := k) (fun g => ρ g)) × (commOf (k := k) (fun g => ρ g)) →ₗ[k]
      commOf (k := k) (fun g => (ρ g).prodMap (ρ g)) where
  toFun t := ⟨((t.1 : V →ₗ[k] V).coprod (t.2.1 : V →ₗ[k] V)).prod
      ((t.2.2.1 : V →ₗ[k] V).coprod (t.2.2.2 : V →ₗ[k] V)), by
    intro g
    have ha : ∀ v, (t.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.1.2 g)
    have hb : ∀ v, (t.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.1.2 g)
    have hc : ∀ v, (t.2.2.1 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.1 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.1.2 g)
    have hd : ∀ v, (t.2.2.2 : V →ₗ[k] V) (ρ g v) = ρ g ((t.2.2.2 : V →ₗ[k] V) v) :=
      fun v => congrArg (fun f => f v) (t.2.2.2.2 g)
    apply LinearMap.ext
    rintro ⟨x, y⟩
    simp [ha, hb, hc, hd]⟩
  map_add' s t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
    simp [add_add_add_comm]
  map_smul' c t := by
    apply Subtype.ext; apply LinearMap.ext; rintro ⟨x, y⟩
    simp

lemma blockMap_injective (ρ : Representation k G V) : Function.Injective (blockMap ρ) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  rintro ⟨a, b, c, d⟩ h
  have h' := congrArg Subtype.val h
  have hx : ∀ x, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (x, 0) = 0 :=
    fun x => by rw [h']; rfl
  have hy : ∀ y, (blockMap ρ (a, b, c, d) : V × V →ₗ[k] V × V) (0, y) = 0 :=
    fun y => by rw [h']; rfl
  simp only [blockMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.prod_apply, Function.prod,
    LinearMap.coprod_apply, map_zero, add_zero, zero_add, Prod.mk_eq_zero] at hx hy
  refine Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).1))
    (Prod.ext (Subtype.ext (LinearMap.ext fun y => (hy y).1))
      (Prod.ext (Subtype.ext (LinearMap.ext fun x => (hx x).2))
        (Subtype.ext (LinearMap.ext fun y => (hy y).2))))

omit [Monoid G] in
lemma id_mem_commOf {W : Type*} [AddCommGroup W] [Module k W] (r : G → W →ₗ[k] W) :
    (LinearMap.id : W →ₗ[k] W) ∈ commOf r := by
  intro g; simp

omit [Monoid G] in
/-- A commutant of dimension `1` consists of the scalars. -/
lemma scalar_of_finrank_commOf_eq_one {W : Type*} [AddCommGroup W] [Module k W] [Nontrivial W]
    (r : G → W →ₗ[k] W) (h1 : Module.finrank k (commOf r) = 1) :
    ∀ φ ∈ commOf r, ∃ c : k, φ = c • LinearMap.id := by
  intro φ hφ
  have hid0 : (⟨LinearMap.id, id_mem_commOf r⟩ : commOf r) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    exact hx (by simpa using congrArg (fun f : commOf r => (f : W →ₗ[k] W) x) h0)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hid0).mp h1 ⟨φ, hφ⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

/-- **The dimension count of C2 (GLUE, proved).** If `dim End_G(V ⊕ V) ≤ 4` and `V ≠ 0` is
finite-dimensional, then `dim End_G(V) = 1`. -/
theorem finrank_commOf_eq_one_of_prod_le_four (ρ : Representation k G V) [Nontrivial V]
    [FiniteDimensional k V]
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4) :
    Module.finrank k (commOf (k := k) (fun g => ρ g)) = 1 := by
  have hinj := blockMap_injective ρ
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod] at hle
  have hC1 : Module.finrank k (commOf (k := k) (fun g => ρ g)) ≤ 1 := by omega
  have hid0 : (⟨LinearMap.id, id_mem_commOf _⟩ : commOf (k := k) (fun g => ρ g)) ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have h0x := congrArg (fun f : commOf (k := k) (fun g => ρ g) => (f : V →ₗ[k] V) x) h0
    exact hx (by simpa using h0x)
  have hpos : 0 < Module.finrank k (commOf (k := k) (fun g => ρ g)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hid0⟩
  omega

/-- **C2 over the splitting field (GLUE, proved).** N5 L731-734: over a field `E` splitting `B`,
`V_ℓ(A) ⊗ E ≅ r ⊕ r` and `dim_E End_G(V_ℓ A ⊗ E) = 4`. If the commutant of `r ⊕ r` has
dimension at most `4` and `r` is semisimple and nonzero, then `r` is irreducible, and its
commutant is the scalars. -/
theorem isIrreducible_of_finrank_commOf_prod_le_four (ρ : Representation k G V) [Nontrivial V]
    (hss : ρ.IsSemisimpleRepresentation)
    [FiniteDimensional k V]
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4) :
    ρ.IsIrreducible ∧ ∀ φ ∈ commOf (k := k) (fun g => ρ g), ∃ c : k, φ = c • LinearMap.id := by
  have hsc := scalar_of_finrank_commOf_eq_one _ (finrank_commOf_eq_one_of_prod_le_four ρ h4)
  exact ⟨isIrreducible_of_commutant_scalar ρ hss (fun φ hφ => hsc φ hφ), hsc⟩

/-- **Semisimplicity passes to equivariant quotients (GLUE, proved).** -/
theorem isSemisimple_of_surjective {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (hss : ρ.IsSemisimpleRepresentation)
    (f : V →ₗ[k] W) (hf : Function.Surjective f) (hfeq : ∀ g v, f (ρ g v) = σ g (f v)) :
    σ.IsSemisimpleRepresentation := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at hss ⊢
  exact IsSemisimpleModule.of_surjective
    (IntertwiningMap.equivLinearMapAsModule ρ σ (LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ f hfeq)) hf

/-- An equivariant linear isomorphism `V ≃ W` gives `dim End_G(V) ≤ dim End_G(W)`. -/
lemma finrank_commOf_le_of_equiv {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (r : G → V →ₗ[k] V) (s : G → W →ₗ[k] W) (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (r g v) = s g (e v)) :
    Module.finrank k (commOf r) ≤ Module.finrank k (commOf s) := by
  have hmem : ∀ φ ∈ commOf r, e.conj φ ∈ commOf s := by
    intro φ hφ g
    apply LinearMap.ext; intro w
    have hφ' := congrArg (fun f => f (e.symm w)) (hφ g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hφ'
    have he' : e.symm (s g w) = r g (e.symm w) := by
      apply e.injective; rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.conj_apply,
      LinearEquiv.coe_coe]
    rw [he', hφ', he]
  let f : commOf r →ₗ[k] commOf s := e.conj.toLinearMap.restrict hmem
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact e.conj.injective (congrArg Subtype.val hxy)
  exact LinearMap.finrank_le_finrank_of_injective hf

/-! ### Extension of the coefficient field -/

/-- Base change `ρ_E` of a representation along a field extension `E/k`. -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

/-- **GLUE, not proved here (algebra; STANDARD).** In characteristic `0`, semisimplicity of a
finite-dimensional representation survives extension of the coefficient field. (The span of
`ρ(G)` is a finite-dimensional algebra with a faithful semisimple module, hence semisimple, hence
separable since `k` is perfect, so its base change is semisimple.) -/
def SemisimpleBaseChange : Prop :=
  ∀ (k E G V : Type) [Field k] [CharZero k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (ρ : Representation k G V),
    ρ.IsSemisimpleRepresentation → (repBaseChange E ρ).IsSemisimpleRepresentation

/-! ### E1: a common constituent gives a nonzero equivariant map -/

/-- **E1, first arrow (GLUE, proved).** If `ρ` is semisimple and a nonzero subrepresentation `U`
of `ρ` is equivariantly isomorphic to a subrepresentation `U'` of `σ`, there is a nonzero
`G`-equivariant linear map `V → W`. (Project onto `U` along an invariant complement, transport,
include.) -/
theorem exists_equivariant_ne_zero_of_common {W : Type*} [AddCommGroup W] [Module k W]
    (ρ : Representation k G V) (σ : Representation k G W) (hss : ρ.IsSemisimpleRepresentation)
    (U : Subrepresentation ρ) (U' : Subrepresentation σ) (hU : U ≠ ⊥)
    (e : U.toSubmodule ≃ₗ[k] U'.toSubmodule)
    (he : ∀ g (u : U.toSubmodule), (e ⟨ρ g u, U.apply_mem_toSubmodule g u.2⟩ : W) = σ g (e u)) :
    ∃ φ : V →ₗ[k] W, φ ≠ 0 ∧ ∀ g, φ ∘ₗ ρ g = σ g ∘ₗ φ := by
  obtain ⟨U'', hU''⟩ := hss.exists_isCompl U
  have h : IsCompl U.toSubmodule U''.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have := congrArg Subrepresentation.toSubmodule hU''.inf_eq_bot
      simp only [Subrepresentation.toSubmodule_inf] at this
      exact this
    · rw [codisjoint_iff]
      have := congrArg Subrepresentation.toSubmodule hU''.sup_eq_top
      simp only [Subrepresentation.toSubmodule_sup] at this
      exact this
  let p := Submodule.projectionOnto U.toSubmodule U''.toSubmodule h
  refine ⟨U'.toSubmodule.subtype ∘ₗ e.toLinearMap ∘ₗ p, ?_, ?_⟩
  · intro h0
    apply hU
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊥
    rw [eq_bot_iff]
    intro u hu
    have := congrArg (fun f => f u) h0
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply,
      Submodule.coe_subtype, LinearEquiv.coe_coe, p] at this
    rw [Submodule.projectionOnto_apply_left h ⟨u, hu⟩] at this
    have h2 : e ⟨u, hu⟩ = 0 := Subtype.ext this
    have h3 : (⟨u, hu⟩ : U.toSubmodule) = 0 := by simpa using h2
    exact (Submodule.mem_bot k).mpr (congrArg Subtype.val h3)
  · intro g
    apply LinearMap.ext
    intro v
    have hpv : (p (ρ g v)) = ⟨ρ g (p v), U.apply_mem_toSubmodule g (p v).2⟩ := by
      apply Subtype.ext
      exact congrArg (fun f => f v) (projection_comm U U'' h g)
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe]
    rw [hpv, he]

/-- **Equivariant descent (GLUE, proved).** A nonzero `G`-equivariant `E`-linear map
`E ⊗ V → E ⊗ W` gives a nonzero `G`-equivariant `k`-linear map `V → W`: expand in a `k`-basis of
`E` and take a nonzero coordinate. -/
theorem exists_equivariant_ne_zero_of_baseChange {W : Type*} [AddCommGroup W] [Module k W]
    (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) (σ : Representation k G W)
    (φ : TensorProduct k E V →ₗ[E] TensorProduct k E W) (hφ0 : φ ≠ 0)
    (hφ : ∀ g, φ ∘ₗ repBaseChange E ρ g = repBaseChange E σ g ∘ₗ φ) :
    ∃ ψ : V →ₗ[k] W, ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ ρ g = σ g ∘ₗ ψ := by
  classical
  let b := Module.Free.chooseBasis k E
  let c : TensorProduct k E W ≃ₗ[k] (Module.Free.ChooseBasisIndex k E →₀ W) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl k W)).trans
      (TensorProduct.finsuppScalarLeft k W _)
  have hc : ∀ (x : TensorProduct k E W) g j, c (repBaseChange E σ g x) j = σ g (c x j) := by
    intro x g j
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp [c, repBaseChange, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
  let ψ : Module.Free.ChooseBasisIndex k E → V →ₗ[k] W := fun j =>
    (Finsupp.lapply j) ∘ₗ c.toLinearMap ∘ₗ (φ.restrictScalars k) ∘ₗ (TensorProduct.mk k E V 1)
  have hψ : ∀ j v, ψ j v = c (φ (1 ⊗ₜ[k] v)) j := fun j v => rfl
  have heq : ∀ j g, ψ j ∘ₗ ρ g = σ g ∘ₗ ψ j := by
    intro j g
    apply LinearMap.ext; intro v
    show c (φ ((1 : E) ⊗ₜ[k] ρ g v)) j = σ g (c (φ ((1 : E) ⊗ₜ[k] v)) j)
    have h1 : (1 : E) ⊗ₜ[k] ρ g v = repBaseChange E ρ g (1 ⊗ₜ v) := by
      simp [repBaseChange, LinearMap.baseChange_tmul]
    have h2 := congrArg (fun f => f ((1 : E) ⊗ₜ[k] v)) (hφ g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at h2
    rw [h1, h2, hc]
  have hne : ∃ j, ψ j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hφ0
    have h1 : ∀ v, φ (1 ⊗ₜ[k] v) = 0 := fun v => by
      apply c.injective
      ext j
      rw [map_zero, Finsupp.zero_apply, ← hψ, h j, LinearMap.zero_apply]
    apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      have : a ⊗ₜ[k] v = a • ((1 : E) ⊗ₜ[k] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul, h1, smul_zero, LinearMap.zero_apply]
    | add x y hx hy => rw [map_add, hx, hy]; simp
  obtain ⟨j, hj⟩ := hne
  exact ⟨ψ j, hj, heq j⟩

/-- `E ⊗_k End_G(V) → End_E(E ⊗ V)`, `e ⊗ ψ ↦ e • (ψ ⊗ E)`. -/
def commBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    TensorProduct k E (commOf (k := k) (fun g => ρ g)) →ₗ[E]
      (TensorProduct k E V →ₗ[E] TensorProduct k E V) :=
  ((LinearMap.baseChangeHom k E V V) ∘ₗ (commOf (k := k) (fun g => ρ g)).subtype).liftBaseChange E

/-- **Every equivariant `E`-linear endomorphism of `E ⊗ V` comes from `E ⊗ End_G(V)` (GLUE,
proved).** Coordinates in a `k`-basis `(bⱼ)` of `E`: `φ = ∑ⱼ bⱼ • (ψⱼ ⊗ E)` with `ψⱼ ∈ End_G(V)`. -/
theorem commOf_baseChange_le_range (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V] :
    commOf (k := E) (fun g => repBaseChange E ρ g) ≤ LinearMap.range (commBaseChange E ρ) := by
  classical
  let C := commOf (k := k) (fun g => ρ g)
  let Φ := commBaseChange E ρ
  intro φ hφ
  have hmem : φ ∈ LinearMap.range Φ := by
    let b := Module.Free.chooseBasis k E
    let c : TensorProduct k E V ≃ₗ[k] (Module.Free.ChooseBasisIndex k E →₀ V) :=
      (TensorProduct.congr b.repr (LinearEquiv.refl k V)).trans
        (TensorProduct.finsuppScalarLeft k V _)
    have hc : ∀ (x : TensorProduct k E V) g j, c (repBaseChange E ρ g x) j = ρ g (c x j) := by
      intro x g j
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a w =>
        simp [c, repBaseChange, LinearMap.baseChange_tmul]
      | add x y hx hy =>
        rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add, Finsupp.add_apply, map_add]
    have hcb : ∀ j (w : V) j', c (b j ⊗ₜ[k] w) j' = if j = j' then w else 0 := by
      intro j w j'
      simp [c, Finsupp.single_apply]
    let ψ : Module.Free.ChooseBasisIndex k E → V →ₗ[k] V := fun j =>
      (Finsupp.lapply j) ∘ₗ c.toLinearMap ∘ₗ (φ.restrictScalars k) ∘ₗ (TensorProduct.mk k E V 1)
    have hψ : ∀ j v, ψ j v = c (φ (1 ⊗ₜ[k] v)) j := fun j v => rfl
    have hψC : ∀ j, ψ j ∈ C := by
      intro j g
      apply LinearMap.ext; intro v
      show c (φ ((1 : E) ⊗ₜ[k] ρ g v)) j = ρ g (c (φ ((1 : E) ⊗ₜ[k] v)) j)
      have h1 : (1 : E) ⊗ₜ[k] ρ g v = repBaseChange E ρ g (1 ⊗ₜ v) := by
        simp [repBaseChange, LinearMap.baseChange_tmul]
      have h2 := congrArg (fun f => f ((1 : E) ⊗ₜ[k] v)) (hφ g)
      simp only [LinearMap.coe_comp, Function.comp_apply] at h2
      rw [h1, h2, hc]
    let bV := Module.finBasis k V
    let S : Finset (Module.Free.ChooseBasisIndex k E) :=
      Finset.univ.biUnion (fun i => (c (φ (1 ⊗ₜ[k] bV i))).support)
    have hS : ∀ j, j ∉ S → ψ j = 0 := by
      intro j hj
      apply bV.ext; intro i
      rw [hψ, LinearMap.zero_apply]
      by_contra h
      apply hj
      simp only [S, Finset.mem_biUnion, Finset.mem_univ, true_and, Finsupp.mem_support_iff]
      exact ⟨i, h⟩
    refine ⟨∑ j ∈ S, b j ⊗ₜ[k] (⟨ψ j, hψC j⟩ : C), ?_⟩
    have key : ∀ v, (Φ (∑ j ∈ S, b j ⊗ₜ[k] (⟨ψ j, hψC j⟩ : C))) (1 ⊗ₜ[k] v) =
        ∑ j ∈ S, b j ⊗ₜ[k] ψ j v := by
      intro v
      simp [Φ, commBaseChange, map_sum, LinearMap.sum_apply, LinearMap.baseChange_tmul,
        TensorProduct.smul_tmul']
    apply LinearMap.ext; intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a v =>
      have hav : a ⊗ₜ[k] v = a • ((1 : E) ⊗ₜ[k] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hav, map_smul, map_smul, key]
      congr 1
      apply c.injective
      ext j'
      rw [map_sum, Finsupp.finsetSum_apply, ← hψ]
      simp only [hcb]
      rw [Finset.sum_ite_eq']
      split_ifs with hj'
      · rfl
      · rw [hS j' hj', LinearMap.zero_apply]
  exact hmem

/-- **Invariants under extension of coefficients, `≤` (GLUE, proved).**
`dim_E End_G(E ⊗ V) ≤ dim_k End_G(V)` for finite-dimensional `V`. -/
theorem finrank_commOf_baseChange_le (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V] :
    Module.finrank E (commOf (k := E) (fun g => repBaseChange E ρ g)) ≤
      Module.finrank k (commOf (k := k) (fun g => ρ g)) :=
  calc Module.finrank E (commOf (k := E) (fun g => repBaseChange E ρ g))
      ≤ Module.finrank E (LinearMap.range (commBaseChange E ρ)) :=
        Submodule.finrank_mono (commOf_baseChange_le_range E ρ)
    _ ≤ Module.finrank E (TensorProduct k E (commOf (k := k) (fun g => ρ g))) :=
        LinearMap.finrank_range_le _
    _ = Module.finrank k (commOf (k := k) (fun g => ρ g)) := Module.finrank_baseChange

/-- **Scalar commutants stay scalar under extension of coefficients (GLUE, proved).** -/
theorem scalar_commOf_baseChange (E : Type*) [Field E] [Algebra k E]
    (ρ : Representation k G V) [FiniteDimensional k V]
    (hsc : ∀ ψ ∈ commOf (k := k) (fun g => ρ g), ∃ c : k, ψ = c • LinearMap.id) :
    ∀ φ ∈ commOf (k := E) (fun g => repBaseChange E ρ g), ∃ μ : E, φ = μ • LinearMap.id := by
  intro φ hφ
  obtain ⟨t, rfl⟩ := commOf_baseChange_le_range E ρ hφ
  clear hφ
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul e ψ =>
    obtain ⟨c, hc⟩ := hsc ψ ψ.2
    refine ⟨e * algebraMap k E c, ?_⟩
    simp only [commBaseChange, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp,
      Function.comp_apply, Submodule.coe_subtype, LinearMap.baseChangeHom_apply, hc]
    rw [LinearMap.baseChange_smul, LinearMap.baseChange_id]
    apply LinearMap.ext; intro x
    simp [mul_smul, algebraMap_smul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    exact ⟨a + a', by rw [map_add, ha, ha', add_smul]⟩

/-- **C2, absolute irreducibility (GLUE, proved from `SemisimpleBaseChange`).**
If `r` is a nonzero semisimple representation over a field of characteristic `0` with
`dim End_G(r ⊕ r) ≤ 4`, then `r ⊗ F` is irreducible for every extension `F`, i.e. `r` is
absolutely irreducible. -/
theorem absolutelyIrreducible_of_finrank_commOf_prod_le_four (hSS : SemisimpleBaseChange)
    {k G V : Type} [Field k] [CharZero k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V] (ρ : Representation k G V)
    (hss : ρ.IsSemisimpleRepresentation)
    (h4 : Module.finrank k (commOf (k := k) (fun g => (ρ g).prodMap (ρ g))) ≤ 4)
    (F : Type) [Field F] [Algebra k F] : (repBaseChange F ρ).IsIrreducible := by
  obtain ⟨-, hsc⟩ := isIrreducible_of_finrank_commOf_prod_le_four ρ hss h4
  have : Nontrivial (TensorProduct k F V) := by
    apply Module.nontrivial_of_finrank_pos (R := F)
    rw [Module.finrank_baseChange]
    exact Module.finrank_pos
  exact isIrreducible_of_commutant_scalar _ (hSS k F G V ρ hss)
    (scalar_commOf_baseChange F ρ hsc)


/-- **GLUE (linear algebra; the `Hom` form of invariants under extension, weakened to what E1 uses;
proved below as `equivariantDescent`).** A nonzero `G`-equivariant `E`-linear map
`V ⊗ E → W ⊗ E` forces a nonzero `G`-equivariant `k`-linear map `V → W` (`V`, `W`
finite-dimensional): `Hom_G(V ⊗ E, W ⊗ E) = Hom_G(V, W) ⊗ E`. -/
def EquivariantDescent : Prop :=
  ∀ (k E G V W : Type) [Field k] [Field E] [Algebra k E] [Monoid G] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W),
    (∃ φ : TensorProduct k E V →ₗ[E] TensorProduct k E W, φ ≠ 0 ∧
      ∀ g, φ ∘ₗ repBaseChange E ρ g = repBaseChange E σ g ∘ₗ φ) →
    ∃ ψ : V →ₗ[k] W, ψ ≠ 0 ∧ ∀ g, ψ ∘ₗ ρ g = σ g ∘ₗ ψ

theorem equivariantDescent : EquivariantDescent := by
  intro k E G V W _ _ _ _ _ _ _ _ _ _ ρ σ ⟨φ, h0, h⟩
  exact exists_equivariant_ne_zero_of_baseChange E ρ σ φ h0 h

end GlueI3


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

/-- **I3.M3 — Poincaré complete reducibility (Mumford §19, Thm 1, over `k̄`; over any `k` of
characteristic 0: Milne, *Abelian varieties*, in Cornell–Silverman 1986, Prop. 12.1, UNVERIFIED;
rv-leaves-b repair 2), in the form used at E1.**
Over a field of characteristic `0`, if `End⁰(A)` is a division algebra and `f : A → J` is a
nonzero homomorphism, there are an abelian variety `Z` and a homomorphism `g : Z → J` such that
`(f, g) : A × Z → J`, `(a, z) ↦ f(a) + g(z)`, is an isogeny. -/
def PoincareReducibility : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A J : AbVar k), EndDivision A →
    ∀ f : Hom A J, f ≠ 0 → ∃ (Z : AbVar k) (g : Hom Z J),
      IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)

/-- `ℍ[ℚ, a, b]` is indefinite: `ℍ[ℚ,a,b] ⊗ ℝ ≅ M₂(ℝ)`, i.e. not both `a < 0` and `b < 0`. -/
def QuatIndefinite (a b : ℚ) : Prop := 0 < a ∨ 0 < b

/-- **I3.Q / T27 — the QM dichotomy (step A9), with Yu's hypothesis.** Chia-Fu Yu,
*Endomorphism algebras of QM abelian surfaces*, J. Pure Appl. Algebra (2013; volume 217 from memory, UNVERIFIED), Thm 1.1
(journal p. 907; arXiv:1210.1125 Thm 1.1; checked by the locator audit): over an algebraically
closed field of characteristic `0`, if an **indefinite** quaternion division algebra `B = (a, b)_ℚ`
embeds in `End⁰(A)` for an abelian surface `A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))`,
`d < 0` (Yu adds that `ℚ(√d)` splits `B`; dropped, so this is a consequence of Yu's theorem).
*2026-11-12 (loc-fix, applying rv-loc-leaves (i)):* this replaces the earlier leaf `QMDichotomy`,
which had no indefiniteness hypothesis and was therefore stronger than Yu's theorem (still true by
Mumford §21, but not a consequence of the cited locator). The earlier conclusion survives only at
the project's `B = (2, -3)`, as the lemma `qmDichotomy_B6`, proved from this leaf. -/
def QMDichotomyYu : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- The project's `B = (2, -3)` is indefinite. -/
theorem quatIndefinite_two_neg_three : QuatIndefinite 2 (-3) := Or.inl (by norm_num)

/-- The use at step A9 / G5 (`B = (2,-3)`) needs only the repaired form. -/
theorem qmDichotomy_B6 (h : QMDichotomyYu) (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbVar k) (hA : A.dim = 2) (hdiv : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x)
    (hemb : Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] End0 A)) :
    Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) ∨
      ∃ d : ℚ, d < 0 ∧
        Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) :=
  h k A hA 2 (-3) quatIndefinite_two_neg_three hdiv hemb

/-- The package as one hypothesis. -/
structure I3Leaves : Prop where
  faltingsSemisimple : FaltingsSemisimple
  faltingsTate : FaltingsTate
  tateModuleFree : TateModuleFree
  homFreeFinite : HomFreeFinite
  charPolyIndepOfEll : CharPolyIndepOfEll
  poincare : PoincareReducibility
  qmDichotomy : QMDichotomyYu

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

-- glue-I3-linalg (hsyn-fix): C2 and E1 in pkg-I3's object layer, from scratch/glue-I3-linalg/C2.lean §5.
/-! ## 5. C2 in the object layer of pkg-I3 -/

namespace PkgI3

open GlueI3 AbVar

lemma equivEnd_eq_commOf {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    equivEnd A ℓ = commOf (k := ℚ_[ℓ]) (fun σ => A.galRep ℓ σ) := rfl

/-- **C2 (GLUE, proved from I3's leaves, `SemisimpleBaseChange`, and A9's output).**
`A` over a number field `K` with `rank_ℤ End_K(A) = 4` (`End⁰_K(A) = B`, from A9, A10, A8/B3);
`E ⊇ ℚ_ℓ` a field and `V_ℓ(A) ⊗ E ≅ r ⊕ r` as `G_K`-representations (from `B ⊗ E ≅ M₂(E)`), with `r`
semisimple (a quotient of `V_ℓ(A) ⊗ E`, semisimple by `FaltingsSemisimple` and
`SemisimpleBaseChange`; derived here). Then `r` is absolutely irreducible: `r ⊗ F` is irreducible
for every field `F ⊇ E`. -/
theorem C2_absolutelyIrreducible (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree) (hH : HomFreeFinite)
    (hSS : SemisimpleBaseChange)
    {K : Type} [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hrank : Module.finrank ℤ (End A) = 4)
    (E : Type) [Field E] [CharZero E] [Algebra ℚ_[ℓ] E]
    {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] [Nontrivial U]
    (r : Representation E (Field.absoluteGaloisGroup K) U)
    (e : TensorProduct ℚ_[ℓ] E (A.V ℓ) ≃ₗ[E] U × U)
    (he : ∀ σ v, e (repBaseChange E (A.galRep ℓ) σ v) = (r σ).prodMap (r σ) (e v))
    (F : Type) [Field F] [Algebra E F] : (repBaseChange F r).IsIrreducible := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfin, -⟩ := hT K A ℓ hℓK
  have : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  have h1 : Module.finrank E (commOf (k := E) (fun σ => repBaseChange E (A.galRep ℓ) σ)) ≤ 4 := by
    have := finrank_commOf_baseChange_le E (A.galRep ℓ)
    rwa [← equivEnd_eq_commOf, finrank_equivEnd hF hT hH, hrank] at this
  have he' : ∀ σ w, e.symm ((r σ).prodMap (r σ) w) = repBaseChange E (A.galRep ℓ) σ (e.symm w) := by
    intro σ w
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have h4 := finrank_commOf_le_of_equiv (fun σ => (r σ).prodMap (r σ)) _ e.symm he'
  replace h4 := h4.trans h1
  have hVE := hSS ℚ_[ℓ] E _ _ (A.galRep ℓ) (hS K A ℓ)
  have hr : r.IsSemisimpleRepresentation := by
    refine isSemisimple_of_surjective (repBaseChange E (A.galRep ℓ)) r hVE
      (LinearMap.fst E U U ∘ₗ e.toLinearMap) ?_ ?_
    · intro u
      exact ⟨e.symm (u, 0), by simp⟩
    · intro σ v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.fst_apply]
      rw [he]
      rfl
  exact absolutelyIrreducible_of_finrank_commOf_prod_le_four hSS r hr h4 F

/-- **E1, from a common constituent to a nonzero homomorphism (GLUE, proved from I3's leaves and
`SemisimpleBaseChange`).** N5 L861-867: if `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common
constituent (a nonzero subrepresentation `U` of the first, equivariantly isomorphic to a
subrepresentation `U'` of the second), then there is a nonzero homomorphism `A → J` over `K`. -/
theorem E1_exists_hom_ne_zero (hS : FaltingsSemisimple) (hF : FaltingsTate) (hT : TateModuleFree)
    (hSS : SemisimpleBaseChange)
    {K : Type} [Field K] [NumberField K] (A J : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E]
    (U : Subrepresentation (repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (repBaseChange E (J.galRep ℓ))) (hU : U ≠ ⊥)
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule)
    (he : ∀ g (u : U.toSubmodule),
      (e ⟨repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = repBaseChange E (J.galRep ℓ) g (e u)) :
    ∃ f : Hom A J, f ≠ 0 := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨-, hfinA, -⟩ := hT K A ℓ hℓK
  obtain ⟨-, hfinJ, -⟩ := hT K J ℓ hℓK
  have : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  have : FiniteDimensional ℚ_[ℓ] (J.V ℓ) := inferInstance
  have hVE := hSS ℚ_[ℓ] E _ _ (A.galRep ℓ) (hS K A ℓ)
  obtain ⟨φ, hφ0, hφ⟩ := exists_equivariant_ne_zero_of_common _ _ hVE U U' hU e he
  obtain ⟨ψ, hψ0, hψ⟩ := equivariantDescent ℚ_[ℓ] E _ _ _ (A.galRep ℓ) (J.galRep ℓ) ⟨φ, hφ0, hφ⟩
  exact exists_hom_ne_zero_of_equivariant hF hT A J ℓ ψ hψ0 hψ

end PkgI3

-- hsyn-fold: C10 trace comparison, from scratch/glue-c10/Trace.lean (pkg-I3 copy dropped).
namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped TensorProduct

/-- **C10, the characteristic-polynomial comparison (GLUE, proved from Mumford §19 Thm 4).**
For an endomorphism `φ` of an abelian variety over any field `k` there is one integer `t` that is
the trace of `V_ℓ(φ)` for every prime `ℓ ≠ char k` (N5 L788-790: "independent of the coefficient
prime"). -/
theorem trace_indep_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        LinearMap.trace ℚ_[ℓ] (A.V ℓ) ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) = (t : ℚ_[ℓ]) := by
  obtain ⟨P, -, hP⟩ := h k A φ
  refine ⟨-P.nextCoeff, fun ℓ _ hℓ I _ _ b => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    hP ℓ hℓ I b, Polynomial.nextCoeff_map (Int.castRingHom ℚ_[ℓ]).injective_int]
  simp

/-- The same integer for two primes: the traces at `ℓ₁` and `ℓ₂` are images of one integer. -/
theorem trace_eq_trace_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime] (h₁ : (ℓ₁ : k) ≠ 0) (h₂ : (ℓ₂ : k) ≠ 0)
    (I₁ I₂ : Type) [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (b₁ : Module.Basis I₁ ℚ_[ℓ₁] (A.V ℓ₁)) (b₂ : Module.Basis I₂ ℚ_[ℓ₂] (A.V ℓ₂)) :
    ∃ t : ℤ, LinearMap.trace ℚ_[ℓ₁] (A.V ℓ₁) ((homT (ℓ := ℓ₁) φ).baseChange ℚ_[ℓ₁]) = t ∧
      LinearMap.trace ℚ_[ℓ₂] (A.V ℓ₂) ((homT (ℓ := ℓ₂) φ).baseChange ℚ_[ℓ₂]) = t := by
  obtain ⟨t, ht⟩ := trace_indep_of_ell h k A φ
  exact ⟨t, ht ℓ₁ h₁ I₁ b₁, ht ℓ₂ h₂ I₂ b₂⟩

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
(pst at `ℓ`, every level; UNVERIFIED); Kato, Astérisque 295 (2004) §§9.2-9.4, (9.2.2) pp. 187-188
(de Rham, every level, newforms; checked by the locator audit), with `NewformOfEigenform` and
Brauer–Nesbitt for general cuspidal eigenforms (hence `ρ.IsSemisimple`); Scholl 1990
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
Brauer–Nesbitt, their Lemma 3.2): a semisimple `ρ` attached to a weight-one eigenform has finite
image. Consequence form. Semisimplicity cannot be dropped (a non-split extension can have the same
traces; locator audit, R15). Same as hdec-faithful L27(b). -/
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

/-- **I4-L6. Carayol at unramified primes** (Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411, the
case "conductor exponent 0"; coverage of every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`, read by the
locator audit; newform conductor `a(π_p) = v_p(N)`, Casselman 1973, locator UNVERIFIED). For a newform `f` of weight 2 and level `N` and a semisimple `ρ` attached to it, a
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
Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4 (statement VERIFIED in h-a011 §1.1 and by the locator
audit from the arXiv source; JAMS numbering UNVERIFIED)), for `p ≥ 5` only: at `p = 3` Pan excludes
`ρ̄|_{G_{ℚ₃}}^{ss} ≅ η ⊕ ηω`, and this leaf does not cover `p = 3`. Pan states the conclusion with
geometric Frobenius (`ρ ≅ ρ_g ⊗ ψ'`); the arithmetic-Frobenius trace form below follows with the
conjugate eigenform `g^ρ` (character `χ̄`) and `ψ = ψ'ε^{1−k}`, by `tr(M⁻¹) = tr M / det M`:
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

-- hsyn-fold: copied from scratch/leaf-push/PushDR.lean.
/-! ## leaf-push: T23, Fontaine's closure properties of de Rham representations -/

section Fontaine

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ ρ(σ)` is continuous for the Krull topology and the `p`-adic topology on matrices. -/
def ContRep {n : ℕ} (ρ : GQp p →* GL (Fin n) ℚ_[p]) : Prop :=
  Continuous fun σ => (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])

/-- **T23. Fontaine's closure properties.** Published statement: Fontaine, *Représentations
p-adiques des corps locaux I*, Astérisque 223 (1994), Exp. III, §1.5 (admissible representations
for a regular period ring form a Tannakian subcategory: stable under subobjects, quotients, direct
sums, tensor products, duals) applied to `B = B_dR` (regular, Exp. II §3 / Exp. III Thm 3.8;
numbering UNVERIFIED; also Brinon–Conrad, CMI notes, Thm 5.2.1, Prop. 6.3.3, 6.3.8). Lean form,
for continuous `ℚ_p`-linear representations of `G_{ℚ_p}` on `ℚ_pⁿ` and pkg-I4's predicate
`IsDeRham` (`dim_{ℚ_p} D_dR = n`, `D_dR` computed on `V^∨`, which is equivalent by the dual
clause): (i) invariance under change of basis; (ii) duals (`σ ↦ ρ(σ)⁻ᵀ`); (iii) subquotients:
if `ρ` is block upper triangular with diagonal blocks `ρ₁, ρ₂` (`ρ₁` the subrepresentation on
the first `a` coordinates, `ρ₂` the quotient), then `ρ` de Rham ⇒ `ρ₁, ρ₂` de Rham; (iv) direct
sums (block diagonal); (v) tensor products (Kronecker product, reindexed by `Fin a × Fin b ≃
Fin (a * b)`). Every clause is a special case of the published statement (matrix form of the
same representations); (i) is the basis independence of `dim D_dR`, a triviality included so
that the leaf is basis-free. Exact. -/
def T23_FontaineClosure : Prop :=
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]) (P : GL (Fin n) ℚ_[p]),
    (∀ σ, ρ' σ = P * ρ σ * P⁻¹) → (IsDeRham p ρ ↔ IsDeRham p ρ')) ∧
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose) →
    IsDeRham p ρ → IsDeRham p ρ') ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]) (X : GQp p → Matrix (Fin a) (Fin b) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) (X σ) 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ → IsDeRham p ρ₁ ∧ IsDeRham p ρ₂) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a * b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRham p ρ₁ → IsDeRham p ρ₂ → IsDeRham p ρ)

end Fontaine

end PkgI4

end



/-! (fast-environment copies of part_weight.lean's `IsConj`, `HTConj`; not used in Weight.lean) -/
namespace G0Galois
open PkgI4 (GaloisRep GaloisChar)

/-- `r` and `ρ'` are conjugate by a fixed matrix: `r(σ) = P ρ'(σ) P⁻¹`. -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **Hodge–Tate weights are invariant under conjugation (GLUE, about the definition
`PkgI4.LocalHasHTWeights`; STANDARD).** Enlarge the finite coefficient field `E` to contain the
entries of `P` and `P⁻¹` and use that `htMult` does not change under a finite extension of `E`
(`(ℂ_p(i) ⊗ V)^G` commutes with `E'/E` base change) nor under an `E'`-linear isomorphism. -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

end G0Galois

/-! ## g12-det: `HTConj` reduced to `HTExtend` (independence of the coefficient field) -/

section G12DetHTSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Hodge–Tate multiplicities do not depend on the finite coefficient field (GLUE, about the
definition `PkgI4.LocalHasHTWeights`; STANDARD).** If a `ℚ̄_p`-valued `ρ` has a model `ρ_E` over a
finite `E ⊆ ℚ̄_p` with weights `S`, then for every finite `E' ⊇ E` the model over `E'` (the same
matrices) has weights `S`. Argument: `E' ⊗_E E^n ≅ (E^n)^{[E':E]}` as `ℚ_p[G]`-modules (`G` acts
trivially on `E'`), so `dim_{ℚ_p} H_i(ρ_{E'}) = [E':E] dim_{ℚ_p} H_i(ρ_E)` and `htMult`, which divides
by `[E':ℚ_p]`, is unchanged. (The docstring of `LocalHasHTWeights` asserts this, STANDARD.) -/
def HTExtend : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : PkgI4.GQp p →* GL (Fin n) (PadicAlgCl p))
    (S : Multiset ℤ) (E E' : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'], E ≤ E' →
    ∀ ρE : PkgI4.GQp p →* GL (Fin n) E,
      (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
      PkgI4.HasHTWeights p ρE S →
      ∃ ρE' : PkgI4.GQp p →* GL (Fin n) E',
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E' (PadicAlgCl p)) (ρE' σ) = ρ σ) ∧
        PkgI4.HasHTWeights p ρE' S

/-- Conjugating a model by `P ∈ GL_n(E)` does not change the Hodge–Tate spaces' dimensions. -/
lemma finrank_htSpace_conj {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Type*} [Field E]
    [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
    (ρ ρ' : PkgI4.GQp p →* GL (Fin n) E) (P : GL (Fin n) E)
    (h : ∀ σ, ρ' σ = P⁻¹ * ρ σ * P) (i : ℤ) :
    Module.finrank ℚ_[p] (PkgI4.htSpace p ρ' i) = Module.finrank ℚ_[p] (PkgI4.htSpace p ρ i) := by
  let A : Matrix (Fin n) (Fin n) E := (P : Matrix (Fin n) (Fin n) E)
  let B : Matrix (Fin n) (Fin n) E := ((P⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
  have hAB : A * B = 1 := by simp [A, B]
  have hBA : B * A = 1 := by simp [A, B]
  have hρ' : ∀ σ, ((ρ' σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      B * (ρ σ : Matrix (Fin n) (Fin n) E) * A := by
    intro σ; rw [h σ]; simp [A, B]
  let LA : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin A).restrictScalars ℚ_[p]
  let LB : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E) := (Matrix.mulVecLin B).restrictScalars ℚ_[p]
  let TA := LinearMap.lcomp ℚ_[p] ℂ_[p] LA
  let TB := LinearMap.lcomp ℚ_[p] ℂ_[p] LB
  have hTA : ∀ φ ∈ PkgI4.htSpace p ρ i, TA φ ∈ PkgI4.htSpace p ρ' i := by
    intro φ hφ σ v
    have := hφ σ (A.mulVec v)
    simp only [TA, LA, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAB, Matrix.one_mul,
      ← Matrix.mulVec_mulVec]
    exact this
  have hTB : ∀ φ ∈ PkgI4.htSpace p ρ' i, TB φ ∈ PkgI4.htSpace p ρ i := by
    intro φ hφ σ v
    have := hφ σ (B.mulVec v)
    simp only [TB, LB, LinearMap.lcomp_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply] at this ⊢
    rw [hρ', Matrix.mulVec_mulVec, Matrix.mul_assoc _ A B, hAB, Matrix.mul_one] at this
    rw [Matrix.mulVec_mulVec]
    exact this
  let f : PkgI4.htSpace p ρ i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := TA.restrict hTA
  let g : PkgI4.htSpace p ρ' i →ₗ[ℚ_[p]] PkgI4.htSpace p ρ i := TB.restrict hTB
  have e : PkgI4.htSpace p ρ i ≃ₗ[ℚ_[p]] PkgI4.htSpace p ρ' i := LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
    (by
      apply LinearMap.ext; intro φ; apply Subtype.ext; apply LinearMap.ext; intro v
      simp [f, g, TA, TB, LA, LB, Matrix.mulVec_mulVec, hAB, hBA])
  exact e.finrank_eq.symm

/-- **`HTConj` from `HTExtend`.** -/
theorem htConj_of (hX : HTExtend) : HTConj := by
  intro ℓ _ n r ρ' S hconj hr
  obtain ⟨P, hP⟩ := hconj
  obtain ⟨E, hEfd, ρE, hmap, hHT⟩ := hr
  let T : Set (PadicAlgCl ℓ) :=
    Set.range (fun ij : Fin n × Fin n => (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2) ∪
    Set.range (fun ij : Fin n × Fin n =>
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) ij.1 ij.2)
  have hTfin : Finite T := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  have hadj : FiniteDimensional ℚ_[ℓ] (IntermediateField.adjoin ℚ_[ℓ] T) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E' : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) := E ⊔ IntermediateField.adjoin ℚ_[ℓ] T
  have hE'fd : FiniteDimensional ℚ_[ℓ] E' := IntermediateField.finiteDimensional_sup _ _
  obtain ⟨ρE', hmap', hHT'⟩ := hX ℓ n (r.restrictLocal ℓ) S E E' le_sup_left ρE hmap hHT
  have hmemT : ∀ x ∈ T, x ∈ E' := fun x hx =>
    (le_sup_right : IntermediateField.adjoin ℚ_[ℓ] T ≤ E') (IntermediateField.subset_adjoin _ _ hx)
  let Pm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨(P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j, hmemT _ (Or.inl ⟨(i, j), rfl⟩)⟩
  let Qm : Matrix (Fin n) (Fin n) E' := Matrix.of fun i j =>
    ⟨((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j,
      hmemT _ (Or.inr ⟨(i, j), rfl⟩)⟩
  let φ := algebraMap E' (PadicAlgCl ℓ)
  have hinj : Function.Injective (φ.mapMatrix : Matrix (Fin n) (Fin n) E' → _) := by
    intro M N hMN
    exact Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hMN i) j)
  have hPm : φ.mapMatrix Pm = (P : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hQm : φ.mapMatrix Qm =
      ((P⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := by
    ext i j; rfl
  have hPQ : Pm * Qm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  have hQP : Qm * Pm = 1 := hinj (by rw [map_mul, map_one, hPm, hQm]; simp)
  let P' : GL (Fin n) E' := ⟨Pm, Qm, hPQ, hQP⟩
  have hP' : Matrix.GeneralLinearGroup.map φ P' = P := by
    apply Units.ext
    exact hPm
  let ρ'E : PkgI4.GQp ℓ →* GL (Fin n) E' :=
    { toFun := fun σ => P'⁻¹ * ρE' σ * P'
      map_one' := by simp
      map_mul' := fun σ τ => by simp [mul_assoc] }
  refine ⟨E', hE'fd, ρ'E, ?_, ?_⟩
  · intro σ
    change Matrix.GeneralLinearGroup.map φ (P'⁻¹ * ρE' σ * P') = _
    rw [map_mul, map_mul, map_inv, hP', hmap' σ]
    change P⁻¹ * r.toHom (PkgI4.decomp ℓ σ) * P = ρ'.toHom (PkgI4.decomp ℓ σ)
    rw [hP]
    group
  · intro w
    unfold PkgI4.htMult
    rw [finrank_htSpace_conj ρE' ρ'E P' (fun σ => rfl) (-w)]
    exact hHT' w

end G0Galois

end

end G12DetHTSec

#print axioms G0Galois.finrank_htSpace_conj
#print axioms G0Galois.htConj_of

/-! ## g12-det: `HTExtend` proved (Hodge–Tate multiplicities do not depend on the coefficient
field) -/

section G12DetHTExtSec

noncomputable section

namespace G0Galois

section Extend

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {E E' : Type} [Field E] [Field E'] [Algebra ℚ_[p] E]
  [Algebra ℚ_[p] E'] [Algebra E E'] [IsScalarTower ℚ_[p] E E'] [FiniteDimensional ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E'] {m : ℕ} (b : Module.Basis (Fin m) E E')

/-- `v ↦ (v_a • b_k)_a`. -/
def jk (k : Fin m) : (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E') :=
  (LinearMap.pi fun a => (LinearMap.toSpanSingleton E E' (b k)).comp (LinearMap.proj a) :
    (Fin n → E) →ₗ[E] (Fin n → E')).restrictScalars ℚ_[p]

/-- `w ↦ (b.coord k (w_a))_a`. -/
def ck (k : Fin m) : (Fin n → E') →ₗ[ℚ_[p]] (Fin n → E) :=
  (LinearMap.pi fun a => (b.coord k).comp (LinearMap.proj a) :
    (Fin n → E') →ₗ[E] (Fin n → E)).restrictScalars ℚ_[p]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_apply (k : Fin m) (v : Fin n → E) (a : Fin n) : jk (p := p) b k v a = v a • b k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_apply (k : Fin m) (w : Fin n → E') (a : Fin n) :
    ck (p := p) b k w a = b.repr (w a) k := rfl

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma jk_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    jk (p := p) b k (M.mulVec v) = (M.map (algebraMap E E')).mulVec (jk (p := p) b k v) := by
  funext a
  simp only [jk_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  ring

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_mulVec (k : Fin m) (M : Matrix (Fin n) (Fin n) E) (w : Fin n → E') :
    ck (p := p) b k ((M.map (algebraMap E E')).mulVec w) = M.mulVec (ck (p := p) b k w) := by
  funext a
  simp only [ck_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum,
    Finsupp.coe_finset_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma ck_jk (k l : Fin m) (v : Fin n → E) :
    ck (p := p) b l (jk (p := p) b k v) = if k = l then v else 0 := by
  funext a
  rw [ck_apply, jk_apply, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
    Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> simp

omit [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E'] in
lemma sum_jk_ck (w : Fin n → E') : ∑ k, jk (p := p) b k (ck (p := p) b k w) = w := by
  funext a
  simp only [Finset.sum_apply, jk_apply, ck_apply]
  exact b.sum_repr (w a)

/-- `htSpace` of the extended model is `htSpace` of the model, `m` times. -/
def htSpaceExtendEquiv (ρE : PkgI4.GQp p →* GL (Fin n) E) (i : ℤ) :
    PkgI4.htSpace p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) i ≃ₗ[ℚ_[p]]
      (Fin m → PkgI4.htSpace p ρE i) where
  toFun φ k := ⟨φ.1.comp (jk (p := p) b k), by
    intro σ v
    have := φ.2 σ (jk (p := p) b k v)
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [jk_mulVec]
    exact this⟩
  invFun ψ := ⟨∑ k, (ψ k).1.comp (ck (p := p) b k), by
    intro σ w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply,
      map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := (ψ k).2 σ (ck (p := p) b k w)
    have hm : ((((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) σ :
        GL (Fin n) E') : Matrix (Fin n) (Fin n) E') =
        ((ρE σ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (algebraMap E E') := rfl
    rw [hm, ck_mulVec]
    exact h⟩
  left_inv φ := by
    apply Subtype.ext
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [← map_sum, sum_jk_ck]
  right_inv ψ := by
    funext k
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_eq_single k]
    · rw [ck_jk, if_pos rfl]
    · intro l _ hl
      rw [ck_jk, if_neg (Ne.symm hl), map_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  map_add' φ ψ := by
    funext k; apply Subtype.ext; rfl
  map_smul' c φ := by
    funext k; apply Subtype.ext; rfl

include b in
lemma htMult_extend (ρE : PkgI4.GQp p →* GL (Fin n) E) (w : ℤ) :
    PkgI4.htMult p ((Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE) w =
      PkgI4.htMult p ρE w := by
  have hm : 0 < m := by
    by_contra h
    have h0 : m = 0 := by omega
    subst h0
    have := b.index_nonempty
    exact (IsEmpty.false this.some)
  unfold PkgI4.htMult
  rw [(htSpaceExtendEquiv b ρE (-w)).finrank_eq,
    ← (Finsupp.linearEquivFunOnFinite ℚ_[p] (PkgI4.htSpace p ρE (-w)) (Fin m)).finrank_eq,
    Module.finrank_finsupp, Fintype.card_fin, ← Module.finrank_mul_finrank ℚ_[p] E E',
    Module.finrank_eq_card_basis b, Fintype.card_fin, mul_comm (Module.finrank ℚ_[p] E) m]
  exact Nat.mul_div_mul_left _ _ hm

end Extend

/-- **`HTExtend`, proved.** -/
theorem htExtend : HTExtend := by
  intro p _ n ρ S E E' _ _ hle ρE hmap hHT
  letI : Algebra E E' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[p] E E' := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite E E' := Module.Finite.of_restrictScalars_finite ℚ_[p] E E'
  haveI : Module.Free E E' := Module.Free.of_divisionRing E E'
  let b := Module.finBasis E E'
  refine ⟨(Matrix.GeneralLinearGroup.map (algebraMap E E')).comp ρE, ?_, ?_⟩
  · intro σ
    rw [← hmap σ]
    apply Units.ext
    ext i j
    rfl
  · intro w
    rw [htMult_extend b ρE w]
    exact hHT w

end G0Galois

end

end G12DetHTExtSec

#print axioms G0Galois.htExtend
