import ZInQKernel.HDecomp.Analytic.Uniformization
import ZInQKernel.HDecomp.Analytic.QMLattice
import ZInQKernel.HDecomp.QM.Pin

/-! # r1b-state, part 0: pkg-I1's definitions (`PkgI1`), copied verbatim from
`scratch/h-decomposition/Leaves.lean` lines 104-316 (the `PkgI1` section through
`QMHauptmodul`), closed after `QMHauptmodul`. -/

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


/-! # r1b-state, part 1: R1(b), the analytic uniformization clause of R1, stated concretely

Everything is over genuine definitions of the build:
* bp-analytic's complex tori `BPAnalytic.Torus Λ = ℂ²/Λ`, its QM lattice
  `BPAnalytic.QM.qmLattice hτ = ι(𝒪)(τ, 1)ᵀ` and its uniformization predicate
  `BPAnalytic.Uniformization.IsUniformization` (an isomorphism of complex Lie groups
  `ℂ²/Λ ≃ A(ℂ)`, phrased through regular functions; `ZInQKernel/HDecomp/Analytic/`);
* the QM objects `LeafQM.AV.QML3`, their classes `M3`, the point bijections `PtEquiv` and the
  repaired clause list `R1fpProps` (with qm-pin's `R1famProps`, `R1univProps`) of
  `ZInQKernel/HDecomp/QM/`;
* complex points `fieldPt ℂ ⟶ Y` of the `ℚ`-scheme `Y` and regular functions on its Zariski opens,
  evaluated at those points through Mathlib's `Scheme.SpecToEquivOfField` and
  `Scheme.evaluation` (as `LeafQM.AV.ToP1.val` does).
No `sorry`, no `axiom`. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic Matrix
open scoped Topology

/-! ## §1 The QM torus at `τ` and QM-compatible uniformizations -/

/-- `ι(a)` (bp-analytic's real embedding `B → M₂(ℝ)`, N5's) as a complex matrix. -/
def iotaC (a : LeafQM.B) : Matrix (Fin 2) (Fin 2) ℂ :=
  (BPAnalytic.QM.iota a).map (fun r : ℝ => (r : ℂ))

theorem latVec_eq (a : LeafQM.B) (τ : ℂ) : QM.latVec a τ = iotaC a *ᵥ ![τ, 1] := rfl

/-- **`φ : ℂ²/Λ_τ ≃ P.A(ℂ)` is a QM-compatible analytic uniformization of `P`**: an isomorphism
of complex Lie groups (bp-analytic's `IsUniformization`) carrying the action of `a ∈ 𝒪` by the
matrix `ι(a)` on `ℂ²` (which preserves `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, `iotaC_mem` below) to the action of
`ι_P(a)` on `P.A(ℂ)` (`qmAct`). -/
structure IsQMUnif (P : QML3 ℂ) {τ : ℂ} (hτ : τ.im ≠ 0)
    (φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)) : Prop where
  unif : Uniformization.IsUniformization P.A (QM.qmLattice hτ) φ
  iota_compat : ∀ (a : O) (v : Fin 2 → ℂ),
    φ (proj (QM.qmLattice hτ) (iotaC (a : LeafQM.B) *ᵥ v)) =
      qmAct P.q ℂ a (φ (proj (QM.qmLattice hτ) v))

/-- **… and it carries the standard level-3 structure of the torus** `a ↦ [ι(a)(τ, 1)ᵀ/3]`
(an `𝒪`-linear map `𝒪 → (ℂ²/Λ_τ)[3]` with kernel `3𝒪`: `level_linear`, `level_ker` below) to the
level structure `η` of `P`. This pins the class of `P` given `τ` (the analytic family of the
moduli problem over `ℍ`). -/
def IsQMUnifLevel (P : QML3 ℂ) {τ : ℂ} (hτ : τ.im ≠ 0)
    (φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)) : Prop :=
  IsQMUnif P hτ φ ∧
    ∀ a : O, P.e.eta a = φ (proj (QM.qmLattice hτ) ((1 / 3 : ℂ) • QM.latVec (a : LeafQM.B) τ))

/-! ## §2 Complex points of `Y` and regular functions on them -/

/-- The scheme point of `X` under a complex point `y : Spec ℂ → X`. -/
def ptOfS {X : Scheme.{0}} (y : Spec (CommRingCat.of ℂ) ⟶ X) : X :=
  (Scheme.SpecToEquivOfField ℂ X y).1

open Classical in
/-- The value `s(y) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_X)` at a complex point `y ∈ U(ℂ)`:
the image of `s(x) ∈ κ(x)` under the residue embedding `κ(x) → ℂ` of `y` (`0` if `y ∉ U(ℂ)`; only
used on `U(ℂ)`). -/
def evalS {X : Scheme.{0}} (y : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens) (s : Γ(X, U)) : ℂ :=
  if h : ptOfS y ∈ U then
    (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation U _ h s)
  else 0

/-- The scheme point of `Y` under a complex point `y : Spec ℂ → Y` over `ℚ`. -/
def ptOf {Y : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt ℂ ⟶ Y) : Y.left := ptOfS y.left

/-- The value at a complex point of `Y` over `ℚ` of a regular function on a Zariski open. -/
def evalC {Y : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt ℂ ⟶ Y) (U : Y.left.Opens)
    (s : Γ(Y.left, U)) : ℂ := evalS y.left U s

/-- The upper half plane as a subset of `ℂ`. -/
def UHP : Set ℂ := {τ | 0 < τ.im}

/-! ## §3 The leaf -/

/-- **R1(b) clause list, family form** (rv-blueprints Q3), for a candidate `(Y, Φ)` of R1(a):

(a) *every complex object occurs*: every `P : QML3 ℂ` has a QM-compatible analytic
uniformization `ℂ²/Λ_τ ≃ P.A(ℂ)` for some `τ ∈ ℍ`;

(b) *every `τ ∈ ℍ` occurs, in a family*: there is a map `y : ℍ → Y(ℂ)` (values off `ℍ` are not
used) such that for every `τ ∈ ℍ` the class `Φ_ℂ(y(τ))` is the class of an object `P_τ` with a
QM-compatible uniformization by `Λ_τ` carrying the standard level structure of the torus to
`η_{P_τ}`;

(c) *the family is holomorphic*: for every Zariski open `U ⊆ Y` and every regular function
`s ∈ Γ(U, 𝒪_Y)`, the set `{τ ∈ ℍ : y(τ) ∈ U(ℂ)}` is open and `τ ↦ s(y(τ))` is holomorphic on it.
(So `y` is a holomorphic map `ℍ → Y(ℂ)^an`; in particular `τ ↦ π(y(τ)) ∈ P¹(ℂ)` is holomorphic for
every morphism `π : Y → P¹`, `holomorphicP1On_of_family` below.) -/
def R1bProps (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) : Prop :=
  (∀ P : QML3 ℂ, ∃ (τ : ℂ) (hτ : 0 < τ.im)
      (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)), IsQMUnif P hτ.ne' φ) ∧
  ∃ y : ℂ → (fieldPt ℂ ⟶ Y),
    (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) ∧
    (∀ (U : Y.left.Opens) (s : Γ(Y.left, U)),
      IsOpen {τ : ℂ | 0 < τ.im ∧ ptOf (y τ) ∈ U} ∧
      DifferentiableOn ℂ (fun τ => evalC (y τ) U s) {τ : ℂ | 0 < τ.im ∧ ptOf (y τ) ∈ U})

/-- **LEAF R1(b) (Shimura–Deligne, complex uniformization in family form).** Some candidate
`(Y, Φ)` satisfying R1(a)'s repaired clause list `R1fpProps` (the field-point leaf `R1fp`)
satisfies the family clauses `R1bProps`.

*Published statement.* Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3 (the family
`A_τ = ℂ²/ι(𝒪)(τ, 1)ᵀ`, `τ ∈ ℍ`, with the Riemann form `Trd(μ⁻¹xȳ)` and its level structures, and
the holomorphic map `ℍ → V(ℂ)` onto a component of the canonical model); Deligne, Sém. Bourbaki
389 (1971), §4 (the canonical model as moduli space of the PEL problem, with the complex
uniformization `Sh_K(ℂ) = G(ℚ)\(X × G(𝔸_f)/K)` of its analytification), (all locators
UNVERIFIED; the audit read Deligne §§4.9-4.17 for R1(a), not this part).

*Why a consequence, never stronger.* `Y = Y₃` with `Φ` the moduli bijection (R1(a)); for the
type-`μ` PEL problem, `Y₃(ℂ)^an = G(ℚ)\(ℍ^± × G(𝔸_f)/K₃)`, and the component of `(τ, 1)` carries
the polarized object `(ℂ²/Λ_τ, ι, E_μ, η_τ)` with `η_τ(a) = [ι(a)(τ, 1)ᵀ/3]`; forgetting `E_μ`
(Lemma P, rv-qm-polar: it is the unique type-`μ` principal polarization) gives (b). The map
`τ ↦ (τ, 1)` is holomorphic into the analytification and regular functions are holomorphic on
it, which is (c). Clause (a) is the surjectivity of the uniformization (every complex point lies
in some component, and on the component of `g ∈ G(𝔸_f)` the object is `ℂ²/ι(𝒪_g)(τ, 1)ᵀ` with
`𝒪_g ≅ 𝒪`; with class number one of `𝒪` (Eichler) and the unit `1 + i` of norm `−1` the lattice is
`c·ι(𝒪)(τ', 1)ᵀ` with `Im τ' > 0`; level structures are forgotten in (a)). Nothing is claimed
about the other components of `Y₃(ℂ)` beyond (a), nor about polarizations, theta functions or
`π`. -/
def R01b_ComplexUniformization' : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ R1bProps Y Φ

/-! ## §4 Glue (proved): `R1bProps` holds for every candidate satisfying `R1fpProps` -/

theorem ptOfS_comp {X X' : Scheme.{0}} (h : X' ⟶ X) (y : Spec (CommRingCat.of ℂ) ⟶ X') :
    ptOfS (y ≫ h) = h (ptOfS y) := by
  unfold ptOfS
  rw [specToEquivOfField_comp_right]

theorem evalS_comp {X X' : Scheme.{0}} (h : X' ⟶ X) (y : Spec (CommRingCat.of ℂ) ⟶ X')
    (U : X.Opens) (s : Γ(X, U)) :
    evalS (y ≫ h) U s = evalS y (h ⁻¹ᵁ U) (h.app U s) := by
  unfold evalS ptOfS
  generalize hp : Scheme.SpecToEquivOfField ℂ X (y ≫ h) = p
  rw [specToEquivOfField_comp_right] at hp
  subst hp
  dsimp only
  split_ifs with h1 h2 h2
  · rw [ConcreteCategory.comp_apply, Scheme.evaluation_naturality_apply]
    rfl
  · exact (h2 h1).elim
  · exact (h1 h2).elim
  · rfl

theorem ptOf_comp {Y Y' : Over (Spec (CommRingCat.of ℚ))} (g : Y' ⟶ Y) (y : fieldPt ℂ ⟶ Y') :
    ptOf (y ≫ g) = g.left (ptOf y) :=
  ptOfS_comp g.left y.left

theorem evalC_comp {Y Y' : Over (Spec (CommRingCat.of ℚ))} (g : Y' ⟶ Y) (y : fieldPt ℂ ⟶ Y')
    (U : Y.left.Opens) (s : Γ(Y.left, U)) :
    evalC (y ≫ g) U s = evalC y (g.left ⁻¹ᵁ U) (g.left.app U s) :=
  evalS_comp g.left y.left U s

/-- **Transport along a morphism compatible with the point bijections.** -/
theorem R1bProps.of_hom {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} (g : Y' ⟶ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ g))
    (h : R1bProps Y' Φ') : R1bProps Y Φ := by
  obtain ⟨ha, y, hb, hc⟩ := h
  refine ⟨ha, fun τ => y τ ≫ g, fun τ hτ => ?_, fun U s => ?_⟩
  · obtain ⟨P, φ, hP, hu⟩ := hb τ hτ
    exact ⟨P, φ, (hg ℂ (y τ)).symm.trans hP, hu⟩
  · obtain ⟨ho, hd⟩ := hc (g.left ⁻¹ᵁ U) (g.left.app U s)
    have e1 : {τ : ℂ | 0 < τ.im ∧ ptOf (y τ ≫ g) ∈ U} =
        {τ : ℂ | 0 < τ.im ∧ ptOf (y τ) ∈ g.left ⁻¹ᵁ U} := by
      ext τ
      simp only [Set.mem_setOf_eq, ptOf_comp]
      rfl
    rw [e1]
    exact ⟨ho, hd.congr fun τ _ => evalC_comp g (y τ) U s⟩

/-- **R1(b) for every candidate (glue, proved).** If the leaf holds, then every `(Y, Φ)`
satisfying `R1fpProps` satisfies `R1bProps`: by qm-pin's `phi_part` (from `R1univProps` of `Y`)
the leaf's witness maps to `Y` compatibly with `Φ`, and `R1bProps` transports forward. So the
existential leaf serves consumers that quantify over all `(Y, Φ, π)` (g0-split's pieces), with
no uniqueness glue (`PinUnique`, `MobiusGlue`). -/
theorem r1bProps_of_leaf (h : R01b_ComplexUniformization') {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ) : R1bProps Y Φ := by
  obtain ⟨Y₀, Φ₀, h1₀, hb⟩ := h
  obtain ⟨g, hg⟩ := Pin.phi_part (Pin.R1fpProps.univ h1) h1₀
  exact R1bProps.of_hom g hg hb

end R1bState
