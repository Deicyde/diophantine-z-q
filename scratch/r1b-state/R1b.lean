import ZInQKernel.HDecomp.Analytic.Uniformization
import ZInQKernel.HDecomp.Analytic.QMLattice
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.Assembly

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
abbrev ptOfS {X : Scheme.{0}} (y : Spec (CommRingCat.of ℂ) ⟶ X) : X :=
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
      simp only [Set.mem_ofPred_eq, ptOf_comp]
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

/-! # r1b-state, part 2: the `π`-form of clause (c) (rv-blueprints Q3), proved from `R1bProps`

`τ ↦ π(y(τ)) ∈ P¹(ℂ)` is holomorphic for every morphism `π : Y → P¹` (`LeafQM.AV.ToP1`, by
charts). Holomorphy into `P¹(ℂ) = OnePoint ℂ` is stated by charts: near every point the map is
`h` or `1/h` (`recipP1`, with `1/0 = ∞` written out, not Lean's `x/0 = 0`) for a holomorphic `h`. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj LeafQM.AV
open scoped Topology

/-- `z ↦ 1/z` into `P¹(ℂ)`, with `1/0 = ∞`. -/
def recipP1 (z : ℂ) : OnePoint ℂ := if z = 0 then OnePoint.infty else ((z⁻¹ : ℂ) : OnePoint ℂ)

/-- **Holomorphic maps into `P¹(ℂ)`, by charts.** `F` is holomorphic on `D` if near each point of
`D` it is `h` (chart `t`) or `1/h` (chart `1/t`) for a holomorphic `h : ℂ → ℂ`. (Equivalent to the
usual definition: such an `F` is continuous, and holomorphic in both charts of `P¹`.) -/
def HolomorphicP1On (F : ℂ → OnePoint ℂ) (D : Set ℂ) : Prop :=
  ∀ τ₀ ∈ D, ∃ N ∈ 𝓝 τ₀, ∃ h : ℂ → ℂ, DifferentiableOn ℂ h N ∧
    ((∀ τ ∈ N, F τ = (h τ : OnePoint ℂ)) ∨ (∀ τ ∈ N, F τ = recipP1 (h τ)))

theorem evaluation_res (X : Scheme.{0}) {U V : X.Opens} (hUV : U ≤ V) (x : X) (hx : x ∈ U)
    (s : Γ(X, V)) :
    X.evaluation U x hx (X.presheaf.map (homOfLE hUV).op s) = X.evaluation V x (hUV hx) s := by
  simp only [Scheme.evaluation, ConcreteCategory.comp_apply]
  rw [TopCat.Presheaf.germ_res_apply]

theorem val_of_mem {X : Scheme.{0}} (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X)
    (h : ptOfS y ∈ π.U) : π.val y = ((evalS y π.U π.f : ℂ) : OnePoint ℂ) := by
  have h' : (Scheme.SpecToEquivOfField ℂ X y).1 ∈ π.U := h
  unfold ToP1.val evalS ptOfS
  rw [dif_pos h', dif_pos h']

theorem val_of_not_mem {X : Scheme.{0}} (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X)
    (h : ptOfS y ∉ π.U) : π.val y = OnePoint.infty := by
  have h' : (Scheme.SpecToEquivOfField ℂ X y).1 ∉ π.U := h
  unfold ToP1.val
  rw [dif_neg h']

theorem evalS_g_eq_zero {X : Scheme.{0}} (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X)
    (hV : ptOfS y ∈ π.V) (hU : ptOfS y ∉ π.U) : evalS y π.V π.g = 0 := by
  unfold evalS
  rw [dif_pos hV]
  have : X.evaluation π.V _ hV π.g = 0 := by
    rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, π.basicOpen_g]
    exact fun hx => hU (TopologicalSpace.Opens.mem_inf.mp hx).1
  rw [this, map_zero]

theorem evalS_f_mul_g {X : Scheme.{0}} (π : ToP1 X) (y : Spec (CommRingCat.of ℂ) ⟶ X)
    (hU : ptOfS y ∈ π.U) (hV : ptOfS y ∈ π.V) : evalS y π.U π.f * evalS y π.V π.g = 1 := by
  unfold evalS
  rw [dif_pos hU, dif_pos hV]
  have hUV : ptOfS y ∈ π.U ⊓ π.V := TopologicalSpace.Opens.mem_inf.mpr ⟨hU, hV⟩
  have e := congrArg (X.evaluation (π.U ⊓ π.V) _ hUV) π.inv
  rw [map_mul, map_one, evaluation_res, evaluation_res] at e
  rw [← map_mul, e, map_one]

/-- **Glue (proved): the `π`-form of clause (c).** For a family `y : ℍ → Y(ℂ)` along which regular
functions are holomorphic, `τ ↦ π(y(τ))` is holomorphic into `P¹(ℂ)` for every `π : Y → P¹`. -/
theorem holomorphicP1On_of_family {Y : Over (Spec (CommRingCat.of ℚ))} (y : ℂ → (fieldPt ℂ ⟶ Y))
    (hc : ∀ (U : Y.left.Opens) (s : Γ(Y.left, U)),
      IsOpen {τ : ℂ | 0 < τ.im ∧ ptOf (y τ) ∈ U} ∧
      DifferentiableOn ℂ (fun τ => evalC (y τ) U s) {τ : ℂ | 0 < τ.im ∧ ptOf (y τ) ∈ U})
    (π : ToP1 Y.left) :
    HolomorphicP1On (fun τ => π.val (K := ℂ) (y τ).left) UHP := by
  intro τ₀ hτ₀
  by_cases hU : ptOf (y τ₀) ∈ π.U
  · obtain ⟨ho, hd⟩ := hc π.U π.f
    exact ⟨_, ho.mem_nhds ⟨hτ₀, hU⟩, _, hd, Or.inl fun τ hτ => val_of_mem π (y τ).left hτ.2⟩
  · have hV : ptOf (y τ₀) ∈ π.V := by
      have : ptOf (y τ₀) ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
      exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hU
    obtain ⟨ho, hd⟩ := hc π.V π.g
    refine ⟨_, ho.mem_nhds ⟨hτ₀, hV⟩, _, hd, Or.inr fun τ hτ => ?_⟩
    by_cases hU' : ptOf (y τ) ∈ π.U
    · refine (val_of_mem π (y τ).left hU').trans ?_
      have e : evalC (y τ) π.U π.f * evalC (y τ) π.V π.g = 1 :=
        evalS_f_mul_g π (y τ).left hU' hτ.2
      show ((evalC (y τ) π.U π.f : ℂ) : OnePoint ℂ) = _
      unfold recipP1
      rw [if_neg (right_ne_zero_of_mul_eq_one e)]
      exact congrArg _ (eq_inv_of_mul_eq_one_left e)
    · refine (val_of_not_mem π (y τ).left hU').trans ?_
      have h0 : evalC (y τ) π.V π.g = 0 := evalS_g_eq_zero π (y τ).left hτ.2 hU'
      simp only [recipP1, h0, if_pos]

/-- **R1(b) in exactly the form rv-blueprints Q3 asks for (proved from `R1bProps`).** Every
`τ ∈ ℍ` occurs (`P_τ`, in a family `y`), and `τ ↦ π(Φ⁻¹[P_τ])` is holomorphic on `ℍ` for every
morphism `π : Y → P¹`. -/
theorem q3_form_of_R1bProps {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h : R1bProps Y Φ) : ∃ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : BPAnalytic.Torus (BPAnalytic.QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) ∧
      ∀ π : ToP1 Y.left, HolomorphicP1On (fun τ => π.val (K := ℂ) (y τ).left) UHP := by
  obtain ⟨-, y, hb, hc⟩ := h
  exact ⟨y, hb, holomorphicP1On_of_family y hc⟩

end R1bState

/-! # r1b-state, part 3: g0-thetapoint's `FibreQMPeriod` from R1(b)

`FibreQMPeriod'` below is g0-thetapoint's `HSyn.G0Split.ThetaPt.FibreQMPeriod`
(scratch/g0-thetapoint/part_theta.lean) restated over the build's declarations, with the same
text except for names: the build's `PkgI3.AbVar` stands for the scratch copy
`ZInQ.DefFaltings.AbVar` (in the build `ZInQ.DefFaltings` uses `PkgI3.AbVar` itself, so
`LeafAdopt.abVarEquiv` is the identity and is dropped), and `CPts`, `IsUniformization` are the
build's `ZInQ.LeafPush2` ones (the scratch file's `HSyn.G0Split` copies have the same text).
`FibreOver'` is g0-split's `FibreOver` with the same change.

It follows from the leaf `R01b_ComplexUniformization'` (through `r1bProps_of_leaf`, used for
clause (a) at the fibre and for the family clauses inside the comparison), the leaf
`PkgI1.QMHauptmodul`, and two named glue Props:
* `HauptmodulCompare` (the Möbius comparison of `τ ↦ π(P_τ)` with `QMHauptmodul`'s `f`, used only
  where `π` is finite and nonzero, as the review's trap list requires);
* `UnifBaseChange` (transport of a uniformization along base change of the fibre).
The rest is proved: the embedding `ℚ̄ → ℂ`, the base change of the fibre object to `ℂ` (from the
naturality clause of `R1fpProps`), the value of `π` there (`ToP1.val_comp`), and `J(u) ≠ 0`. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic ZInQ ZInQ.JHeight

/-- g0-split's `FibreOver` (with `PkgI3.AbVar` for def-faltings' copy). -/
def FibreOver' (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : PkgI3.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- g0-thetapoint's `FibreQMPeriod` (GLUE G19), over the build's declarations. -/
def FibreQMPeriod' : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : PkgI3.AbVar K.K), FibreOver' Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
      Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **GLUE (the Hauptmodul comparison; the analytic half of F1).** For a candidate `(Y, Φ, π)`
satisfying R1(a)'s clauses, R2's clauses and R1(b)'s family clauses, and given `QMHauptmodul`:
if a complex object `P` with class `Φ_ℂ(y)` has a QM-compatible uniformization by `Λ_τ`
(`τ ∈ ℍ`) and `π(y)` is **finite and nonzero**, `π(y) = c`, then `jDen(Ω(τ)) ≠ 0` and
`jNum(Ω(τ))/jDen(Ω(τ)) = c`.

Why true (model argument, SPECULATIVE until proved; no human review). Let `f` be
`QMHauptmodul`'s function and `y_τ` the family of `R1bProps` (b). `F(τ) = π(y_τ)` is holomorphic
into `P¹` (`q3_form_of_R1bProps`); it is `Γ*`-invariant, because for `γ ∈ Γ* = ι(N_B(𝒪)⁺)` the
lattice `Λ_{γτ}` is a scalar multiple of `ι(n)Λ_τ` (`γ = ι(n)`), so the QM pairs at `τ` and `γτ` are
twist-isomorphic (`(A, ι∘Ad n) ≅ (A, ι)`-type), and `π` is constant on twist classes (R2's fibre
clause, transported from `ℚ̄`- to `ℂ`-points: `π` is determined by its values on the dense set of
`ℚ̄`-points). So `F = g ∘ f` with `g : P¹ → P¹` holomorphic (`f` identifies `Γ*\ℍ` with `P¹`),
`g` is injective (R2's fibre clause: `π`-fibres are twist classes = `Γ*`-orbits, by R1(b)(a) and
the lattice computation), hence a Möbius map; `F` and `f` take the values `0, ∞, −16/27` at the
CM points of discriminants `−4, −3, −24` (R2's CM clauses; `QMHauptmodul`'s value clauses), so
`g = id` and `π(y_τ) = f(τ)`. For `P` uniformized at `τ` (any level structure), `π(y) = π(y_τ)`
(same QM pair). Finally, where `f(τ) = c` is finite and nonzero, `jDen(Ω(τ)) ≠ 0`: `jDen ∘ Ω =
(4ψ₄ ∘ Ω)⁵` and `ψ₄ ∘ Ω` is a nonzero modular form of weight 8 for `Γ*` (signature `(0; 2, 4, 6)`,
orbifold degree `8/2 · (1/12)·… = 1/3`), so its only zeros are at the order-6 elliptic orbit, the
disc `−3` points, where `f = ∞`; so `f(τ) = jNum/jDen` there by `QMHauptmodul`'s second clause.

The guards are needed. Without `c ≠ ∞` the clause would claim `jNum/jDen = π(y)` at the disc `−3`
point, where Lean's `x/0 = 0` makes the left side `0` but `π = ∞`; `c ≠ 0` keeps the clause off
the disc `−4` points, where Lin–Yang's weighted representative (`ψ₄ = 144j`, `χ₁₀ = −j³/4`)
degenerates (it is not used for `J(u)`, which is nonzero for `u ∉ 𝒞`). The comparison is with the
fixed `Ω(τ)` (the type-`μ` principal polarization of rv-qm-polar's Lemma P), never with every
period matrix of `Λ_τ`: at CM points a product polarization makes the theta product vanish. -/
def HauptmodulCompare : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → R1bProps Y Φ → PkgI1.QMHauptmodul →
    ∀ (y : fieldPt ℂ ⟶ Y) (P : QML3 ℂ), Φ ℂ y = M3.mk P →
    ∀ (τ : ℂ) (hτ : 0 < τ.im) (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
      IsQMUnif P hτ.ne' φ →
    ∀ c : ℂ, c ≠ 0 → π.val (K := ℂ) y.left = OnePoint.some c →
      PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧ PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = c

/-- **GLUE (uniformization along base change; no analytic input).** Let `A` be an abelian
variety over a number field `K`, `emb : K → ℚ̄` with `A_ℚ̄ ≅ P.A`, `ε : ℚ̄ → ℂ`, and `Pc` the base
change of `P` along `ε` (`IsBaseChangeOf`). A uniformization `φ : ℂ²/Λ_τ ≃ Pc.A(ℂ)` (bp-analytic's
`IsUniformization`, the `ι`-compatibility is not needed) gives a uniformization of `A(ℂ)_σ` at
`σ = ε ∘ emb` with kernel `Λ_τ` (leaf-push2's `IsUniformization`). Why true: `A(ℂ)_σ`,
`(A_ℚ̄)(ℂ)_ε`, `P.A(ℂ)_ε` and `Pc.A(ℂ)` are identified by the pullback squares (Yoneda), as groups
(the identifications are morphisms of group objects after composing with the isomorphism, which
can be chosen to respect the identity: an isomorphism of schemes between abelian varieties is a
translate of a homomorphism, rigidity); regular functions on opens of `A` pull back to regular
functions on opens of `Pc.A`, so bp-analytic's (i) gives openness and holomorphy. -/
def UnifBaseChange : Prop :=
  ∀ (K : GlueAssembly.NF) (A : PkgI3.AbVar K.K) (emb : K.K →+* Qbar) (P : QML3 Qbar)
    (ε : Qbar →+* ℂ) (Pc : QML3 ℂ),
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) →
    IsBaseChangeOf ε P Pc →
    ∀ (τ : ℂ) (hτ : τ.im ≠ 0) (φ : Torus (QM.qmLattice hτ) ≃+ Additive (Pc.A.Pt ℂ)),
      Uniformization.IsUniformization Pc.A (QM.qmLattice hτ) φ →
    ∃ Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (ε.comp emb),
      ZInQ.LeafPush2.IsUniformization (ε.comp emb) (QM.qmLattice hτ) Φu

/-- `J(u) ≠ 0` off the contact set. -/
theorem jmap_ne_zero (u : ℚ) (hu : u ∉ contactSet) : Jmap u ≠ 0 := by
  have hF : u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60) ≠ 0 := by
    simp only [contactSet, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hu
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_
    · exact h0
    all_goals intro h; first
      | exact h1 (by linarith) | exact h2 (by linarith) | exact h3 (by linarith)
      | exact h4 (by linarith) | exact h5 (by linarith)
  unfold Jmap
  exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hF)) (pow_ne_zero 6 (G_ne_zero u))

/-- **`FibreQMPeriod` from R1(b) (proved, modulo the two named glue Props).** -/
theorem fibreQMPeriod_of_r1b (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hC : HauptmodulCompare) (hB : UnifBaseChange) :
    FibreQMPeriod' := by
  intro Y Φ π h1 h2 u hu K A hF
  obtain ⟨emb, y, P, hP, hπ, hiso⟩ := hF
  have hb : R1bProps Y Φ := r1bProps_of_leaf hR1b h1
  -- an embedding `ε : ℚ̄ → ℂ`
  let ε : Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  -- the object at the complex point `y_ℂ = y ∘ Spec ε` is the base change of `P`
  obtain ⟨Pc, hPc, hbc⟩ := h1.2.2.2.1 Qbar ℂ ε y P hP
  -- the value of `π` at `y_ℂ`
  have hπc : π.val (K := ℂ) (fieldMap ε ≫ y).left =
      OnePoint.some (((Jmap u : ℚ) : ℂ)) := by
    have e1 : π.val (K := ℂ) (fieldMap ε ≫ y).left =
        (π.val (K := Qbar) y.left).map (ε : Qbar →+* ℂ) :=
      ToP1.val_comp π (ε : Qbar →+* ℂ) y.left
    rw [e1, hπ]
    change OnePoint.some (ε (algebraMap ℚ Qbar (Jmap u))) = _
    rw [ε.commutes, eq_ratCast]
  -- R1(b)(a) at `Pc`
  obtain ⟨τ, hτ, φ, hφ⟩ := hb.1 Pc
  -- the comparison
  obtain ⟨-, hj⟩ := hC Y Φ π h1 h2 hb hH (fieldMap ε ≫ y) Pc hPc τ hτ φ hφ
    _ (by exact_mod_cast jmap_ne_zero u hu) hπc
  -- the uniformization of `A(ℂ)_σ`
  obtain ⟨Φu, hΦu⟩ := hB K A emb P (ε : Qbar →+* ℂ) Pc hiso hbc τ hτ.ne' φ hφ.unif
  refine ⟨(ε : Qbar →+* ℂ).comp emb, QM.qmLattice hτ.ne', Φu, hΦu, τ, hτ, LinearEquiv.refl ℂ _,
    ?_, hj⟩
  convert Submodule.map_id (QM.qmLattice hτ.ne')
  exact LinearMap.ext fun v => rfl

end R1bState

/-! # r1b-state, part 4: consistency probes for the clauses of `R1bProps`

The clauses quantify over uniformizations with two compatibilities. If either were inconsistent
on the torus side, no object could satisfy it and the leaf would be **false** (not vacuous), so
both are checked here:
* `iotaC_mem`: for `a ∈ 𝒪` the matrix `ι(a)` maps `Λ_τ` into itself, so `ι(a)` acts on
  `ℂ²/Λ_τ` (the `ι`-compatibility of `IsQMUnif` is between two genuine actions), and the action is
  multiplicative (`iotaC_mul`), unital and additive;
* `level_linear`, `level_ker`: `a ↦ [ι(a)(τ, 1)ᵀ/3]` is `𝒪`-linear with kernel exactly `3𝒪`, the
  shape of `LeafQM.AV.Level3` (so the level clause of `IsQMUnifLevel` is consistent).
The domain clause of (b), (c) is nonempty (`I ∈ ℍ`), and `Λ_I` is a genuine full lattice
(bp-analytic's instances). -/

noncomputable section

namespace R1bState

open LeafQM BPAnalytic Matrix

theorem iota_mul (x y : LeafQM.B) : QM.iota (x * y) = QM.iota x * QM.iota y := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QM.iota, QM.Mi, QM.Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> push_cast <;>
    ring_nf <;> rw [h2] <;> ring

theorem iota_one : QM.iota (1 : LeafQM.B) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QM.iota]

theorem iota_add (x y : LeafQM.B) : QM.iota (x + y) = QM.iota x + QM.iota y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [QM.iota, QM.Mi, QM.Mj] <;> push_cast <;> ring

theorem iotaC_mul (x y : LeafQM.B) : iotaC (x * y) = iotaC x * iotaC y := by
  unfold iotaC
  rw [iota_mul]
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- The explicit formula `ι(x)(τ, 1)ᵀ = ((a+√2b)τ − 3c − 3√2d, (c−√2d)τ + a − √2b)`. -/
theorem latVec_apply (x : LeafQM.B) (τ : ℂ) :
    QM.latVec x τ = ![((x.re : ℝ) + √2 * (x.imI : ℝ) : ℝ) * τ - 3 * ((x.imJ : ℝ) : ℂ)
        - 3 * (√2 : ℂ) * ((x.imK : ℝ) : ℂ),
      (((x.imJ : ℝ) - √2 * (x.imK : ℝ) : ℝ) : ℂ) * τ + ((x.re : ℝ) : ℂ)
        - (√2 : ℂ) * ((x.imI : ℝ) : ℂ)] := by
  ext i
  fin_cases i <;>
    simp [QM.latVec, QM.iota, QM.Mi, QM.Mj, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    push_cast <;> ring

theorem latVec_mul (a x : LeafQM.B) (τ : ℂ) :
    QM.latVec (a * x) τ = iotaC a *ᵥ QM.latVec x τ := by
  rw [latVec_eq, latVec_eq, iotaC_mul, Matrix.mulVec_mulVec]

theorem latVec_add (x y : LeafQM.B) (τ : ℂ) :
    QM.latVec (x + y) τ = QM.latVec x τ + QM.latVec y τ := by
  rw [latVec_apply, latVec_apply, latVec_apply]
  ext i; fin_cases i <;> simp <;> push_cast <;> ring

theorem latVec_ofInt (n : Fin 4 → ℤ) (τ : ℂ) :
    QM.latVec (ofInt n) τ = ∑ k, n k • QM.qmVec τ k := by
  simp only [QM.qmVec, Fin.sum_univ_four, QM.latVec0, QM.latVec1, QM.latVec2, QM.latVec3]
  rw [latVec_apply]
  ext i; fin_cases i <;> simp [ofInt] <;> push_cast <;> ring

theorem latVec_mem_of_inO {x : LeafQM.B} (hx : InO x) {τ : ℂ} (hτ : τ.im ≠ 0) :
    QM.latVec x τ ∈ QM.qmLattice hτ := by
  obtain ⟨n, rfl⟩ := hx
  rw [latVec_ofInt, QM.qmLattice_eq]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem oBasis_inO (k : Fin 4) : InO (QM.oBasis k) := by
  refine ⟨Pi.single k 1, ?_⟩
  fin_cases k <;> ext <;> simp [ofInt, QM.oBasis]

/-- **The action of `𝒪` on the torus is well defined**: `ι(a)Λ_τ ⊆ Λ_τ` for `a ∈ 𝒪`. -/
theorem iotaC_mem (a : O) {τ : ℂ} (hτ : τ.im ≠ 0) {v : Fin 2 → ℂ}
    (hv : v ∈ QM.qmLattice hτ) : iotaC (a : LeafQM.B) *ᵥ v ∈ QM.qmLattice hτ := by
  rw [QM.qmLattice_eq] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    rw [QM.qmVec, ← latVec_mul]
    exact latVec_mem_of_inO (O.mul_mem a.2 (oBasis_inO k)) hτ
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hv hw
  | smul n v _ hv =>
    rw [show n • v = (n : ℂ) • v from (Int.cast_smul_eq_zsmul ℂ n v).symm, Matrix.mulVec_smul,
      Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ n hv

/-- **The level map is `𝒪`-linear** (`η(ab) = ι(a)η(b)`, `Level3.linear`'s shape). -/
theorem level_linear (a b : LeafQM.B) (τ : ℂ) :
    (1 / 3 : ℂ) • QM.latVec (a * b) τ = iotaC a *ᵥ ((1 / 3 : ℂ) • QM.latVec b τ) := by
  rw [latVec_mul, Matrix.mulVec_smul]

/-- `x ↦ ι(x)(τ, 1)ᵀ` is injective on `B` for `Im τ ≠ 0`. -/
theorem latVec_eq_zero {x : LeafQM.B} {τ : ℂ} (hτ : τ.im ≠ 0) (h : QM.latVec x τ = 0) :
    x = 0 := by
  have h1 := congrFun h 1
  rw [latVec_apply] at h1
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply] at h1
  have him := congrArg Complex.im h1
  have hre := congrArg Complex.re h1
  simp at him hre
  have irr : ∀ p q : ℚ, (p : ℝ) = √2 * q → p = 0 ∧ q = 0 := by
    intro p q hpq
    by_cases hq : q = 0
    · subst hq; simp at hpq; exact ⟨by exact_mod_cast hpq, rfl⟩
    · exfalso
      apply irrational_sqrt_two
      refine ⟨p / q, ?_⟩
      have : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      push_cast; field_simp; linarith
  have hcd : (x.imJ : ℝ) = √2 * x.imK := by
    have := him.resolve_right hτ
    linarith
  obtain ⟨hc, hd⟩ := irr _ _ hcd
  rw [hc, hd] at hre
  simp at hre
  have hab : (x.re : ℝ) = √2 * x.imI := by linarith
  obtain ⟨ha, hb⟩ := irr _ _ hab
  ext <;> simp [ha, hb, hc, hd]

theorem latVec_smul (q : ℚ) (x : LeafQM.B) (τ : ℂ) :
    QM.latVec (q • x) τ = (q : ℂ) • QM.latVec x τ := by
  rw [latVec_apply, latVec_apply]
  ext i; fin_cases i <;> simp <;> push_cast <;> ring

theorem mem_qmLattice_iff {τ : ℂ} (hτ : τ.im ≠ 0) {v : Fin 2 → ℂ} :
    v ∈ QM.qmLattice hτ → ∃ n : Fin 4 → ℤ, v = QM.latVec (ofInt n) τ := by
  rw [QM.qmLattice_eq]
  intro hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    exact ⟨Pi.single k 1, by
      rw [latVec_ofInt]; simp [Pi.single_apply]⟩
  | zero => exact ⟨0, by rw [latVec_ofInt]; simp⟩
  | add v w _ _ hv hw =>
    obtain ⟨n, rfl⟩ := hv
    obtain ⟨m, rfl⟩ := hw
    exact ⟨n + m, by rw [← latVec_add, ofInt_add]⟩
  | smul k v _ hv =>
    obtain ⟨n, rfl⟩ := hv
    exact ⟨k • n, by
      rw [latVec_ofInt, latVec_ofInt, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, mul_smul]⟩

/-- **The level map has kernel exactly `3𝒪`** (`Level3.ker`'s shape): for `a ∈ 𝒪`,
`ι(a)(τ, 1)ᵀ/3 ∈ Λ_τ` iff `a ∈ 3𝒪`. -/
theorem level_ker (a : O) {τ : ℂ} (hτ : τ.im ≠ 0) :
    (1 / 3 : ℂ) • QM.latVec (a : LeafQM.B) τ ∈ QM.qmLattice hτ ↔ ∃ b : O, a = 3 * b := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_qmLattice_iff hτ h
    have hb : (ofInt n : LeafQM.B) ∈ O := ⟨n, rfl⟩
    refine ⟨⟨ofInt n, hb⟩, ?_⟩
    apply Subtype.ext
    have h0 : QM.latVec ((a : LeafQM.B) + (-3 : ℚ) • ofInt n) τ = 0 := by
      rw [latVec_add, latVec_smul, ← hn, smul_smul]
      ext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; push_cast; ring
    have := latVec_eq_zero hτ h0
    change (a : LeafQM.B) = 3 * ofInt n
    have e : (3 : LeafQM.B) * ofInt n = (3 : ℚ) • ofInt n := by
      rw [Algebra.smul_def, map_ofNat]
    rw [e]
    have e2 : (a : LeafQM.B) = -((-3 : ℚ) • ofInt n) := eq_neg_of_add_eq_zero_left this
    rw [e2, ← neg_smul]; norm_num
  · rintro ⟨b, rfl⟩
    have e : ((3 * b : O) : LeafQM.B) = (3 : ℚ) • (b : LeafQM.B) := by
      rw [Algebra.smul_def, map_ofNat, Subring.coe_mul]
      congr 1
    rw [e, latVec_smul, smul_smul]
    norm_num
    exact latVec_mem_of_inO b.2 hτ

/-- The domain of clauses (b), (c) is nonempty and `Λ_I` is a full lattice in `ℂ²`. -/
example : (0 : ℝ) < (Complex.I).im := by simp

theorem im_I_ne_zero : (Complex.I).im ≠ 0 := by simp

example : IsZLattice ℝ (QM.qmLattice im_I_ne_zero) := inferInstance

end R1bState

/-! ## Axiom audit -/
#print axioms R1bState.r1bProps_of_leaf
#print axioms R1bState.R1bProps.of_hom
#print axioms R1bState.holomorphicP1On_of_family
#print axioms R1bState.q3_form_of_R1bProps
#print axioms R1bState.fibreQMPeriod_of_r1b
#print axioms R1bState.iotaC_mem
#print axioms R1bState.level_ker
#print axioms R1bState.level_linear
#print axioms R1bState.iota_mul
