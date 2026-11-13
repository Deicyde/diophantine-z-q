import ZInQKernel.HDecomp.Analytic.Uniformization
import ZInQKernel.HDecomp.Analytic.QMLattice
import ZInQKernel.HDecomp.QM.Pin
import ZInQKernel.HDecomp.LeafPush2.R22
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.LeafPush2.UnifBridge

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

/-! # r1b-state, part 5: `HauptmodulCompare` split into three named pieces

`hauptmodulCompare_of_parts` proves `HauptmodulCompare` from
* `FamilyHauptmodul` (the Möbius comparison on the family `τ ↦ y(τ)`; the **only** piece that uses
  R1(b)'s family clauses, through the holomorphy of `τ ↦ π(y(τ))` proved in part 2),
* `PiOfQMLattice` (`π` of a complex point depends only on the lattice of its QM pair: no family
  input),
* `JDenNonzero` (a statement about theta functions only: where `QMHauptmodul`'s `f` is finite,
  `jDen(Ω(τ)) ≠ 0`; the x/0 guard),
and R1(b) itself. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic

/-- The body of `PkgI1.QMHauptmodul`, for a given `f` (`qmHauptmodul_iff`). -/
def QMHauptmodulProps (f : UpperHalfPlane → OnePoint ℂ) : Prop :=
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

theorem qmHauptmodul_iff : PkgI1.QMHauptmodul ↔ ∃ f, QMHauptmodulProps f := Iff.rfl

/-- **GLUE (the Möbius comparison on the family).** For a candidate `(Y, Φ, π)` with R1(a)'s and
R2's clauses, a family `y` as in R1(b)(b) with `τ ↦ π(y(τ))` holomorphic into `P¹` (which
R1(b)(c) gives, `holomorphicP1On_of_family`), and `f` as in `QMHauptmodul`: `π(y(τ)) = f(τ)` on
`ℍ`. Why true: `F = π ∘ y` is `Γ*`-invariant with fibres the `Γ*`-orbits (R2's fibre clause and
the lattice computation `Λ_{γτ} ∝ ι(n)Λ_τ`, `γ = ι(n)`), so `F = g ∘ f` with `g` a bijection of
`P¹`; `g` is continuous and holomorphic off the images of the elliptic points (`f` is open and a
local biholomorphism off them), hence holomorphic (removable singularities), hence Möbius; the CM
clauses of R2 and of `QMHauptmodul` (at the fixed points of `ι(x)`, where the object of the family
has CM by `x`: scalar multiplication by the eigenvalue of `ι(x)` on `(τ, 1)ᵀ` preserves `Λ_τ` and
commutes with `ι(𝒪)`, and is algebraic by T11a) make `g` fix `0, ∞, −16/27`, so `g = id`.
SPECULATIVE until proved (complex analysis on `ℍ` and `P¹`; R2 transported from `ℚ̄`- to
`ℂ`-points). -/
def FamilyHauptmodul : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) →
      HolomorphicP1On (fun τ => π.val (K := ℂ) (y τ).left) UHP →
    ∀ f, QMHauptmodulProps f →
    ∀ (τ : ℂ) (hτ : 0 < τ.im), π.val (K := ℂ) (y τ).left = f ⟨τ, hτ⟩

/-- **GLUE (`π` sees only the QM lattice).** Two complex points whose objects have
`ι`-compatible uniformizations by the same `Λ_τ` (level structures arbitrary) have the same
`π`-value. Why true: `φ' ∘ φ⁻¹` is an `ι`-equivariant isomorphism of complex Lie groups
`P.A(ℂ) ≅ P'.A(ℂ)`, hence algebraic (T11a-type GAGA), so the QM pairs are isomorphic; `π`
factors through `Y₃ → X₆` (R2's fibre clause; on `ℂ`-points by transport from the dense
`ℚ̄`-points), which forgets the level structure. No family input. -/
def PiOfQMLattice : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ (y y' : fieldPt ℂ ⟶ Y) (P P' : QML3 ℂ), Φ ℂ y = M3.mk P → Φ ℂ y' = M3.mk P' →
    ∀ (τ : ℂ) (hτ : τ.im ≠ 0) (φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ))
      (φ' : Torus (QM.qmLattice hτ) ≃+ Additive (P'.A.Pt ℂ)),
      IsQMUnif P hτ φ → IsQMUnif P' hτ φ' → π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left

/-- **GLUE (the x/0 guard; theta functions only).** Where `QMHauptmodul`'s `f` is finite,
`jDen(Ω(τ)) ≠ 0`. Why true: `jDen ∘ Ω = (4ψ₄ ∘ Ω)⁵`; `ψ₄ ∘ Ω` is a nonzero modular form of weight
8 for `Γ*` (signature `(0; 2, 4, 6)`), whose zero divisor has orbifold degree
`4·(−2 + 1/2 + 3/4 + 5/6) = 1/3`, so it vanishes only at the order-6 elliptic orbit (the disc `−3`
points), where `f = ∞` (`QMHauptmodul`'s sixth clause). Numerically (`jden_check.py`):
`Σθ⁸(Ω(i√3)) ≈ 0` at the disc `−3` point, `|Σθ⁸| ≥ 7` at the disc `−4`, `−24` points and five
sample points. SPECULATIVE until proved. -/
def JDenNonzero : Prop :=
  ∀ f, QMHauptmodulProps f → ∀ τ : UpperHalfPlane, f τ ≠ OnePoint.infty →
    PkgI1.jDen (PkgI1.Omega τ) ≠ 0

/-- **`HauptmodulCompare` from the three pieces and R1(b) (proved).** -/
theorem hauptmodulCompare_of_parts (hA : FamilyHauptmodul) (hB : PiOfQMLattice)
    (hC : JDenNonzero) : HauptmodulCompare := by
  intro Y Φ π h1 h2 hb hH y P hP τ hτ φ hφ c hc hπ
  obtain ⟨f, hf⟩ := hH
  obtain ⟨-, yf, hyb, hyc⟩ := hb
  obtain ⟨P', φ', hP', hφ', -⟩ := hyb τ hτ
  have hhol := holomorphicP1On_of_family yf hyc π
  have e1 : π.val (K := ℂ) y.left = π.val (K := ℂ) (yf τ).left :=
    hB Y Φ π h1 h2 y (yf τ) P P' hP hP' τ hτ.ne' φ φ' hφ hφ'
  have e2 := hA Y Φ π h1 h2 yf hyb hhol f hf τ hτ
  have hfc : f ⟨τ, hτ⟩ = OnePoint.some c := by rw [← e2, ← e1, hπ]
  have hden : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 :=
    hC f hf ⟨τ, hτ⟩ (by rw [hfc]; exact OnePoint.coe_ne_infty c)
  refine ⟨hden, ?_⟩
  have e3 := hf.2.1 ⟨τ, hτ⟩ hden
  rw [hfc] at e3
  exact (OnePoint.coe_injective e3).symm

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul`, and four named glue Props (proved).** -/
theorem fibreQMPeriod_of_r1b_parts (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hA : FamilyHauptmodul) (hB : PiOfQMLattice) (hC : JDenNonzero)
    (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b hR1b hH (hauptmodulCompare_of_parts hA hB hC) hU

end R1bState

/-! # r1b-state, part 6: `FamilyHauptmodul` split into pure analysis and moduli inputs

`familyHauptmodul_of_parts` proves `FamilyHauptmodul` from
* `MobiusRigidity` (pure complex analysis, no moduli: two holomorphic maps `ℍ → P¹` whose fibres
  are the orbits of the same set `G ⊆ GL₂(ℝ)`, the first continuous and onto, which agree at three
  points with distinct values, are equal);
* `HauptmodulHolomorphic` (`QMHauptmodul`'s `f` is holomorphic into `P¹`: theta functions only);
* `FamilyOrbits` (the fibres of `τ ↦ π(y(τ))` on the family are the `Γ*`-orbits);
* `FamilyCMValues` (the family takes `π = 0, ∞, −16/27` at the fixed points of `ι(x)`, `x` of
  discriminant `−4, −3, −24`);
* `CMPointsExist` (`ι(x)` has such fixed points in `ℍ`; an elementary computation);
together with R1(b)(c) through the holomorphy of `τ ↦ π(y(τ))` (part 2). -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic
open scoped Topology

/-- A function on `ℍ` extended to `ℂ` (by `∞` off `ℍ`; only used on `ℍ`). -/
def extH (f : UpperHalfPlane → OnePoint ℂ) : ℂ → OnePoint ℂ :=
  fun τ => if h : 0 < τ.im then f ⟨τ, h⟩ else OnePoint.infty

theorem isOpen_UHP : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im

theorem HolomorphicP1On.congr {F F' : ℂ → OnePoint ℂ} {D : Set ℂ} (hF : HolomorphicP1On F D)
    (hD : IsOpen D) (he : ∀ τ ∈ D, F τ = F' τ) : HolomorphicP1On F' D := by
  intro τ₀ hτ₀
  obtain ⟨N, hN, h, hh, hor⟩ := hF τ₀ hτ₀
  refine ⟨N ∩ D, Filter.inter_mem hN (hD.mem_nhds hτ₀), h, hh.mono Set.inter_subset_left, ?_⟩
  rcases hor with hl | hr
  · exact Or.inl fun τ hτ => (he τ hτ.2).symm.trans (hl τ hτ.1)
  · exact Or.inr fun τ hτ => (he τ hτ.2).symm.trans (hr τ hτ.1)

/-- **GLUE (pure complex analysis; no moduli).** Let `G ⊆ GL₂(ℝ)` and `f, F : ℍ → P¹`, both
holomorphic, with fibres exactly the `G`-orbits, `f` continuous and onto. If `F` and `f` agree at
three points where `f` takes three distinct values, then `F = f`. Why true: `f` is open
(nonconstant holomorphic), so `F = g ∘ f` for a continuous bijection `g` of `P¹`; `g` is
holomorphic off the image of the critical points of `f`, a closed discrete (`G`-saturated
preimage) hence finite subset of `P¹`, so holomorphic (removable singularities); a holomorphic
bijection of `P¹` is a Möbius map, and one fixing three points is the identity. (If `G` contains
orientation-reversing elements the hypotheses are contradictory.) Mathlib has removable
singularities; it lacks the degree theory of holomorphic maps `P¹ → P¹`. -/
def MobiusRigidity : Prop :=
  ∀ (G : Set (GL (Fin 2) ℝ)) (f F : UpperHalfPlane → OnePoint ℂ),
    Continuous f → Function.Surjective f →
    (∀ τ τ' : UpperHalfPlane, f τ = f τ' ↔ ∃ g ∈ G, g • τ = τ') →
    (∀ τ τ' : UpperHalfPlane, F τ = F τ' ↔ ∃ g ∈ G, g • τ = τ') →
    HolomorphicP1On (extH f) UHP → HolomorphicP1On (extH F) UHP →
    ∀ τ₁ τ₂ τ₃ : UpperHalfPlane, f τ₁ ≠ f τ₂ → f τ₁ ≠ f τ₃ → f τ₂ ≠ f τ₃ →
      F τ₁ = f τ₁ → F τ₂ = f τ₂ → F τ₃ = f τ₃ → F = f

/-- **GLUE (theta functions only).** `QMHauptmodul`'s `f` is holomorphic into `P¹`. Why true:
`f = jNum/jDen ∘ Ω` off the zeros of `jDen ∘ Ω`, a quotient of holomorphic functions of `τ`
(theta constants are holomorphic on `𝔥₂`, `Ω` is holomorphic on `ℍ` by bp-analytic's partial
fractions), and `f` is continuous, so `f` is the meromorphic quotient. -/
def HauptmodulHolomorphic : Prop :=
  ∀ f, QMHauptmodulProps f → HolomorphicP1On (extH f) UHP

/-- **GLUE (the family's `π`-fibres are the `Γ*`-orbits).** Why true: for `γ = ι(n)`,
`n ∈ N_B(𝒪)` of positive norm, `Λ_{γτ}` is a scalar multiple of `ι(n)Λ_τ`, so the QM pairs at
`τ` and `γτ` are twist-isomorphic (by `Ad n`), and conversely an `ι`-twisted isomorphism of the
QM pairs at `τ`, `τ'` is a linear map carrying `Λ_τ` to `Λ_{τ'}` and normalizing `ι(𝒪)`, i.e.
`ι(n)` up to a scalar (Skolem–Noether, T13); with GAGA (T11a) and R2's fibre clause on
`ℂ`-points. -/
def FamilyOrbits : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) →
    ∀ τ τ' : UpperHalfPlane, π.val (K := ℂ) (y τ).left = π.val (K := ℂ) (y τ').left ↔
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ'

/-- **GLUE (the family's CM values).** At a fixed point `τ` of `ι(x)`, `x ∈ 𝒪` with `x² = −1`
(resp. `x² − x + 1 = 0`, `x² = −6`), `π(y(τ)) = 0` (resp. `∞`, `−16/27`). Why true: if
`ι(x)(τ, 1)ᵀ = λ(τ, 1)ᵀ`, multiplication by `λ` preserves `Λ_τ` and commutes with `ι(𝒪)`, so it is
an endomorphism of the QM pair at `τ` (algebraic by T11a) in `End_𝒪` with `λ² = −1` (resp. …),
and R2's CM clauses (on `ℂ`-points) give the value. -/
def FamilyCMValues : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) →
    ∀ (x : PkgI1.B) (g : GL (Fin 2) ℝ) (τ : UpperHalfPlane), PkgI1.InO x →
      (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det →
      g • τ = τ →
      (x * x = -1 → π.val (K := ℂ) (y τ).left = ((0 : ℂ) : OnePoint ℂ)) ∧
      (x * x - x + 1 = 0 → π.val (K := ℂ) (y τ).left = OnePoint.infty) ∧
      (x * x = -6 → π.val (K := ℂ) (y τ).left = ((-16 / 27 : ℂ) : OnePoint ℂ))

/-- **Elementary (proved below, `cmPointsExist`): CM points exist in `ℍ`.** E.g. `ι(i + j)` fixes `√2 + i`,
`ι((1+j)/2)` fixes `i√3`, `ι(2j + ij)` fixes `i√(9+6√2)` (pkg-I1's numerics, `jden_check.py`). -/
def CMPointsExist : Prop :=
  (∃ (x : PkgI1.B) (g : GL (Fin 2) ℝ) (τ : UpperHalfPlane), PkgI1.InO x ∧ x * x = -1 ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧
    g • τ = τ) ∧
  (∃ (x : PkgI1.B) (g : GL (Fin 2) ℝ) (τ : UpperHalfPlane), PkgI1.InO x ∧ x * x - x + 1 = 0 ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧
    g • τ = τ) ∧
  (∃ (x : PkgI1.B) (g : GL (Fin 2) ℝ) (τ : UpperHalfPlane), PkgI1.InO x ∧ x * x = -6 ∧
    (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x ∧ 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det ∧
    g • τ = τ)

theorem extH_eq (f : UpperHalfPlane → OnePoint ℂ) (τ : UpperHalfPlane) :
    extH f (τ : ℂ) = f τ := by
  unfold extH
  rw [dif_pos (show 0 < (τ : ℂ).im from τ.im_pos)]

/-- **`FamilyHauptmodul` from the five pieces (proved).** -/
theorem familyHauptmodul_of_parts (hM : MobiusRigidity) (hH : HauptmodulHolomorphic)
    (hO : FamilyOrbits) (hV : FamilyCMValues) (hE : CMPointsExist) : FamilyHauptmodul := by
  intro Y Φ π h1 h2 y hb hhol f hf τ hτ
  set F : UpperHalfPlane → OnePoint ℂ := fun t => π.val (K := ℂ) (y t).left with hFdef
  have hFhol : HolomorphicP1On (extH F) UHP := by
    refine hhol.congr isOpen_UHP fun t ht => ?_
    show _ = extH F t
    unfold extH
    rw [dif_pos (show 0 < t.im from ht)]
  obtain ⟨⟨x₁, g₁, t₁, i₁, e₁, m₁, p₁, f₁⟩, ⟨x₂, g₂, t₂, i₂, e₂, m₂, p₂, f₂⟩,
    ⟨x₃, g₃, t₃, i₃, e₃, m₃, p₃, f₃⟩⟩ := hE
  have v₁ : f t₁ = ((0 : ℂ) : OnePoint ℂ) := hf.2.2.2.2.1 x₁ i₁ e₁ g₁ m₁ t₁ f₁
  have v₂ : f t₂ = OnePoint.infty := hf.2.2.2.2.2.1 x₂ i₂ e₂ g₂ m₂ t₂ f₂
  have v₃ : f t₃ = ((-16 / 27 : ℂ) : OnePoint ℂ) := hf.2.2.2.2.2.2 x₃ i₃ e₃ g₃ m₃ t₃ f₃
  have w₁ : F t₁ = f t₁ := by rw [v₁]; exact (hV Y Φ π h1 h2 y hb x₁ g₁ t₁ i₁ m₁ p₁ f₁).1 e₁
  have w₂ : F t₂ = f t₂ := by rw [v₂]; exact (hV Y Φ π h1 h2 y hb x₂ g₂ t₂ i₂ m₂ p₂ f₂).2.1 e₂
  have w₃ : F t₃ = f t₃ := by rw [v₃]; exact (hV Y Φ π h1 h2 y hb x₃ g₃ t₃ i₃ m₃ p₃ f₃).2.2 e₃
  have d₁₂ : f t₁ ≠ f t₂ := by rw [v₁, v₂]; exact OnePoint.coe_ne_infty 0
  have d₂₃ : f t₂ ≠ f t₃ := by rw [v₂, v₃]; exact (OnePoint.coe_ne_infty _).symm
  have d₁₃ : f t₁ ≠ f t₃ := by
    rw [v₁, v₃]; intro h; have := OnePoint.coe_injective h; norm_num at this
  have hEq := hM PkgI1.GammaStar f F hf.1 hf.2.2.2.1 hf.2.2.1 (hO Y Φ π h1 h2 y hb) (hH f hf)
    hFhol t₁ t₂ t₃ d₁₂ d₁₃ d₂₃ w₁ w₂ w₃
  exact congrFun hEq ⟨τ, hτ⟩

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul` and the finest named glue (proved).** -/
theorem fibreQMPeriod_of_r1b_fine (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hM : MobiusRigidity) (hHol : HauptmodulHolomorphic)
    (hO : FamilyOrbits) (hV : FamilyCMValues) (hE : CMPointsExist) (hB : PiOfQMLattice)
    (hC : JDenNonzero) (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b_parts hR1b hH (familyHauptmodul_of_parts hM hHol hO hV hE) hB hC hU

end R1bState

/-! # r1b-state, part 7: `CMPointsExist` (proved)

`ι(i + j)` fixes `√2 + i` (disc `−4`), `ι((1+j)/2)` fixes `i√3` (disc `−3`), and `ι(2j + ij)`
fixes `i√(9+6√2)` (disc `−24`). The memberships and quadratic relations are pkg-I1's `cm4`,
`cm3`, `cm24` (copied from `scratch/h-decomposition/Leaves.lean` lines 411-431). -/

noncomputable section

namespace R1bState

open PkgI1 (B InO oBasis mu iota Mi Mj)

theorem inO_of (x : B) (n : Fin 4 → ℤ) (h : x = ∑ k, (n k : ℚ) • oBasis k) : InO x := ⟨n, h⟩

/-- (copied) `i + j ∈ 𝒪`, `(i+j)² = -1` (disc `-4`). -/
theorem cm4 : InO ⟨0, 1, 1, 0⟩ ∧ (⟨0, 1, 1, 0⟩ : B) * ⟨0, 1, 1, 0⟩ = -1 := by
  refine ⟨inO_of _ ![-1, 1, 2, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp <;> norm_num

/-- (copied) `ω = (1+j)/2 ∈ 𝒪`, `ω² - ω + 1 = 0` (disc `-3`). -/
theorem cm3 : InO ⟨1/2, 0, 1/2, 0⟩ ∧
    (⟨1/2, 0, 1/2, 0⟩ : B) * ⟨1/2, 0, 1/2, 0⟩ - ⟨1/2, 0, 1/2, 0⟩ + 1 = 0 := by
  refine ⟨inO_of _ ![0, 0, 1, 0] ?_, ?_⟩
  · ext <;> simp [oBasis, Fin.sum_univ_four]
  · ext <;> simp <;> norm_num

/-- (copied) `μ = 2j + ij ∈ 𝒪`, `μ² = -6` (disc `-24`). -/
theorem cm24 : InO mu ∧ mu * mu = -6 := by
  refine ⟨inO_of _ ![-2, -1, 4, 2] ?_, ?_⟩
  · ext <;> simp [mu, oBasis, Fin.sum_univ_four] <;> norm_num
  · ext <;> simp [mu, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
      QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

/-- The entries of `ι(x)`. -/
theorem iota_eq (x : B) : iota x = !![(x.re : ℝ) + √2 * x.imI, -3 * (x.imJ : ℝ) - 3 * √2 * x.imK;
    (x.imJ : ℝ) - √2 * x.imK, (x.re : ℝ) - √2 * x.imI] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [iota, Mi, Mj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A fixed point of `g ∈ GL₂(ℝ)` with `det g > 0`: `g 1 0 · τ² + (g 1 1 − g 0 0)τ − g 0 1 = 0`. -/
theorem smul_eq_self_of {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (τ : UpperHalfPlane)
    (h : (g 0 0 : ℂ) * τ + g 0 1 = τ * ((g 1 0 : ℂ) * τ + g 1 1)) : g • τ = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos hg, div_eq_iff (UpperHalfPlane.denom_ne_zero g τ)]
  exact h

theorem sqrt2_sq : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem cmPointsExist : CMPointsExist := by
  refine ⟨?_, ?_, ?_⟩
  · -- disc −4: `x = i + j`, `ι(x) = [[√2, −3], [1, −√2]]`, `τ = √2 + i`
    have hdet : (iota ⟨0, 1, 1, 0⟩).det = 1 := by
      rw [iota_eq, Matrix.det_fin_two_of]; push_cast; ring_nf; rw [sqrt2_sq]; ring
    let g : GL (Fin 2) ℝ := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hgdet : 0 < g.det.val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]; change 0 < (iota _).det; rw [hdet]; norm_num
    refine ⟨⟨0, 1, 1, 0⟩, g, ⟨√2 + Complex.I, by simp⟩, cm4.1, cm4.2, rfl,
      by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hgdet, smul_eq_self_of hgdet _ ?_⟩
    change ((iota _ 0 0 : ℝ) : ℂ) * (√2 + Complex.I) + ((iota _ 0 1 : ℝ) : ℂ) =
      (√2 + Complex.I) * (((iota _ 1 0 : ℝ) : ℂ) * (√2 + Complex.I) + ((iota _ 1 1 : ℝ) : ℂ))
    rw [iota_eq]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    push_cast
    apply Complex.ext <;> simp <;> norm_num
  · -- disc −3: `x = (1+j)/2`, `ι(x) = [[1/2, −3/2], [1/2, 1/2]]`, `τ = i√3`
    have hdet : (iota ⟨1/2, 0, 1/2, 0⟩).det = 1 := by
      rw [iota_eq, Matrix.det_fin_two_of]; push_cast; ring
    let g : GL (Fin 2) ℝ := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hgdet : 0 < g.det.val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]; change 0 < (iota _).det; rw [hdet]; norm_num
    refine ⟨⟨1/2, 0, 1/2, 0⟩, g, ⟨√3 * Complex.I, by simp⟩, cm3.1, cm3.2, rfl,
      by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hgdet, smul_eq_self_of hgdet _ ?_⟩
    change ((iota _ 0 0 : ℝ) : ℂ) * (√3 * Complex.I) + ((iota _ 0 1 : ℝ) : ℂ) =
      (√3 * Complex.I) * (((iota _ 1 0 : ℝ) : ℂ) * (√3 * Complex.I) + ((iota _ 1 1 : ℝ) : ℂ))
    rw [iota_eq]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    have h3 : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    push_cast
    apply Complex.ext <;> simp <;> first | linear_combination (-1/2 : ℝ) * h3 | ring
  · -- disc −24: `x = μ = 2j + ij`, `ι(μ) = [[0, −6−3√2], [2−√2, 0]]`, `τ = i√(9+6√2)`
    have hdet : (iota mu).det = 6 := by
      rw [iota_eq, Matrix.det_fin_two_of]; simp [mu]; ring_nf; rw [sqrt2_sq]; ring
    let g : GL (Fin 2) ℝ := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_iff_ne_zero.mpr (by norm_num))
    have hgdet : 0 < g.det.val := by
      rw [Matrix.GeneralLinearGroup.val_det_apply]; change 0 < (iota _).det; rw [hdet]; norm_num
    have hpos : (0 : ℝ) < 9 + 6 * √2 := by positivity
    refine ⟨mu, g, ⟨√(9 + 6 * √2) * Complex.I, by simp [hpos]⟩, cm24.1, cm24.2, rfl,
      by rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hgdet, smul_eq_self_of hgdet _ ?_⟩
    change ((iota _ 0 0 : ℝ) : ℂ) * (√(9 + 6 * √2) * Complex.I) + ((iota _ 0 1 : ℝ) : ℂ) =
      (√(9 + 6 * √2) * Complex.I) * (((iota _ 1 0 : ℝ) : ℂ) * (√(9 + 6 * √2) * Complex.I) +
        ((iota _ 1 1 : ℝ) : ℂ))
    rw [iota_eq]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    have hs : (√(9 + 6 * √2) : ℝ) ^ 2 = 9 + 6 * √2 := Real.sq_sqrt hpos.le
    simp [mu]
    apply Complex.ext <;> simp <;> linear_combination (2 - √2) * hs + (-6) * sqrt2_sq

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul` and seven named glue Props (proved).** -/
theorem fibreQMPeriod_of_r1b_final (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hM : MobiusRigidity) (hHol : HauptmodulHolomorphic)
    (hO : FamilyOrbits) (hV : FamilyCMValues) (hB : PiOfQMLattice) (hC : JDenNonzero)
    (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b_fine hR1b hH hM hHol hO hV cmPointsExist hB hC hU

end R1bState

/-! # r1b-state, part 8: `FamilyCMValues` from the leaf T11a and R2's CM clauses on `ℂ`-points

At a fixed point `τ` of `ι(x)` (`x ∈ 𝒪`, `det ι(x) > 0`), `(τ, 1)ᵀ` is an eigenvector of `ι(x)`
with eigenvalue `λ = (ι(x)(τ, 1)ᵀ)₂`; multiplication by `λ` preserves `Λ_τ` (`lam_mem`) and
commutes with `ι(𝒪)`, so by T11a (leaf-push2's `T11a_RiemannEnd`, Riemann/GAGA for
endomorphisms) it is an endomorphism `f` of the object of the family at `τ`, in `End_𝒪`, with
`f² = −1` (resp. `f² − f + 1 = 0`, `f² = −6`) because `λ` satisfies the relation of `x`
(uniqueness in T11a). R2's CM clauses on `ℂ`-points (`R2CMOnC`, glue) then give the value. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic Matrix
open ZInQ.LeafPush2 (T11a_RiemannEnd isUniformization_of_bp)

/-- **GLUE (R2's CM clauses on `ℂ`-points).** Why true: a complex point whose object has CM is
algebraic (CM abelian surfaces, and so their moduli points, are defined over `ℚ̄`), so it is a
`ℚ̄`-point composed with an embedding `ℚ̄ → ℂ` (naturality clause of `R1fpProps`, `ToP1.val_comp`),
and `End` does not grow from `ℚ̄` to `ℂ` (rigidity, leaf T11b); then R2's CM clauses apply. -/
def R2CMOnC : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ (y : fieldPt ℂ ⟶ Y) (P : QML3 ℂ), Φ ℂ y = M3.mk P →
      (HasCM4 P.q → π.val (K := ℂ) y.left = ((0 : ℂ) : OnePoint ℂ)) ∧
      (HasCM3 P.q → π.val (K := ℂ) y.left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := ℂ) y.left = ((-16 / 27 : ℂ) : OnePoint ℂ))

section Induces

variable {P : QML3 ℂ} {τ : ℂ} {hτ : τ.im ≠ 0}
  {φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)}

/-- The map `ℂ² → P.A(ℂ)`, `z ↦ φ[z]`. -/
def unifMap (φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)) (z : Fin 2 → ℂ) : P.A.Pt ℂ :=
  Additive.toMul (φ (proj (QM.qmLattice hτ) z))

/-- `f` is induced by the linear map `M`: `φ[Mz] = f(φ[z])`. -/
def Induces (φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)) (f : AbVar.End P.A)
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) : Prop :=
  ∀ z, unifMap φ (M z) = unifMap φ z ≫ f.hom

theorem unifMap_add (z w : Fin 2 → ℂ) : unifMap φ (z + w) = unifMap φ z * unifMap φ w := by
  unfold unifMap
  rw [← toMul_add, ← map_add]
  rfl

theorem unifMap_zero : unifMap φ 0 = 1 := by
  unfold unifMap
  change Additive.toMul (φ 0) = 1
  rw [map_zero]
  rfl

theorem Induces.mul {f g : AbVar.End P.A} {M N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)}
    (hf : Induces φ f M) (hg : Induces φ g N) : Induces φ (f * g) (M ∘ₗ N) := by
  intro z
  rw [LinearMap.comp_apply, hf, hg, Category.assoc]
  rfl

theorem Induces.add {f g : AbVar.End P.A} {M N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)}
    (hf : Induces φ f M) (hg : Induces φ g N) : Induces φ (f + g) (M + N) := by
  intro z
  rw [LinearMap.add_apply, unifMap_add, hf, hg, AbVar.Hom.hom_add, MonObj.comp_mul]

theorem induces_one : Induces φ (1 : AbVar.End P.A) LinearMap.id := by
  intro z
  change unifMap φ z = unifMap φ z ≫ 𝟙 _
  rw [Category.comp_id]

theorem induces_zero : Induces φ (0 : AbVar.End P.A) 0 := by
  intro z
  rw [LinearMap.zero_apply, unifMap_zero, AbVar.Hom.hom_zero, MonObj.comp_one]

/-- **Uniqueness (from T11a).** Two endomorphisms induced by one `Λ_τ`-preserving map agree. -/
theorem Induces.unique (hT : T11a_RiemannEnd) (hφ : Uniformization.IsUniformization P.A
      (QM.qmLattice hτ) φ) {f g : AbVar.End P.A} {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)}
    (hM : ∀ z ∈ QM.qmLattice hτ, M z ∈ QM.qmLattice hτ) (hf : Induces φ f M)
    (hg : Induces φ g M) : f = g := by
  have hdim : P.A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [P.surface]; norm_cast
  exact ((hT P.A 2 (QM.qmLattice hτ) (unifMap φ) hdim (isUniformization_of_bp P.A hφ)).1 M
    hM).unique hf hg

/-- **Existence (from T11a).** -/
theorem Induces.exists (hT : T11a_RiemannEnd) (hφ : Uniformization.IsUniformization P.A
      (QM.qmLattice hτ) φ) {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)}
    (hM : ∀ z ∈ QM.qmLattice hτ, M z ∈ QM.qmLattice hτ) : ∃ f, Induces φ f M := by
  have hdim : P.A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [P.surface]; norm_cast
  exact ((hT P.A 2 (QM.qmLattice hτ) (unifMap φ) hdim (isUniformization_of_bp P.A hφ)).1 M
    hM).exists

/-- `ι_P(a)` is induced by the matrix `ι(a)` (the `ι`-compatibility of `IsQMUnif`). -/
theorem induces_iota (hφ : IsQMUnif P hτ φ) (a : O) :
    Induces φ (P.q.iota a) (Matrix.toLin' (iotaC (a : LeafQM.B))) := by
  intro z
  have h := hφ.iota_compat a z
  unfold unifMap
  rw [Matrix.toLin'_apply, h]
  rfl

end Induces

theorem coe_im_ne_zero (τ : UpperHalfPlane) : (τ : ℂ).im ≠ 0 := τ.im_ne_zero

/-- `PkgI1`'s membership in `𝒪` is `LeafQM`'s. -/
theorem inO_of_pkgI1 {x : PkgI1.B} (hx : PkgI1.InO x) : LeafQM.InO x := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n, ?_⟩
  ext <;> simp [ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

theorem pkgI1_iota_eq (x : PkgI1.B) : PkgI1.iota x = QM.iota x := rfl

/-- The second coordinate of `ι(x)(τ, 1)ᵀ`: the eigenvalue at a fixed point. -/
def eigenval (x : LeafQM.B) (τ : ℂ) : ℂ := QM.latVec x τ 1

/-- **At a fixed point, `(τ, 1)ᵀ` is an eigenvector of `ι(x)`.** -/
theorem latVec_fixed {x : PkgI1.B} {g : GL (Fin 2) ℝ} {τ : UpperHalfPlane}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hfix : g • τ = τ) : QM.latVec x τ = eigenval x τ • ![(τ : ℂ), 1] := by
  have hg : 0 < g.det.val := by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
  have h := congrArg UpperHalfPlane.coe hfix
  rw [UpperHalfPlane.coe_smul_of_det_pos hg, div_eq_iff (UpperHalfPlane.denom_ne_zero g τ)] at h
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, hm, pkgI1_iota_eq] at h
  ext i
  fin_cases i
  · simp only [eigenval, QM.latVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul, Fin.isValue]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at h ⊢
    linear_combination h
  · simp [eigenval]

theorem eigenval_mul {x : PkgI1.B} {g : GL (Fin 2) ℝ} {τ : UpperHalfPlane}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hfix : g • τ = τ) (b : LeafQM.B) :
    QM.latVec (b * x) τ = eigenval x τ • QM.latVec b τ := by
  rw [latVec_mul, latVec_fixed hm hdet hfix, Matrix.mulVec_smul, latVec_eq]

/-- `λ²` is the eigenvalue of `x²`. -/
theorem eigenval_sq {x : PkgI1.B} {g : GL (Fin 2) ℝ} {τ : UpperHalfPlane}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hfix : g • τ = τ) : QM.latVec (x * x) τ = (eigenval x τ * eigenval x τ) • ![(τ : ℂ), 1] := by
  rw [eigenval_mul hm hdet hfix, latVec_fixed hm hdet hfix, smul_smul]

/-- **Multiplication by `λ` preserves `Λ_τ`.** -/
theorem lam_mem {x : PkgI1.B} (hx : PkgI1.InO x) {g : GL (Fin 2) ℝ} {τ : UpperHalfPlane}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hfix : g • τ = τ) {v : Fin 2 → ℂ} (hv : v ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ)) :
    eigenval x τ • v ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) := by
  have hxO : x ∈ O := inO_of_pkgI1 hx
  rw [QM.qmLattice_eq] at hv ⊢
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    rw [QM.qmVec, ← eigenval_mul hm hdet hfix, ← QM.qmLattice_eq (coe_im_ne_zero τ)]
    exact latVec_mem_of_inO (O.mul_mem (oBasis_inO k) hxO) _
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [smul_add]; exact Submodule.add_mem _ hv hw
  | smul n v _ hv => rw [smul_comm]; exact Submodule.smul_mem _ n hv

/-- **The CM endomorphism of the family object at a fixed point (from T11a).** -/
theorem exists_cm_end (hT : T11a_RiemannEnd) {x : PkgI1.B} (hx : PkgI1.InO x)
    {g : GL (Fin 2) ℝ} {τ : UpperHalfPlane}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (hfix : g • τ = τ) (P : QML3 ℂ)
    (φ : Torus (QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ)) ≃+ Additive (P.A.Pt ℂ))
    (hφ : IsQMUnif P (coe_im_ne_zero τ) φ) :
    ∃ f : AbVar.End P.A, f ∈ com P.q ∧ Induces φ f (eigenval x τ • LinearMap.id) := by
  set lam := eigenval x τ
  have hM : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
      (lam • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈
        QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) :=
    fun z hz => lam_mem hx hm hdet hfix hz
  obtain ⟨f, hf⟩ := Induces.exists hT hφ.unif hM
  refine ⟨f, ?_, hf⟩
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  have hMa : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
      ((lam • LinearMap.id) ∘ₗ Matrix.toLin' (iotaC (a : LeafQM.B))) z ∈
        QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) := by
    intro z hz
    exact hM _ (by rw [Matrix.toLin'_apply]; exact iotaC_mem a _ hz)
  have e1 : Induces φ (f * P.q.iota a) ((lam • LinearMap.id) ∘ₗ
      Matrix.toLin' (iotaC (a : LeafQM.B))) := hf.mul (induces_iota hφ a)
  have e2 : Induces φ (P.q.iota a * f) ((lam • LinearMap.id) ∘ₗ
      Matrix.toLin' (iotaC (a : LeafQM.B))) := by
    have : (lam • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) ∘ₗ
        Matrix.toLin' (iotaC (a : LeafQM.B)) =
        Matrix.toLin' (iotaC (a : LeafQM.B)) ∘ₗ (lam • LinearMap.id) := by
      ext z i; simp [Matrix.mulVec_smul]
    rw [this]
    exact (induces_iota hφ a).mul hf
  exact Induces.unique hT hφ.unif hMa e2 e1

/-- `x ↦ λ` respects the quadratic relations (second coordinates of `latVec`). -/
theorem latVec_one_snd (τ : ℂ) : QM.latVec (1 : LeafQM.B) τ 1 = 1 := by
  rw [latVec_apply]; simp

theorem latVec_zero_snd (τ : ℂ) : QM.latVec (0 : LeafQM.B) τ 1 = 0 := by
  rw [latVec_apply]; simp

theorem latVec_snd_add (a b : LeafQM.B) (τ : ℂ) :
    QM.latVec (a + b) τ 1 = QM.latVec a τ 1 + QM.latVec b τ 1 := by
  rw [latVec_add]; rfl

theorem latVec_snd_neg (a : LeafQM.B) (τ : ℂ) : QM.latVec (-a) τ 1 = -QM.latVec a τ 1 := by
  have h := latVec_smul (-1) a τ
  rw [show ((-1 : ℚ) • a) = -a by simp] at h
  rw [h]; simp

/-- **`FamilyCMValues` from T11a and `R2CMOnC` (proved).** -/
theorem familyCMValues_of_T11a (hT : T11a_RiemannEnd) (hR : R2CMOnC) : FamilyCMValues := by
  intro Y Φ π h1 h2 y hb x g τ hx hm hdet hfix
  obtain ⟨P, φ, hP, hφ, -⟩ := hb τ τ.im_pos
  obtain ⟨f, hfc, hf⟩ := exists_cm_end hT hx hm hdet hfix P φ hφ
  have hR' := hR Y Φ π h1 h2 (y τ) P hP
  set lam := eigenval x τ with hlam
  have hsq : QM.latVec (x * x) τ 1 = lam * lam := by
    rw [eigenval_sq hm hdet hfix, ← hlam]; simp
  have hlin : ∀ c : ℂ, ((c • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) ∘ₗ
      (c • LinearMap.id)) = (c * c) • LinearMap.id := by
    intro c; ext z i; simp [mul_smul]
  have hff : Induces φ (f * f) ((lam * lam) • LinearMap.id) := by
    rw [← hlin]; exact hf.mul hf
  have h0 : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
      (0 : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) :=
    fun z _ => by rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
  refine ⟨fun hx2 => hR'.1 ⟨f, hfc, ?_⟩, fun hx3 => hR'.2.1 ⟨f, hfc, ?_⟩,
    fun hx6 => hR'.2.2 ⟨f, hfc, ?_⟩⟩
  · -- `λ² = −1`, so `f² + 1` is induced by `0`
    have hl : lam * lam = -1 := by
      rw [← hsq, hx2, latVec_snd_neg, latVec_one_snd]
    have e : Induces φ (f * f + 1) 0 := by
      have := hff.add (induces_one (φ := φ))
      rwa [hl, show ((-1 : ℂ) • LinearMap.id + LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 0 by
        ext z i; simp] at this
    have := Induces.unique hT hφ.unif h0 e induces_zero
    exact eq_neg_of_add_eq_zero_left this
  · -- `λ² − λ + 1 = 0`, so `f² + 1` and `f` are induced by `λ`
    have hl : lam * lam + 1 = lam := by
      have h : QM.latVec (x * x - x + 1) (τ : ℂ) 1 = QM.latVec 0 (τ : ℂ) 1 := by rw [hx3]
      rw [show x * x - x + 1 = x * x + (-x) + 1 by abel, latVec_snd_add, latVec_snd_add,
        latVec_snd_neg, latVec_one_snd, latVec_zero_snd, hsq] at h
      change lam * lam + -lam + 1 = 0 at h
      linear_combination h
    have e : Induces φ (f * f + 1) (lam • LinearMap.id) := by
      have := hff.add (induces_one (φ := φ))
      rwa [show ((lam * lam) • LinearMap.id + LinearMap.id :
        (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = (lam * lam + 1) • LinearMap.id by
          rw [add_smul, one_smul], hl] at this
    have hMl : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
        (lam • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈
          QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) :=
      fun z hz => lam_mem hx hm hdet hfix hz
    have := Induces.unique hT hφ.unif hMl e hf
    rw [show f * f - f + 1 = (f * f + 1) - f by abel, this, sub_self]
  · -- `λ² = −6`, so `f² + 6` is induced by `0`
    have hl : lam * lam = -6 := by
      rw [← hsq, hx6]
      rw [latVec_apply]
      simp [QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat,
        QuaternionAlgebra.imK_ofNat]
    have h6 : Induces φ (1 + 1 + 1 + 1 + 1 + 1 : AbVar.End P.A) ((6 : ℂ) • LinearMap.id) := by
      have h1 := induces_one (φ := φ)
      have := ((((h1.add h1).add h1).add h1).add h1).add h1
      convert this using 1
      ext z i; simp; ring
    have e : Induces φ (f * f + (1 + 1 + 1 + 1 + 1 + 1)) 0 := by
      have := hff.add h6
      rwa [hl, ← add_smul, show (-6 : ℂ) + 6 = 0 by norm_num, zero_smul] at this
    have := Induces.unique hT hφ.unif h0 e induces_zero
    rw [show (1 + 1 + 1 + 1 + 1 + 1 : AbVar.End P.A) = 6 by norm_num] at this
    exact eq_neg_of_add_eq_zero_left this

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul`, the leaf T11a and seven glue Props
(proved).** -/
theorem fibreQMPeriod_of_r1b_T11a (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hT : T11a_RiemannEnd) (hM : MobiusRigidity)
    (hHol : HauptmodulHolomorphic) (hO : FamilyOrbits) (hR : R2CMOnC) (hB : PiOfQMLattice)
    (hC : JDenNonzero) (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b_final hR1b hH hM hHol hO (familyCMValues_of_T11a hT hR) hB hC hU

end R1bState

/-! # r1b-state, part 8b: `PiOfQMLattice` and `R2CMOnC` from T11a in `Hom` form and R2 on `ℂ`-points

`T11aHom` is T11a for homomorphisms (the same textbook theorem; leaf-push2's `T11a_RiemannEnd` is
its `A = B` case). `R2OnC` (glue) says that R2's clause list holds at complex points. From them:
`piOfQMLattice_of` (an `ι`-equivariant analytic isomorphism of the QM tori is algebraic, so the
QM pairs are isomorphic and `π` agrees) and `r2CMOnC_of` (immediate). -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic Matrix
open ZInQ.LeafPush2 (CPts IsUniformization isUniformization_of_bp)

/-- **T11(a) in `Hom` form (textbook leaf candidate; the same theorem as leaf-push2's
`T11a_RiemannEnd`, which is its case `A = B`).** For complex abelian varieties `A`, `B` of
dimension `g` with uniformizations `Φ_A`, `Φ_B` (kernels `Λ_A`, `Λ_B`), every `ℂ`-linear `M` with
`MΛ_A ⊆ Λ_B` is induced by a unique homomorphism `f : A → B` (`Φ_B(Mz) = f(Φ_A(z))`).
Mumford, *Abelian varieties*, §1-§2; Birkenhake–Lange, Prop. 1.2.1 (for complex tori); GAGA,
Serre 1956, for "holomorphic ⇒ algebraic" (UNVERIFIED numbers). -/
def T11aHom : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA ΛB : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin g → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- R2's clause list (`R2fpProps`) at complex points. -/
def R2fpPropsC (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  ∀ (y y' : fieldPt ℂ ⟶ Y) (P Q : QML3 ℂ),
    Φ ℂ y = M3.mk P → Φ ℂ y' = M3.mk Q →
      (π.val (K := ℂ) y.left = π.val (K := ℂ) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q → π.val (K := ℂ) y.left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := ℂ) y.left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := ℂ) y.left = OnePoint.some (-16 / 27))

/-- **GLUE (R2 at complex points).** Why true: the published statement behind `R2fpProps`
(Baba–Granath, with R1 at level one) is about `X₆` and `X₆/W ≅ P¹` over `ℚ`, and the coarse moduli
property holds over every algebraically closed field of characteristic 0, `ℂ` included. For a
candidate `(Y, Φ, π)` satisfying the clause lists: `(Y, Φ)` is isomorphic to `Y₃` compatibly with
`Φ` (`phi_part` both ways; a self-map of a reduced separated scheme that is the identity on all
field points is the identity); `π` agrees with the published map on `ℚ̄`-points (same fibres and
three values, so they differ by a bijection of `P¹(ℚ̄)` that is algebraic, hence Möbius, hence the
identity: qm-pin's `MobiusGlue` argument); and a morphism is determined by its values on the
dense set of `ℚ̄`-points of the reduced `Y`. So `π` is the published map, and its fibres and CM
values at `ℂ`-points are the coarse-moduli ones (Lefschetz principle). -/
def R2OnC : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → R2fpPropsC Y Φ π

theorem r2CMOnC_of (h : R2OnC) : R2CMOnC := by
  intro Y Φ π h1 h2 y P hP
  obtain ⟨-, h4, h3, h24⟩ := h Y Φ π h1 h2 y y P P hP hP
  exact ⟨h4, h3, h24⟩

section HomInduces

variable {P P' : QML3 ℂ} {τ : ℂ} {hτ : τ.im ≠ 0}

theorem dim_two (P : QML3 ℂ) : P.A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [P.surface]; norm_cast

/-- The homomorphism induced by a `Λ_τ`-preserving `M`, between two uniformized objects. -/
theorem existsUnique_hom (hT : T11aHom)
    {φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)}
    {φ' : Torus (QM.qmLattice hτ) ≃+ Additive (P'.A.Pt ℂ)}
    (hφ : Uniformization.IsUniformization P.A (QM.qmLattice hτ) φ)
    (hφ' : Uniformization.IsUniformization P'.A (QM.qmLattice hτ) φ')
    {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} (hM : ∀ z ∈ QM.qmLattice hτ, M z ∈ QM.qmLattice hτ) :
    ∃! f : AbVar.Hom P.A P'.A, ∀ z, unifMap φ' (M z) = unifMap φ z ≫ f.hom :=
  hT P.A P'.A 2 _ _ (unifMap φ) (unifMap φ') (dim_two P) (dim_two P')
    (isUniformization_of_bp P.A hφ) (isUniformization_of_bp P'.A hφ') M hM

end HomInduces

/-- **`PiOfQMLattice` from `T11aHom` and `R2OnC` (proved).** -/
theorem piOfQMLattice_of (hT : T11aHom) (hR : R2OnC) : PiOfQMLattice := by
  intro Y Φ π h1 h2 y y' P P' hP hP' τ hτ φ φ' hφ hφ'
  have hid : ∀ z ∈ QM.qmLattice hτ, (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈
      QM.qmLattice hτ := fun z hz => hz
  obtain ⟨f, hf, -⟩ := existsUnique_hom hT hφ.unif hφ'.unif hid
  obtain ⟨g, hg, -⟩ := existsUnique_hom hT hφ'.unif hφ.unif hid
  -- `g ∘ f = 1` and `f ∘ g = 1`, by uniqueness for `M = id`
  have hgf : f.hom ≫ g.hom = 𝟙 _ := by
    have u := existsUnique_hom hT hφ.unif hφ.unif hid
    have e1 : ∀ z, unifMap φ ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (f.hom ≫ g.hom) : AbVar.Hom P.A P.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hf z]
      exact hg z
    have e2 : ∀ z, unifMap φ ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (𝟙 P.A.X) : AbVar.Hom P.A P.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', Category.comp_id]
      rfl
    have := u.unique e1 e2
    simpa using congrArg AbVar.Hom.hom this
  have hfg : g.hom ≫ f.hom = 𝟙 _ := by
    have u := existsUnique_hom hT hφ'.unif hφ'.unif hid
    have e1 : ∀ z, unifMap φ' ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ' z ≫ (AbVar.Hom.mk' (g.hom ≫ f.hom) : AbVar.Hom P'.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hg z]
      exact hf z
    have e2 : ∀ z, unifMap φ' ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ' z ≫ (AbVar.Hom.mk' (𝟙 P'.A.X) : AbVar.Hom P'.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', Category.comp_id]
      rfl
    have := u.unique e1 e2
    simpa using congrArg AbVar.Hom.hom this
  -- equivariance, by uniqueness for `M = ι(a)`
  have heq : ∀ a : O, (P.q.iota a).hom ≫ f.hom = f.hom ≫ (P'.q.iota a).hom := by
    intro a
    have hMa : ∀ z ∈ QM.qmLattice hτ, Matrix.toLin' (iotaC (a : LeafQM.B)) z ∈
        QM.qmLattice hτ := fun z hz => by rw [Matrix.toLin'_apply]; exact iotaC_mem a hτ hz
    have u := existsUnique_hom hT hφ.unif hφ'.unif hMa
    have e1 : ∀ z, unifMap φ' (Matrix.toLin' (iotaC (a : LeafQM.B)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' ((P.q.iota a).hom ≫ f.hom) : AbVar.Hom P.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← induces_iota hφ a z]
      exact hf _
    have e2 : ∀ z, unifMap φ' (Matrix.toLin' (iotaC (a : LeafQM.B)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (f.hom ≫ (P'.q.iota a).hom) : AbVar.Hom P.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hf z]
      exact induces_iota hφ' a z
    have := u.unique e1 e2
    simpa using congrArg AbVar.Hom.hom this
  have iso : QMIso (P.q.twist (RingEquiv.refl O)) P'.q :=
    { φ := f, ψ := g, left := hgf, right := hfg, equivariant := fun a => heq a }
  exact ((hR Y Φ π h1 h2 y y' P P' hP hP').1).2 ⟨RingEquiv.refl O, ⟨iso⟩⟩

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul`, T11a (both forms) and six glue Props
(proved).** -/
theorem fibreQMPeriod_of_r1b_T11aHom (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hT : ZInQ.LeafPush2.T11a_RiemannEnd) (hTH : T11aHom)
    (hM : MobiusRigidity) (hHol : HauptmodulHolomorphic) (hO : FamilyOrbits) (hR : R2OnC)
    (hC : JDenNonzero) (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b_T11a hR1b hH hT hM hHol hO (r2CMOnC_of hR) (piOfQMLattice_of hTH hR) hC hU

end R1bState

/-! # r1b-state, part 8c: half of `FamilyOrbits` (`Γ*`-invariance) from `T11aHom` and `R2OnC`

`FamilyOrbits` is split into `FamilyOrbitsInv` (`π ∘ y` is `Γ*`-invariant) and `FamilyOrbitsSep`
(its fibres are no larger than the `Γ*`-orbits). The first is proved here
(`familyOrbitsInv_of`). For `γ = ι(x) ∈ Γ*` (`x` normalizes `𝒪`, `y = x⁻¹`, `det > 0`) and
`μ = cτ + d`, the map `M = μ⁻¹ι(x)` carries `Λ_τ` into `Λ_{γτ}` (`ι(x)ι(b)(τ, 1)ᵀ = μ·ι(xby)(γτ, 1)ᵀ`),
`M' = μι(y)` carries it back, and `Mι(yax) = ι(a)M`. By `T11aHom` they are induced by
homomorphisms, inverse to each other by uniqueness, and the first is equivariant for the twist
by `a ↦ yax`; so the QM pairs at `τ` and `γτ` are twist-isomorphic and R2's fibre clause (on
`ℂ`-points, `R2OnC`) gives equal `π`. `FamilyOrbitsSep` (the converse; it needs every
homomorphism to be induced by a linear map, Skolem–Noether, and the centralizer of `ι(B)` in
`M₂(ℂ)`) stays glue. -/

noncomputable section

namespace R1bState

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV PkgI3 BPAnalytic Matrix
open ZInQ.LeafPush2 (CPts IsUniformization isUniformization_of_bp)

/-- **GLUE half 1 (`Γ*`-invariance), proved below from `T11aHom` and `R2OnC`.** -/
def FamilyOrbitsInv : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) →
    ∀ (τ : UpperHalfPlane) (g : GL (Fin 2) ℝ), g ∈ PkgI1.GammaStar →
      π.val (K := ℂ) (y τ).left = π.val (K := ℂ) (y (g • τ : UpperHalfPlane)).left

/-- **GLUE half 2 (fibres no larger than `Γ*`-orbits).** Why true: an isomorphism of the QM pairs
at `τ`, `τ'` up to a twist `α` is induced by a linear `M` with `MΛ_τ = Λ_{τ'}` (T11a, second half,
in `Hom` form) and `Mι(α(a)) = ι(a)M`; `α = Ad n⁻¹` (Skolem–Noether, T13) with `n ∈ N_B(𝒪)`, so
`Mι(n)⁻¹` centralizes `ι(B)`, hence is a scalar, and `τ' = γτ` for `γ = ι(nu) ∈ Γ*` (`u ∈ 𝒪^×`
fixing the sign of the determinant). With R2's fibre clause on `ℂ`-points. -/
def FamilyOrbitsSep : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    ∀ y : ℂ → (fieldPt ℂ ⟶ Y),
      (∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (P : QML3 ℂ)
        (φ : Torus (QM.qmLattice hτ.ne') ≃+ Additive (P.A.Pt ℂ)),
        Φ ℂ (y τ) = M3.mk P ∧ IsQMUnifLevel P hτ.ne' φ) →
    ∀ τ τ' : UpperHalfPlane, π.val (K := ℂ) (y τ).left = π.val (K := ℂ) (y τ').left →
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ'

theorem familyOrbits_of_halves (h1 : FamilyOrbitsInv) (h2 : FamilyOrbitsSep) : FamilyOrbits := by
  intro Y Φ π hY hR y hb τ τ'
  constructor
  · exact h2 Y Φ π hY hR y hb τ τ'
  · rintro ⟨g, hg, rfl⟩
    exact h1 Y Φ π hY hR y hb τ g hg

/-! ### The proof of `FamilyOrbitsInv` -/

theorem pkgI1_inO_of {x : LeafQM.B} (hx : LeafQM.InO x) : PkgI1.InO x := by
  obtain ⟨n, rfl⟩ := hx
  refine ⟨n, ?_⟩
  ext <;> simp [ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- Conjugation `a ↦ yax` by a normalizer element (`xy = yx = 1`), as a ring automorphism of `𝒪`. -/
def conjO (x y : LeafQM.B) (hxy : x * y = 1) (hyx : y * x = 1)
    (hn : ∀ z : PkgI1.B, PkgI1.InO z → PkgI1.InO (x * z * y) ∧ PkgI1.InO (y * z * x)) :
    O ≃+* O where
  toFun a := ⟨y * a * x, inO_of_pkgI1 (hn a (pkgI1_inO_of a.2)).2⟩
  invFun a := ⟨x * a * y, inO_of_pkgI1 (hn a (pkgI1_inO_of a.2)).1⟩
  left_inv a := by
    apply Subtype.ext
    change x * (y * (a : LeafQM.B) * x) * y = a
    calc x * (y * (a : LeafQM.B) * x) * y = (x * y) * a * (x * y) := by noncomm_ring
      _ = a := by rw [hxy, _root_.one_mul, _root_.mul_one]
  right_inv a := by
    apply Subtype.ext
    change y * (x * (a : LeafQM.B) * y) * x = a
    calc y * (x * (a : LeafQM.B) * y) * x = (y * x) * a * (y * x) := by noncomm_ring
      _ = a := by rw [hyx, _root_.one_mul, _root_.mul_one]
  map_mul' a b := by
    apply Subtype.ext
    change y * ((a : LeafQM.B) * b) * x = (y * a * x) * (y * b * x)
    calc y * ((a : LeafQM.B) * b) * x = y * a * (x * y) * b * x := by rw [hxy]; noncomm_ring
      _ = (y * a * x) * (y * b * x) := by noncomm_ring
  map_add' a b := by
    apply Subtype.ext
    change y * ((a : LeafQM.B) + b) * x = y * a * x + y * b * x
    noncomm_ring

theorem iotaC_one : iotaC (1 : LeafQM.B) = 1 := by
  unfold iotaC; rw [iota_one]; simp

/-- The homomorphism induced by `M : Λ_τ → Λ_{τ'}` between two uniformized objects. -/
theorem existsUnique_hom2 (hT : T11aHom) {P P' : QML3 ℂ} {τ τ' : ℂ} {hτ : τ.im ≠ 0}
    {hτ' : τ'.im ≠ 0}
    {φ : Torus (QM.qmLattice hτ) ≃+ Additive (P.A.Pt ℂ)}
    {φ' : Torus (QM.qmLattice hτ') ≃+ Additive (P'.A.Pt ℂ)}
    (hφ : Uniformization.IsUniformization P.A (QM.qmLattice hτ) φ)
    (hφ' : Uniformization.IsUniformization P'.A (QM.qmLattice hτ') φ')
    {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} (hM : ∀ z ∈ QM.qmLattice hτ, M z ∈ QM.qmLattice hτ') :
    ∃! f : AbVar.Hom P.A P'.A, ∀ z, unifMap φ' (M z) = unifMap φ z ≫ f.hom :=
  hT P.A P'.A 2 _ _ (unifMap φ) (unifMap φ') (dim_two P) (dim_two P')
    (isUniformization_of_bp P.A hφ) (isUniformization_of_bp P'.A hφ') M hM

/-- A linear map carrying generators of `Λ_τ` into `Λ_{τ'}` carries `Λ_τ` into `Λ_{τ'}`. -/
theorem map_qmLattice {τ τ' : ℂ} (hτ : τ.im ≠ 0) (hτ' : τ'.im ≠ 0)
    (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
    (hgen : ∀ k, M (QM.qmVec τ k) ∈ QM.qmLattice hτ') :
    ∀ z ∈ QM.qmLattice hτ, M z ∈ QM.qmLattice hτ' := by
  intro z hz
  rw [QM.qmLattice_eq] at hz
  induction hz using Submodule.span_induction with
  | mem w hw => obtain ⟨k, rfl⟩ := hw; exact hgen k
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul n v _ hv => rw [map_zsmul]; exact Submodule.smul_mem _ n hv

/-- `ι(x)(τ, 1)ᵀ = μ·(γτ, 1)ᵀ` with `μ = cτ + d`, for `γ = ι(x)`, `det > 0`. -/
theorem iotaC_mulVec_smul {x : PkgI1.B} {g : GL (Fin 2) ℝ}
    (hm : (g : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x) (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (τ : UpperHalfPlane) :
    iotaC x *ᵥ ![(τ : ℂ), 1] = UpperHalfPlane.denom g τ • ![((g • τ : UpperHalfPlane) : ℂ), 1] := by
  have hg : 0 < g.det.val := by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet
  have h := UpperHalfPlane.coe_smul_of_det_pos hg τ
  have hd := UpperHalfPlane.denom_ne_zero g τ
  rw [h]
  ext i
  fin_cases i
  · simp only [iotaC, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul,
      Fin.isValue, Fin.zero_eta]
    rw [mul_div_cancel₀ _ hd]
    simp [UpperHalfPlane.num, hm, pkgI1_iota_eq]
  · simp [iotaC, Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom, hm,
      pkgI1_iota_eq]

/-- **`FamilyOrbitsInv` from `T11aHom` and `R2OnC` (proved).** -/
theorem familyOrbitsInv_of (hT : T11aHom) (hR : R2OnC) : FamilyOrbitsInv := by
  intro Y Φ π h1 h2 yf hb τ g hgΓ
  obtain ⟨x, ⟨y, hxy, hyx, hn⟩, hm, hdet⟩ := hgΓ
  set τ' : UpperHalfPlane := g • τ
  set dg : ℂ := UpperHalfPlane.denom g τ
  have hdg : dg ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  have hv : iotaC x *ᵥ ![(τ : ℂ), 1] = dg • ![(τ' : ℂ), 1] := iotaC_mulVec_smul hm hdet τ
  obtain ⟨P, φ, hP, hφ, -⟩ := hb τ τ.im_pos
  obtain ⟨P', φ', hP', hφ', -⟩ := hb τ' τ'.im_pos
  -- the two lattice maps `M = dg⁻¹ι(x)`, `M' = dgι(y)`
  let M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := dg⁻¹ • Matrix.toLin' (iotaC x)
  let M' : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := dg • Matrix.toLin' (iotaC y)
  have hM_lat : ∀ b : LeafQM.B, M (QM.latVec b τ) = QM.latVec (x * b * y) τ' := by
    intro b
    simp only [M, LinearMap.smul_apply, Matrix.toLin'_apply]
    rw [latVec_eq, latVec_eq, Matrix.mulVec_mulVec, ← iotaC_mul]
    have e : iotaC (x * b) = iotaC (x * b * y) * iotaC x := by
      rw [← iotaC_mul, _root_.mul_assoc (x * b) y x, hyx, _root_.mul_one]
    rw [e, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hdg, one_smul]
  have hM'_lat : ∀ b : LeafQM.B, M' (QM.latVec b τ') = QM.latVec (y * b * x) τ := by
    intro b
    simp only [M', LinearMap.smul_apply, Matrix.toLin'_apply]
    rw [latVec_eq, latVec_eq, Matrix.mulVec_mulVec, ← iotaC_mul, iotaC_mul (y * b) x,
      ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hM_mem : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
      M z ∈ QM.qmLattice (τ := (τ' : ℂ)) (coe_im_ne_zero τ') :=
    map_qmLattice _ _ M fun k => by
      rw [QM.qmVec, hM_lat]
      exact latVec_mem_of_inO (inO_of_pkgI1 (hn _ (pkgI1_inO_of (oBasis_inO k))).1) _
  have hM'_mem : ∀ z ∈ QM.qmLattice (τ := (τ' : ℂ)) (coe_im_ne_zero τ'),
      M' z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ) :=
    map_qmLattice _ _ M' fun k => by
      rw [QM.qmVec, hM'_lat]
      exact latVec_mem_of_inO (inO_of_pkgI1 (hn _ (pkgI1_inO_of (oBasis_inO k))).2) _
  have hM'M : ∀ z, M' (M z) = z := by
    intro z
    simp only [M, M', LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.mulVec_smul, smul_smul,
      Matrix.mulVec_mulVec, ← iotaC_mul, hyx, iotaC_one, Matrix.one_mulVec,
      mul_inv_cancel₀ hdg, one_smul]
  have hMM' : ∀ z, M (M' z) = z := by
    intro z
    simp only [M, M', LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.mulVec_smul, smul_smul,
      Matrix.mulVec_mulVec, ← iotaC_mul, hxy, iotaC_one, Matrix.one_mulVec,
      inv_mul_cancel₀ hdg, one_smul]
  obtain ⟨f, hf, -⟩ := existsUnique_hom2 hT hφ.unif hφ'.unif hM_mem
  obtain ⟨h, hh, -⟩ := existsUnique_hom2 hT hφ'.unif hφ.unif hM'_mem
  have hid : ∀ (σ : UpperHalfPlane) (z : Fin 2 → ℂ),
      z ∈ QM.qmLattice (τ := (σ : ℂ)) (coe_im_ne_zero σ) →
      (LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈
        QM.qmLattice (τ := (σ : ℂ)) (coe_im_ne_zero σ) := fun _ _ hz => hz
  have hgf : f.hom ≫ h.hom = 𝟙 _ := by
    have u := existsUnique_hom2 hT hφ.unif hφ.unif (hid τ)
    have e1 : ∀ z, unifMap φ ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (f.hom ≫ h.hom) : AbVar.Hom P.A P.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hf z, ← hh (M z), hM'M]
      rfl
    have e2 : ∀ z, unifMap φ ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (𝟙 P.A.X) : AbVar.Hom P.A P.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', Category.comp_id]
      rfl
    simpa using congrArg AbVar.Hom.hom (u.unique e1 e2)
  have hfg : h.hom ≫ f.hom = 𝟙 _ := by
    have u := existsUnique_hom2 hT hφ'.unif hφ'.unif (hid τ')
    have e1 : ∀ z, unifMap φ' ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ' z ≫ (AbVar.Hom.mk' (h.hom ≫ f.hom) : AbVar.Hom P'.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hh z, ← hf (M' z), hMM']
      rfl
    have e2 : ∀ z, unifMap φ' ((LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
        unifMap φ' z ≫ (AbVar.Hom.mk' (𝟙 P'.A.X) : AbVar.Hom P'.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', Category.comp_id]
      rfl
    simpa using congrArg AbVar.Hom.hom (u.unique e1 e2)
  -- equivariance for the twist `a ↦ yax`
  let α := conjO x y hxy hyx hn
  have hlin : ∀ (a : O) (z : Fin 2 → ℂ),
      M (iotaC ((α a : O) : LeafQM.B) *ᵥ z) = iotaC (a : LeafQM.B) *ᵥ M z := by
    intro a z
    simp only [M, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, ← iotaC_mul]
    congr 3
    change x * (y * (a : LeafQM.B) * x) = a * x
    calc x * (y * (a : LeafQM.B) * x) = (x * y) * a * x := by noncomm_ring
      _ = a * x := by rw [hxy, _root_.one_mul]
  have heq : ∀ a : O, ((P.q.twist α).iota a).hom ≫ f.hom = f.hom ≫ (P'.q.iota a).hom := by
    intro a
    change (P.q.iota (α a)).hom ≫ f.hom = f.hom ≫ (P'.q.iota a).hom
    have hMa : ∀ z ∈ QM.qmLattice (τ := (τ : ℂ)) (coe_im_ne_zero τ),
        (M ∘ₗ Matrix.toLin' (iotaC ((α a : O) : LeafQM.B))) z ∈
          QM.qmLattice (τ := (τ' : ℂ)) (coe_im_ne_zero τ') := by
      intro z hz
      rw [LinearMap.comp_apply, Matrix.toLin'_apply]
      exact hM_mem _ (iotaC_mem (α a) _ hz)
    have u := existsUnique_hom2 hT hφ.unif hφ'.unif hMa
    have e1 : ∀ z, unifMap φ' ((M ∘ₗ Matrix.toLin' (iotaC ((α a : O) : LeafQM.B))) z) =
        unifMap φ z ≫
          (AbVar.Hom.mk' ((P.q.iota (α a)).hom ≫ f.hom) : AbVar.Hom P.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← induces_iota hφ (α a) z]
      exact hf _
    have e2 : ∀ z, unifMap φ' ((M ∘ₗ Matrix.toLin' (iotaC ((α a : O) : LeafQM.B))) z) =
        unifMap φ z ≫ (AbVar.Hom.mk' (f.hom ≫ (P'.q.iota a).hom) : AbVar.Hom P.A P'.A).hom := by
      intro z
      rw [AbVar.Hom.hom_mk', ← Category.assoc, ← hf z, LinearMap.comp_apply,
        Matrix.toLin'_apply, hlin]
      exact induces_iota hφ' a (M z)
    simpa using congrArg AbVar.Hom.hom (u.unique e1 e2)
  have iso : QMIso (P.q.twist α) P'.q :=
    { φ := f, ψ := h, left := hgf, right := hfg, equivariant := heq }
  exact ((hR Y Φ π h1 h2 (yf τ) (yf τ') P P' hP hP').1).2 ⟨α, ⟨iso⟩⟩

/-- **`FibreQMPeriod` from R1(b), `QMHauptmodul`, T11a (both forms) and six glue Props, one of
them (`FamilyOrbitsSep`) half of the former `FamilyOrbits` (proved).** -/
theorem fibreQMPeriod_of_r1b_orbits (hR1b : R01b_ComplexUniformization')
    (hH : PkgI1.QMHauptmodul) (hT : ZInQ.LeafPush2.T11a_RiemannEnd) (hTH : T11aHom)
    (hM : MobiusRigidity) (hHol : HauptmodulHolomorphic) (hS : FamilyOrbitsSep) (hR : R2OnC)
    (hC : JDenNonzero) (hU : UnifBaseChange) : FibreQMPeriod' :=
  fibreQMPeriod_of_r1b_T11aHom hR1b hH hT hTH hM hHol
    (familyOrbits_of_halves (familyOrbitsInv_of hTH hR) hS) hR hC hU

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
#print axioms R1bState.hauptmodulCompare_of_parts
#print axioms R1bState.fibreQMPeriod_of_r1b_parts
#print axioms R1bState.familyHauptmodul_of_parts
#print axioms R1bState.fibreQMPeriod_of_r1b_fine
#print axioms R1bState.cmPointsExist
#print axioms R1bState.fibreQMPeriod_of_r1b_final
#print axioms R1bState.familyCMValues_of_T11a
#print axioms R1bState.fibreQMPeriod_of_r1b_T11a
#print axioms R1bState.piOfQMLattice_of
#print axioms R1bState.fibreQMPeriod_of_r1b_T11aHom
#print axioms R1bState.familyOrbitsInv_of
#print axioms R1bState.fibreQMPeriod_of_r1b_orbits
