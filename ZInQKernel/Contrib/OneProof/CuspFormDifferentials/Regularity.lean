import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.JDerivative
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.NativeValue

/-! Rational functions and rational differentials `(A / B) · dj` on the complexified
modular curve, regularity at a point, and the named statements K8–K12 of Route B that
this lane takes as hypotheses.

Algebraic representation. An element `c ⊗ a` of `ℂ ⊗[ℚ] ℚ(X₀(N))` is represented on an
open `W` of `curveC N` by `c` times the pullback, along the projection to the model, of
a regular function on an open `V` of the model whose image in the function field is
`a`, provided `W` lies over `V`; sums are represented by sums (`RepOn`). A section `θ` of
`Ω¹` over `W` represents `(A / B) · dj` (`RepresentsDiffOn`) when on every smaller open
`W'` carrying representatives `s`, `b`, `c` of `A`, `B` and `1 ⊗ j`, with `b` a unit,
one has `b · θ = s · dc`. The rational differential is regular at a point `x` when
some section over an open neighbourhood of `x` represents it (`DiffRegularAt`).

Statements (readings of the route design):
* K8, a complex-linear map from global differentials to weight-two cusp forms on
  `Γ₀(N)` whose underlying function is the native value;
* K9, a global differential with vanishing native value is zero;
* K10, every closed point is an arc point `P τ` or a cusp, a cusp being the analytic
  limit of `P(στ)` as `Im τ → ∞` for some `σ ∈ SL(2, ℤ)`;
* K11, valuation scaling and the regularity criterion at arc points and at cusps, in
  analytic form: at `P τ` with ramification index `e`, for `F` representing
  `(A / B) · j′`, the order `ord_τ F` satisfies `e ∣ ord_τ F + 1`, and the differential is
  regular at `P τ` when `ord_τ F ≥ e - 1` (equivalently, its valuation in a local
  parameter is `(ord_τ F + 1)/e - 1 ≥ 0`); at a cusp `σ(∞)` it is regular when the
  weight-two slash `F ∣[2] σ` vanishes at `i∞`;
* K12, a rational differential regular at every closed point is a global section. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology TensorProduct MatrixGroups ModularForm

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open X0Model J0Cusps

variable (N : ℕ) [NeZero N]

/-- The projection of the complexified curve to the model over `ℚ`. -/
abbrev toModel : (curveC N).left ⟶ X0Model.curve N :=
  Limits.pullback.fst (source N).hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))

/-- The element `1 ⊗ j` of `ℂ ⊗[ℚ] ℚ(X₀(N))`. -/
abbrev jC : FieldC N := (1 : ℂ) ⊗ₜ jField N

/-- `RepOn N W A s`: the section `s` over `W` represents `A ∈ ℂ ⊗[ℚ] ℚ(X₀(N))`. -/
inductive RepOn (W : (curveC N).left.Opens) : FieldC N → Γ((curveC N).left, W) → Prop
  | zero : RepOn W 0 0
  | tmul (c : ℂ) (V : (X0Model.curve N).Opens) [Nonempty V] (r : Γ(X0Model.curve N, V))
      (hW : W ≤ toModel N ⁻¹ᵁ V) :
      RepOn W (c ⊗ₜ X0Model.functionField N ((X0Model.curve N).germToFunctionField V r))
        ((curveC N).hom.specStructureMap W c *
          (curveC N).left.presheaf.map (homOfLE hW).op ((toModel N).app V r))
  | add {A B : FieldC N} {s t : Γ((curveC N).left, W)} :
      RepOn W A s → RepOn W B t → RepOn W (A + B) (s + t)

/-- `θ` represents the rational differential `(A / B) · dj` on `W`. -/
def RepresentsDiffOn (W : (curveC N).left.Opens)
    (θ : Γ((curveC N).hom.relativeDifferentials, W)) (A B : FieldC N) : Prop :=
  ∀ (W' : (curveC N).left.Opens) (hW' : W' ≤ W) (s b c : Γ((curveC N).left, W')),
    RepOn N W' A s → RepOn N W' B b → RepOn N W' (jC N) c → IsUnit b →
      b • (curveC N).hom.relativeDifferentials.presheaf.map (homOfLE hW').op θ =
        s • (curveC N).hom.sectionsD W' c

/-- The rational differential `(A / B) · dj` is regular at `x`. -/
def DiffRegularAt (x : (curveC N).left) (A B : FieldC N) : Prop :=
  ∃ (W : (curveC N).left.Opens) (_ : x ∈ W) (θ : Γ((curveC N).hom.relativeDifferentials, W)),
    RepresentsDiffOn N W θ A B

/-- The germ of `A / B` at a point of `ℍ`. -/
abbrev ratGerm (τ : ℍ) (A B : FieldC N) : MeromorphicGerm (τ : ℂ) :=
  fieldGermC N τ A / fieldGermC N τ B

/-- The analytic limit of `P(στ)` as `Im τ → ∞`, i.e. `p` is the cusp `σ(∞)`. -/
def IsCuspLimit (σ : SL(2, ℤ)) (p : ComplexPoint (curveC N)) : Prop :=
  Tendsto (fun τ : ℍ => arcPoint N (σ • τ)) atImInfty (𝓝 p)

/-- **K8.** A complex-linear map from global differentials to weight-two cusp forms on
`Γ₀(N)` whose underlying function is the native value. -/
def K8 : Prop :=
  letI := differentialsModule N
  ∃ Φ : Γ((curveC N).hom.relativeDifferentials, ⊤) →ₗ[ℂ] CuspFormN N,
    ∀ ω τ, Φ ω τ = nativeValue N ω τ

/-- **K9.** A global differential whose native value vanishes on `ℍ` is zero. -/
def K9 : Prop :=
  ∀ ω : Γ((curveC N).hom.relativeDifferentials, ⊤), nativeValue N ω = 0 → ω = 0

/-- **K10.** Every closed point of `curveC N` is an arc point `P τ` or a cusp. -/
def K10 : Prop :=
  ∀ x : (curveC N).left, IsClosed ({x} : Set (curveC N).left) →
    (∃ τ : ℍ, (arcPoint N τ).underlying = x) ∨
      ∃ (σ : SL(2, ℤ)) (p : ComplexPoint (curveC N)), p.underlying = x ∧ IsCuspLimit N σ p

/-- **K11 at arc points.** Valuation scaling with ramification index `e` at `P τ` and the
regularity criterion, for a function `F` representing `(A / B) · j′` near `τ`. -/
def K11Arc : Prop :=
  ∀ τ : ℍ, ∃ e : ℕ, 0 < e ∧ ∀ (A B : FieldC N) (F : ℂ → ℂ), fieldGermC N τ B ≠ 0 →
    MeromorphicAt F (τ : ℂ) →
    (F : PuncturedGerm (τ : ℂ)) = meromorphicIncl (τ : ℂ) (ratGerm N τ A B * jDerivGerm τ) →
      (∀ n : ℤ, meromorphicOrderAt F (τ : ℂ) = n → (e : ℤ) ∣ n + 1) ∧
      ((((e : ℤ) - 1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F (τ : ℂ) →
        DiffRegularAt N (arcPoint N τ).underlying A B)

/-- **K11 at cusps.** At the cusp `σ(∞)`, the differential `(A / B) · dj` is regular when
the function `F = (A / B) · j′` is holomorphic near the cusp and its weight-two slash by
`σ` vanishes at `i∞`. -/
def K11Cusp : Prop :=
  ∀ (σ : SL(2, ℤ)) (p : ComplexPoint (curveC N)), IsCuspLimit N σ p →
    ∀ (A B : FieldC N) (F : ℍ → ℂ), (∀ τ : ℍ, fieldGermC N τ B ≠ 0) →
      (∀ τ : ℍ, ((F ∘ ofComplex : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) =
        meromorphicIncl (τ : ℂ) (ratGerm N τ A B * jDerivGerm τ)) →
      (∀ᶠ τ in atImInfty, DifferentiableAt ℂ (F ∘ ofComplex) ((σ • τ : ℍ) : ℂ)) →
      IsZeroAtImInfty (F ∣[(2 : ℤ)] σ) → DiffRegularAt N p.underlying A B

/-- **K12.** A rational differential regular at every closed point is a global section. -/
def K12 : Prop :=
  ∀ A B : FieldC N,
    (∀ x : (curveC N).left, IsClosed ({x} : Set (curveC N).left) → DiffRegularAt N x A B) →
      ∃ ω : Γ((curveC N).hom.relativeDifferentials, ⊤), RepresentsDiffOn N ⊤ ω A B

end ZInQ.Manuscript.RC.CuspFormDifferentials
