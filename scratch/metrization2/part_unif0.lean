/-! ## metrization2: `AnalyticUniformizationOfDim` from leaf-push2's `UniformizationExists` (T35)

Verbatim copies (with `AbVar` resolving to the `ZInQ.DefFaltings.AbVar` of `Base.lean`, a copy of
`PkgI3.AbVar`) of leaf-push2's `cptObj`, `CPts`, `cEvalAt`, `cDom`, `IsUniformization`
(`ZInQKernel/HDecomp/LeafPush2/R22.lean`, lines 22-56) and `UniformizationExists`
(`ZInQKernel/HDecomp/LeafPush2/T.lean`, lines 26-37). -/

namespace ZInQ.LeafPush2

open NumberField MeasureTheory
open ZInQ.DefFaltings

section R22Sec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Complex


variable {K : Type} [Field K]

/-- `Spec ℂ` as a `K`-scheme via `σ : K → ℂ`. -/
noncomputable def cptObj (σ : K →+* ℂ) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom σ))

/-- The complex points `A(ℂ)_σ` of an abelian variety over `K` at `σ : K → ℂ`, a group
(Mathlib's group structure on morphisms into a group object). -/
abbrev CPts (A : AbVar K) (σ : K →+* ℂ) : Type := cptObj σ ⟶ A.X

noncomputable example (A : AbVar K) (σ : K →+* ℂ) : Group (CPts A σ) := inferInstance

/-- The value `s(p) ∈ ℂ` of a regular function `s ∈ Γ(U, 𝒪_A)` at a complex point `p ∈ U(ℂ)`
(`0` if `p ∉ U(ℂ)`); adapted from `GroupModel.evalAt` of def-faltings §17. -/
noncomputable def cEvalAt {A : AbVar K} {σ : K →+* ℂ} (p : CPts A σ) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ p.left ⁻¹ᵁ U then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (p.left.appLE U ⊤ h s) else 0

/-- `Φ⁻¹(U(ℂ)) ⊆ ℂ^g`. -/
def cDom {A : AbVar K} {σ : K →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → CPts A σ) (U : A.X.left.Opens) :
    Set (Fin g → ℂ) := {z | ⊤ ≤ (Φ z).left ⁻¹ᵁ U}

/-- **Analytic uniformization of `A(ℂ)_σ`** (def-faltings' `IsAnalyticUniformization`, with the
abelian variety in place of a group model): `Φ : ℂ^g → A(ℂ)_σ` a surjective homomorphism with
kernel `Λ`, with open preimages of affine-chart points and holomorphic regular functions. -/
def IsUniformization {A : AbVar K} (σ : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) : Prop :=
  (∀ z w, Φ (z + w) = Φ z * Φ w) ∧
  (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧
  Function.Surjective Φ ∧
  (∀ U, IsOpen (cDom Φ U)) ∧
  (∀ U (s : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Φ z) U s) (cDom Φ U))

end R22Sec

section TSec

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


/-- **AN3 for abelian varieties (textbook leaf; the analytic half of T11/T12).** Every abelian
variety over a field `K` and every `σ : K → ℂ`: `A(ℂ)_σ` has an analytic uniformization by
`ℂ^g`, `g = dim A`, with kernel a full lattice (Mumford, *Abelian varieties*, §1, with GAGA,
Serre 1956, for the complex Lie group structure; UNVERIFIED numbers). The `AbVar` analogue of
def-faltings' `AnalyticUniformizationExists`. -/
def UniformizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (σ : K →+* ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A σ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization σ Λ Φ


end TSec

end ZInQ.LeafPush2
