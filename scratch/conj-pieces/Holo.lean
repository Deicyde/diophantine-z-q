import ZInQKernel.HDecomp.LeafPush2.T

/-! # conj-pieces §B: `HomLinearLift` (N2) from the analytic leaf `HoloHomLift`

Check with `lake env lean scratch/conj-pieces/Holo.lean` (after
`lake build ZInQKernel.HDecomp.LeafPush2.T`).

* `HomLinearLift` is copied verbatim from `scratch/conj-twist/ConjTwist.lean`.
* `HoloHomLift` (new, textbook leaf): a homomorphism `Ψ : ℂ^g → B(ℂ)_σ` that is holomorphic in the
  sense of `IsUniformization` (open preimages of affine charts, holomorphic regular functions)
  lifts to a `ℂ`-linear map through any uniformization `Φ_B` of `B(ℂ)_σ`.
* Proved: algebraic morphisms preserve that holomorphy (`cDom_comp`, `cEvalAt_comp`), so
  `homLinearLift_of_holoHomLift : HoloHomLift → HomLinearLift` (apply the leaf to
  `Ψ = f ∘ Φ_A`). -/

noncomputable section

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj

open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)

/-- **N2. T11(a) in Hom form (textbook LEAF; Birkenhake–Lange, *Complex abelian varieties*,
Prop. 1.2.1, with holomorphy of algebraic morphisms; Mumford §1; UNVERIFIED numbers).** For
abelian varieties `A, B` over `K`, `σ : K → ℂ` and uniformizations `Φ_A, Φ_B` of `A(ℂ)_σ`,
`B(ℂ)_σ`, every homomorphism `f : A → B` lifts to a `ℂ`-linear map `M` with
`Φ_B(Mz) = f(Φ_A(z))`. (`T11a_RiemannEnd`'s second half is the case `A = B` over `ℂ`.) -/
def HomLinearLift : Prop :=
  ∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom

/-- **N2′. Holomorphic homomorphisms into a uniformized abelian variety are linear (textbook
LEAF).** Let `B` be an abelian variety over `K`, `σ : K → ℂ`, `h = dim B`, and `Φ_B` a
uniformization of `B(ℂ)_σ` (`IsUniformization`). If `Ψ : ℂ^g → B(ℂ)_σ` is a homomorphism which is
holomorphic in the same sense (the preimage of every affine-chart domain is open and every regular
function is holomorphic on it), then `Ψ = Φ_B ∘ M` for a `ℂ`-linear `M : ℂ^g → ℂ^h`.

Source: Mumford, *Abelian varieties*, §1 (`B(ℂ)_σ ≅ ℂ^h/Λ_B` as complex Lie groups, with GAGA,
Serre 1956), and Birkenhake–Lange, *Complex abelian varieties*, Prop. 1.2.1 (a holomorphic map
of complex tori lifts to an affine map of the universal covers; a homomorphism lifts to a linear
one); UNVERIFIED numbers. The predicate makes `Ψ` a continuous, hence holomorphic,
homomorphism into the complex Lie group `B(ℂ)_σ`, so `Ψ = exp ∘ L`; `Φ_B = exp ∘ T` with `T` a
linear isomorphism (`Φ_B` is onto), and `M = T⁻¹L`. It involves one variety and no algebraic
morphism; `HomLinearLift` is the case `Ψ = f ∘ Φ_A`. -/
def HoloHomLift : Prop :=
  ∀ (K : Type) [Field K] (B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛB : Submodule ℤ (Fin h → ℂ)) (ΦB : (Fin h → ℂ) → CPts B σ) (Ψ : (Fin g → ℂ) → CPts B σ),
    B.dim = (h : WithBot ℕ∞) → IsUniformization σ ΛB ΦB →
    (∀ z w, Ψ (z + w) = Ψ z * Ψ w) → (∀ U, IsOpen (cDom Ψ U)) →
    (∀ U (s : Γ(B.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (Ψ z) U s) (cDom Ψ U)) →
    ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), ∀ z, ΦB (M z) = Ψ z

/-! ## Algebraic morphisms preserve holomorphy (proved) -/

/-- `Ψ ∘ φ` meets the chart `U` exactly where `Ψ` meets `φ⁻¹U` (proved). -/
theorem cDom_comp {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} {g : ℕ}
    (Φ : (Fin g → ℂ) → CPts A σ) (φ : A.X ⟶ B.X) (U : B.X.left.Opens) :
    cDom (fun z => Φ z ≫ φ) U = cDom Φ (φ.left ⁻¹ᵁ U) := rfl

/-- Evaluating a regular function at `p ≫ φ` is evaluating its pullback at `p` (proved). -/
theorem cEvalAt_comp {K : Type} [Field K] {A B : PkgI3.AbVar K} {σ : K →+* ℂ} (p : CPts A σ)
    (φ : A.X ⟶ B.X) (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    cEvalAt (p ≫ φ) U s = cEvalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) := by
  unfold cEvalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

/-- **N2 from N2′ (proved).** -/
theorem homLinearLift_of_holoHomLift (hL : HoloHomLift) : HomLinearLift := by
  intro K _ A B σ g h ΛA ΛB ΦA ΦB _ hB hΦA hΦB f
  refine hL K B σ g h ΛB ΦB (fun z => ΦA z ≫ f.hom) hB hΦB (fun z w => ?_) (fun U => ?_)
    (fun U s => ?_)
  · change ΦA (z + w) ≫ f.hom = (ΦA z ≫ f.hom) * (ΦA w ≫ f.hom)
    rw [hΦA.1, MonObj.mul_comp]
  · rw [cDom_comp]
    exact hΦA.2.2.2.1 _
  · rw [cDom_comp]
    have := hΦA.2.2.2.2 (f.hom.left ⁻¹ᵁ U) (f.hom.left.app U s)
    refine this.congr fun z _ => ?_
    exact cEvalAt_comp (ΦA z) f.hom U s

#print axioms homLinearLift_of_holoHomLift

end G0Galois
