import ZInQKernel.Contrib.HomUnify.Corr

/-!
# homlattice: `HomLatticeCorr` reduced to two narrow analytic statements

`HomLatticeCorr` (hom-unify, `ZInQKernel/Contrib/HomUnify/Corr.lean`) is
`HomLinearLift ∧ HomRealize` (`ZInQ.HomUnify.corr_iff_lift_realize`). This file separates, in
each half, the elementary scheme/lattice content (proved here) from the analytic content (stated
as narrow hypotheses):

* `IsAnalyticHom σ ψ`: the clauses of `IsUniformization` other than kernel and surjectivity
  (a homomorphism `ℂ^n → A(ℂ)_σ`, open preimages of charts, holomorphic regular functions).
* **Glue (proved).** `isAnalyticHom_comp`: an algebraic homomorphism `f` preserves analyticity
  (`Φ_A ≫ f` is analytic); `isAnalyticHom_lin`: `Φ_B ∘ M` is analytic for `ℂ`-linear `M`.
* **Lifting half.** `AnalyticHomLift` (every analytic homomorphism `ℂ^g → B(ℂ)_σ` factors as
  `Φ_B ∘ M`, `M` linear) implies `HomLinearLift`. `AnalyticHomLift` is itself proved from the
  one-variety statement `UnifLocalInverse` (a uniformization has a holomorphic local inverse at
  `0` whose image is a neighbourhood of the identity) by pure analysis
  (`eq_fderiv_of_locally_additive`: a locally additive map differentiable at `0` is linear on a
  ball).
* **Realization half.** `AnalyticHomAlgebraic` (GAGA + rigidity, for homomorphisms: an analytic
  homomorphism `ℂ^g → B(ℂ)` killing the lattice of a uniformization of `A` comes from an
  algebraic homomorphism `A → B`) implies `HomRealize`.
-/

namespace ZInQ.HomLattice

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization cEvalAt cDom)
open ZInQ.HomUnify (HomLinearLift HomRealize HomLatticeCorr T11aHom)
open Filter Topology

section Defs

variable {K : Type} [Field K]

/-- **Analytic homomorphism `ℂ^n → A(ℂ)_σ`**: the first, fourth and fifth clauses of
`IsUniformization` (homomorphism; preimages of the complex points of every open are open; every
regular function is holomorphic on that preimage). -/
def IsAnalyticHom {A : AbVar K} (σ : K →+* ℂ) {n : ℕ} (ψ : (Fin n → ℂ) → CPts A σ) : Prop :=
  (∀ z w, ψ (z + w) = ψ z * ψ w) ∧
  (∀ U, IsOpen (cDom ψ U)) ∧
  (∀ U (s : Γ(A.X.left, U)), DifferentiableOn ℂ (fun z => cEvalAt (ψ z) U s) (cDom ψ U))

/-- `IsUniformization` = analytic homomorphism + kernel `Λ` + surjective (proved). -/
theorem isUniformization_iff {A : AbVar K} (σ : K →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A σ) :
    IsUniformization σ Λ Φ ↔
      IsAnalyticHom σ Φ ∧ (∀ z, Φ z = 1 ↔ z ∈ Λ) ∧ Function.Surjective Φ := by
  unfold IsUniformization IsAnalyticHom
  tauto

theorem isAnalyticHom_of_unif {A : AbVar K} {σ : K →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → CPts A σ} (h : IsUniformization σ Λ Φ) :
    IsAnalyticHom σ Φ :=
  ((isUniformization_iff σ Λ Φ).1 h).1

theorem map_zero_of_hom {G : Type*} [Group G] {n : ℕ} {ψ : (Fin n → ℂ) → G}
    (h : ∀ z w, ψ (z + w) = ψ z * ψ w) : ψ 0 = 1 := by
  have h0 := h 0 0
  rw [add_zero] at h0
  exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)

theorem map_nsmul_of_hom {G : Type*} [Group G] {n : ℕ} {ψ : (Fin n → ℂ) → G}
    (h : ∀ z w, ψ (z + w) = ψ z * ψ w) (u : Fin n → ℂ) (k : ℕ) : ψ (k • u) = ψ u ^ k := by
  induction k with
  | zero => simp [map_zero_of_hom h]
  | succ k ih => rw [succ_nsmul, h, ih, pow_succ]

/-! ### Glue 1: algebraic homomorphisms preserve analyticity -/

theorem cEvalAt_comp {A B : AbVar K} {σ : K →+* ℂ} (p : CPts A σ) (f : A.X ⟶ B.X)
    (U : B.X.left.Opens) (s : Γ(B.X.left, U)) :
    cEvalAt (p ≫ f) U s = cEvalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold cEvalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · rw [dif_pos h, dif_pos (show ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h)]
    congr 1
  · rw [dif_neg h, dif_neg (show ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h)]

/-- **`Φ ≫ f` is analytic for an algebraic homomorphism `f` (proved).** This is the part
"algebraic morphisms are holomorphic" of `HomLinearLift`, at the level of the definitions. -/
theorem isAnalyticHom_comp {A B : AbVar K} {σ : K →+* ℂ} {n : ℕ}
    {ψ : (Fin n → ℂ) → CPts A σ} (hψ : IsAnalyticHom σ ψ) (f : A.X ⟶ B.X) [IsMonHom f] :
    IsAnalyticHom σ (fun z => ψ z ≫ f) := by
  refine ⟨fun z w => ?_, fun U => hψ.2.1 (f.left ⁻¹ᵁ U), fun U s => ?_⟩
  · show ψ (z + w) ≫ f = (ψ z ≫ f) * (ψ w ≫ f)
    rw [hψ.1 z w]
    exact MonObj.mul_comp _ _ _
  · have := hψ.2.2 (f.left ⁻¹ᵁ U) (f.left.app U s)
    simp only [← cEvalAt_comp] at this
    exact this

/-! ### Glue 2: lattice maps give analytic homomorphisms -/

/-- **`Φ ∘ M` is analytic for `ℂ`-linear `M` (proved).** -/
theorem isAnalyticHom_lin {B : AbVar K} {σ : K →+* ℂ} {g h : ℕ}
    {Φ : (Fin h → ℂ) → CPts B σ} (hΦ : IsAnalyticHom σ Φ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ)) :
    IsAnalyticHom σ (fun z => Φ (M z)) := by
  have hc : Continuous M := LinearMap.continuous_of_finiteDimensional M
  have hd : Differentiable ℂ (LinearMap.toContinuousLinearMap M) :=
    (LinearMap.toContinuousLinearMap M).differentiable
  refine ⟨fun z w => by simp only [map_add, hΦ.1], fun U => (hΦ.2.1 U).preimage hc,
    fun U s => ?_⟩
  exact (hΦ.2.2 U s).comp hd.differentiableOn (fun z hz => hz)

end Defs

/-! ### The narrow analytic statements -/

/-- **Analytic lifting (BL 1.2.1 transported; analytic leaf candidate).** Every analytic
homomorphism `ψ : ℂ^g → B(ℂ)_σ` factors through a uniformization `Φ_B` (`h = dim B`) by a
`ℂ`-linear map. -/
def AnalyticHomLift : Prop :=
  ∀ (K : Type) [Field K] (B : AbVar K) (σ : K →+* ℂ) (g h : ℕ) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦB : (Fin h → ℂ) → CPts B σ), B.dim = (h : WithBot ℕ∞) → IsUniformization σ ΛB ΦB →
    ∀ ψ : (Fin g → ℂ) → CPts B σ, IsAnalyticHom σ ψ →
      ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), ∀ z, ΦB (M z) = ψ z

/-- **A uniformization is a local analytic isomorphism at `0` (one-variety analytic leaf
candidate; Mumford §1: `Φ = exp ∘ D`, `D` a linear isomorphism, `exp` a local biholomorphism).**
For a uniformization `Φ` of `B(ℂ)_σ` with `h = dim B` there are an open `W ∋ 0` and a map
`χ : B(ℂ)_σ → ℂ^h` inverting `Φ` on `W`, such that for every analytic homomorphism `ψ` into
`B(ℂ)_σ`, `ψ` maps a neighbourhood of `0` into `Φ(W)` and `χ ∘ ψ` is holomorphic at `0`
("`Φ(W)` is a neighbourhood of the identity and `χ` is holomorphic on it", tested on analytic
homomorphisms, since `B(ℂ)_σ` carries no topology in Lean). -/
def UnifLocalInverse : Prop :=
  ∀ (K : Type) [Field K] (B : AbVar K) (σ : K →+* ℂ) (h : ℕ) (Λ : Submodule ℤ (Fin h → ℂ))
    (Φ : (Fin h → ℂ) → CPts B σ), B.dim = (h : WithBot ℕ∞) → IsUniformization σ Λ Φ →
    ∃ W : Set (Fin h → ℂ), IsOpen W ∧ (0 : Fin h → ℂ) ∈ W ∧ ∃ χ : CPts B σ → (Fin h → ℂ),
      (∀ w ∈ W, χ (Φ w) = w) ∧
      ∀ (g : ℕ) (ψ : (Fin g → ℂ) → CPts B σ), IsAnalyticHom σ ψ →
        (∀ᶠ z in 𝓝 0, ψ z ∈ Φ '' W) ∧ DifferentiableAt ℂ (fun z => χ (ψ z)) 0

/-- **GAGA for homomorphisms of complex abelian varieties (analytic leaf candidate; Serre GAGA /
Chow, with rigidity).** An analytic homomorphism `ψ : ℂ^g → B(ℂ)` that kills the lattice of a
uniformization `Φ_A` of `A(ℂ)` (`g = dim A`) is induced by an algebraic homomorphism `A → B`. -/
def AnalyticHomAlgebraic : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → IsUniformization (RingHom.id ℂ) ΛA ΦA →
    ∀ ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ), IsAnalyticHom (RingHom.id ℂ) ψ →
      (∀ z ∈ ΛA, ψ z = 1) →
      ∃ f : AbVar.Hom A B, ∀ z, ψ z = ΦA z ≫ f.hom

/-! ### Reductions -/

/-- **`HomLinearLift` from `AnalyticHomLift` (proved).** -/
theorem homLinearLift_of_analyticHomLift (H : AnalyticHomLift) : HomLinearLift := by
  intro K _ A B σ g h ΛA ΛB ΦA ΦB _ hB hUA hUB f
  exact H K B σ g h ΛB ΦB hB hUB (fun z => ΦA z ≫ f.hom)
    (isAnalyticHom_comp (isAnalyticHom_of_unif hUA) f.hom)

/-- **`HomRealize` from `AnalyticHomAlgebraic` (proved).** -/
theorem homRealize_of_analyticHomAlgebraic (H : AnalyticHomAlgebraic) : HomRealize := by
  intro A B g h ΛA ΛB ΦA ΦB hA _ hUA hUB M hM
  obtain ⟨f, hf⟩ := H A B g ΛA ΦA hA hUA (fun z => ΦB (M z))
    (isAnalyticHom_lin (isAnalyticHom_of_unif hUB) M) (fun z hz => (hUB.2.1 _).2 (hM z hz))
  exact ⟨f, hf⟩

/-- **`HomLatticeCorr` from the two analytic statements (proved).** -/
theorem homLatticeCorr_of_analytic (H1 : AnalyticHomLift) (H2 : AnalyticHomAlgebraic) :
    HomLatticeCorr :=
  ZInQ.HomUnify.corr_iff_lift_realize.2
    ⟨homLinearLift_of_analyticHomLift H1, homRealize_of_analyticHomAlgebraic H2⟩

theorem t11a_riemannEnd_of_analytic (H1 : AnalyticHomLift) (H2 : AnalyticHomAlgebraic) :
    ZInQ.LeafPush2.T11a_RiemannEnd :=
  ZInQ.HomUnify.t11a_riemannEnd_of_corr (homLatticeCorr_of_analytic H1 H2)

theorem t11aHom_of_analytic (H2 : AnalyticHomAlgebraic) : T11aHom :=
  ZInQ.HomUnify.t11aHom_of_realize (homRealize_of_analyticHomAlgebraic H2)

end ZInQ.HomLattice

#print axioms ZInQ.HomLattice.isUniformization_iff
#print axioms ZInQ.HomLattice.cEvalAt_comp
#print axioms ZInQ.HomLattice.isAnalyticHom_comp
#print axioms ZInQ.HomLattice.isAnalyticHom_lin
#print axioms ZInQ.HomLattice.homLinearLift_of_analyticHomLift
#print axioms ZInQ.HomLattice.homRealize_of_analyticHomAlgebraic
#print axioms ZInQ.HomLattice.homLatticeCorr_of_analytic
#print axioms ZInQ.HomLattice.t11a_riemannEnd_of_analytic
#print axioms ZInQ.HomLattice.t11aHom_of_analytic
