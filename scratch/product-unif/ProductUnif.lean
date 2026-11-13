import ZInQKernel.HDecomp.Faltings.Height
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # product-unif: `ProductUnifSplits` (S-an) proved; `ProductMetrizationOfProductUnif` (S-alg)

Task product-unif. Imports only the kernel module `ZInQKernel.HDecomp.Faltings.Height` and Mathlib
(no scratch import). No `sorry`, no `axiom`. See `docs/research/product-unif.md`.

* §0 Verbatim copy from `scratch/product-height/ProductHeight.lean` (namespace
  `ZInQ.ProductHeight`, same names): §5 `ptsProj`, `ptsProj_bijective`, `ptsEquiv`, `prodLattice`,
  `prodUnif`, `prodUnif_clauses` (lines 404-469), §6b `dom_comp` … `proj_analyticClauses`
  (lines 800-862), and the two glue Props `ProductUnifSplits`, `ProductMetrizationOfProductUnif`
  (lines 864-922), unchanged.
* §1 Elementary analysis (copied from `Analysis.lean`, Mathlib only).
* §2 Points of an affine open are determined by the values of its regular functions.
* §3 **`productUnifSplits : ProductUnifSplits`** (proved).
* §4 S-alg: reduction. -/

namespace ZInQ.ProductHeight

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings
open PkgI3 (AbVar)

/-! ## §0. Verbatim copy (from `scratch/product-height/ProductHeight.lean`) -/

section Points

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
  {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}

/-- The two projections on complex points, as one homomorphism. -/
noncomputable def ptsProj (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ →* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  (IsMonHom.monoidHom (e.hom ≫ fst _ _) (GroupModel.ptC τ)).prod
    (IsMonHom.monoidHom (e.hom ≫ snd _ _) (GroupModel.ptC τ))

theorem ptsProj_bijective (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : Function.Bijective (ptsProj e τ) := by
  constructor
  · intro p q hpq
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Prod.mk.injEq] at hpq
    rw [← cancel_mono e.hom]
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc] using hpq.1
    · simpa only [Category.assoc] using hpq.2
  · rintro ⟨a, b⟩
    refine ⟨lift a b ≫ e.inv, ?_⟩
    simp only [ptsProj, MonoidHom.prod_apply, IsMonHom.monoidHom_apply, Category.assoc,
      Iso.inv_hom_id_assoc, lift_fst, lift_snd]

/-- **`𝒢P(ℂ)_τ ≅ 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` as groups (proved).** -/
noncomputable def ptsEquiv (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] (τ : L →+* ℂ) : 𝒢P.Pts τ ≃* 𝒢₁.Pts τ × 𝒢₂.Pts τ :=
  MulEquiv.ofBijective (ptsProj e τ) (ptsProj_bijective e τ)

/-- The lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (LinearMap.funLeft ℤ ℂ (Fin.castAdd g₂)) ⊓
    Λ₂.comap (LinearMap.funLeft ℤ ℂ (Fin.natAdd g₁))

/-- The product uniformization `z ↦ (Φ₁(z₁), Φ₂(z₂))`. -/
noncomputable def prodUnif (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) : (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ := fun z =>
  (ptsEquiv e τ).symm (Φ₁ fun i => z (Fin.castAdd g₂ i), Φ₂ fun i => z (Fin.natAdd g₁ i))

/-- **The algebraic clauses of `IsAnalyticUniformization` for the product (proved).** -/
theorem prodUnif_clauses (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
    {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ}
    {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ} (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodUnif e Φ₁ Φ₂ (z + w) = prodUnif e Φ₁ Φ₂ z * prodUnif e Φ₁ Φ₂ w) ∧
    (∀ z, prodUnif e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodUnif e Φ₁ Φ₂) := by
  obtain ⟨m₁, k₁, s₁, -, -⟩ := h₁
  obtain ⟨m₂, k₂, s₂, -, -⟩ := h₂
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · simp only [prodUnif, ← map_mul, Prod.mk_mul_mk]
    congr 2
    · exact m₁ _ _
    · exact m₂ _ _
  · simp only [prodUnif, MulEquiv.map_eq_one_iff, Prod.mk_eq_one, k₁, k₂, prodLattice,
      Submodule.mem_inf, Submodule.mem_comap]
    rfl
  · obtain ⟨z₁, hz₁⟩ := s₁ (ptsEquiv e τ p).1
    obtain ⟨z₂, hz₂⟩ := s₂ (ptsEquiv e τ p).2
    refine ⟨Fin.append z₁ z₂, ?_⟩
    simp only [prodUnif, Fin.append_left, Fin.append_right, hz₁, hz₂, Prod.mk.eta,
      MulEquiv.symm_apply_apply]

end Points

section MorphComp

variable {K : Type} [Field K] {A B : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

theorem dom_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G) {τ : L →+* ℂ}
    {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒢'.G.left.Opens) :
    𝒢'.dom (fun z => Φ z ≫ f) U = 𝒢.dom Φ (f.left ⁻¹ᵁ U) := rfl

/-- **Values of regular functions along a morphism** (proved):
`s(f ∘ p) = (f* s)(p)`. -/
theorem evalAt_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G)
    {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢'.G.left.Opens) (s : Γ(𝒢'.G.left, U)) :
    𝒢'.evalAt (p ≫ f) U s = 𝒢.evalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · rw [dif_pos (show ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h), dif_pos h]
    congr 1
  · rw [dif_neg (show ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U from h), dif_neg h]

/-- **Clauses 4 and 5 transport along a morphism of `𝓞_L`-schemes** (proved). -/
theorem analyticClauses_comp (𝒢 : GroupModel A L) (𝒢' : GroupModel B L) (f : 𝒢.G ⟶ 𝒢'.G)
    {τ : L →+* ℂ} {g : ℕ} {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (ho : ∀ U, IsOpen (𝒢.dom Φ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U)) :
    (∀ U, IsOpen (𝒢'.dom (fun z => Φ z ≫ f) U)) ∧
    (∀ U (s : Γ(𝒢'.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢'.evalAt (Φ z ≫ f) U s)
      (𝒢'.dom (fun z => Φ z ≫ f) U)) := by
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [dom_comp]; exact ho _
  · rw [dom_comp]
    simp only [evalAt_comp]
    exact hd _ _

/-- **Clauses 4 and 5 transport along a `ℂ`-linear map** `ℓ : ℂ^{g'} → ℂ^g` (proved). -/
theorem analyticClauses_precomp (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g g' : ℕ}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (ℓ : (Fin g' → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (ho : ∀ U, IsOpen (𝒢.dom Φ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ z) U s) (𝒢.dom Φ U)) :
    (∀ U, IsOpen (𝒢.dom (fun z => Φ (ℓ z)) U)) ∧
    (∀ U (s : Γ(𝒢.G.left, U)), DifferentiableOn ℂ (fun z => 𝒢.evalAt (Φ (ℓ z)) U s)
      (𝒢.dom (fun z => Φ (ℓ z)) U)) := by
  let ℓ' : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ) := LinearMap.toContinuousLinearMap ℓ
  refine ⟨fun U => (ho U).preimage ℓ'.continuous, fun U s => ?_⟩
  exact (hd U s).comp ℓ'.differentiableOn (fun z hz => hz)

/-- **The analytic clauses of the factor uniformizations in S-an** (proved): for `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂`,
an analytic uniformization `Φ` of the product and any `ℂ`-linear `ℓ : ℂ^{g₁} → ℂ^g`, the map
`z ↦ p₁(Φ(ℓ z))` satisfies clauses 4 and 5 for `𝒢₁`. -/
theorem proj_analyticClauses {C : AbVar K} {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g g₁ : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢P.Pts τ} (hΦ : 𝒢P.IsAnalyticUniformization τ Λ Φ)
    (ℓ : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    (∀ U, IsOpen (𝒢₁.dom (fun z => (ptsEquiv e τ (Φ (ℓ z))).1) U)) ∧
    (∀ U (s : Γ(𝒢₁.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (ptsEquiv e τ (Φ (ℓ z))).1 U s)
        (𝒢₁.dom (fun z => (ptsEquiv e τ (Φ (ℓ z))).1) U)) := by
  obtain ⟨-, -, -, ho, hd⟩ := hΦ
  obtain ⟨ho', hd'⟩ := analyticClauses_precomp 𝒢P ℓ ho hd
  exact analyticClauses_comp 𝒢P 𝒢₁ (e.hom ≫ fst _ _) ho' hd'

end MorphComp

/-- **Glue S-an (splitting of a uniformization of a product; elementary analysis, no AN3).**
Let `e : 𝒢P ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components. Every analytic uniformization `Φ` of
`𝒢P(ℂ)_τ` with a full discrete lattice `Λ ⊂ ℂ^g` as kernel splits: for some `g₁ + g₂ = g`, full
discrete lattices `Λᵢ ⊂ ℂ^{gᵢ}`, analytic uniformizations `Φᵢ` of `𝒢ᵢ(ℂ)_τ` with kernels `Λᵢ` and a
`ℂ`-linear automorphism `T`, we have `Φ ∘ T = Φ₁ × Φ₂` (`prodUnif`, coordinates `Fin.append`).

Why true (STANDARD, argued in the section header; no uniformization theorem is used). The
ingredients are the structure of closed subgroups of `ℝⁿ` (Bourbaki, *Topologie générale* VII §1,
UNVERIFIED; small elements of a closed subgroup lie in its identity component), the identity
theorem in one complex variable, Baire's theorem, the fact that a `τ`-point of an affine open is
determined by its function values, and the compatibility of `evalAt` with the projections.
Then `Φᵢ = pᵢ ∘ Φ|_{Wᵢ}` with
`Wᵢ = ker(p_{3-i} ∘ Φ)⁰`, `Λᵢ = Λ ∩ Wᵢ`. Unproved. -/
def ProductUnifSplits : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (Φ : (Fin g → ℂ) → 𝒢P.Pts τ), IsZLattice ℝ Λ → 𝒢P.IsAnalyticUniformization τ Λ Φ →
    ∃ (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
      (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
      (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧ (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
      ∀ z, Φ (T z) = prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))

/-- **Glue S-alg (metrizations of the factors from a product-form metrization; Hodge theory, no
AN3).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components. Suppose that at every `τ` the
metrization `MP` of the product model is in product form: its period lattice is `Λ₁ × Λ₂` and its
coefficient map is computed by `Φ₁ × Φ₂`, for full discrete lattices `Λᵢ ⊂ ℂ^{gᵢ(τ)}` and analytic
uniformizations `Φᵢ` of the factors. Then the factors have metrizations `M₁`, `M₂` with
`h(M₁) + h(M₂) ≤ h(MP)`.

Why true (STANDARD; mirror image of `ProductMetrizationGeo`).
- `gᵢ(τ) = dim 𝒢ᵢ`: `MP.hodge.finrank_eq_one` gives `g ∈ {0, d₁ + d₂}` (if `g = 0`, the factors'
  complex points are trivial and `dᵢ = 0`); otherwise, with the algebraic splitting
  `cotangent_P = cotangent₁ ⊕ cotangent₂`, the wedge of `p₁*f, p₂*h` (bases) is nonzero, so
  `coeff ≠ 0` makes the block-shaped Jacobian of `Φ₁ × Φ₂` at `0` nonsingular.
- `ω_{MP} = ω₁ ⊕ ω₂` and `⋀^{top}ω_{MP} = ⋀ω₁ ⊗ ⋀ω₂`.
- `jacDet Φᵢ` descends to a semilinear map on `⋀^{gᵢ}`.
- Indices, coefficients and covolumes multiply (`modelHeight_add_of`); equality holds.

Unproved. -/
def ProductMetrizationOfProductUnif : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)],
    (∀ τ : L →+* ℂ, ∃ (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
        (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
        (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
        (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
        (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
        𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
        (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) ∧
        ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
          MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    ∃ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ ∧ M₂.model = 𝒢₂ ∧
      M₁.hodge.modelHeight + M₂.hodge.modelHeight ≤ MP.hodge.modelHeight

end ZInQ.ProductHeight

/-! ## §1. Elementary analysis (copied from `Analysis.lean`) -/

namespace ZInQ.ProductUnif

open Topology Filter MeasureTheory Metric

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real core `{v | ℝ v ⊆ H}` of an additive subgroup. -/
def rcore (H : AddSubgroup E) : Submodule ℝ E where
  carrier := {v | ∀ t : ℝ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_rcore {H : AddSubgroup E} {v : E} : v ∈ rcore H ↔ ∀ t : ℝ, t • v ∈ H := Iff.rfl

theorem rcore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ rcore H) : v ∈ H := by
  simpa using hv 1

variable [FiniteDimensional ℝ E]

/-- **Isolation in a complement of the real core.** -/
theorem exists_isolated (H : AddSubgroup E) (hH : IsClosed (H : Set E)) (W : Submodule ℝ E)
    (hW : rcore H ⊓ W = ⊥) : ∃ ε > 0, ∀ c ∈ H, c ∈ W → ‖c‖ < ε → c = 0 := by
  by_contra hne
  push Not at hne
  choose c hcH hcW hcn hc0 using fun n : ℕ => hne (1 / ((n : ℝ) + 1)) (by positivity)
  set u : ℕ → E := fun n => ‖c n‖⁻¹ • c n with hu_def
  have hu : ∀ n, u n ∈ sphere (0 : E) 1 := by
    intro n
    have : ‖c n‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 n)
    simp [u, norm_smul, this]
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu
  have hc_lim : Tendsto c atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hcn n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc_lim' : Tendsto (fun n => c (φ n)) atTop (𝓝 0) := hc_lim.comp hφ.tendsto_atTop
  have hvW : v ∈ W :=
    (W.closed_of_finiteDimensional).mem_of_tendsto hlim
      (Eventually.of_forall fun n => W.smul_mem _ (hcW _))
  have hvR : v ∈ rcore H := by
    intro t
    have h1 : Tendsto (fun n => t • u (φ n)) atTop (𝓝 (t • v)) := hlim.const_smul t
    have h2 : Tendsto (fun n => (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hc_lim'.norm)
      have ha : ‖c (φ n)‖ ≠ 0 := norm_ne_zero_iff.mpr (hc0 _)
      have : (⌊t / ‖c (φ n)‖⌋ : ℤ) • c (φ n) - t • u (φ n) =
          (((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖) • c (φ n) := by
        rw [sub_smul, ← Int.cast_smul_eq_zsmul ℝ, hu_def]
        simp only
        rw [smul_smul, div_eq_mul_inv]
      rw [this, norm_smul, Real.norm_eq_abs]
      have hfl : |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [Int.lt_floor_add_one (t / ‖c (φ n)‖)]
        · linarith [Int.floor_le (t / ‖c (φ n)‖)]
      calc |(((⌊t / ‖c (φ n)‖⌋ : ℤ) : ℝ) - t / ‖c (φ n)‖)| * ‖c (φ n)‖
          ≤ 1 * ‖c (φ n)‖ := mul_le_mul_of_nonneg_right hfl (norm_nonneg _)
        _ = ‖c (φ n)‖ := one_mul _
    have h3 := h1.add h2
    simp only [add_sub_cancel, add_zero] at h3
    exact hH.mem_of_tendsto h3 (Eventually.of_forall fun n => H.zsmul_mem (hcH _) _)
  have hv0 : v = 0 := by
    have : v ∈ rcore H ⊓ W := ⟨hvR, hvW⟩
    rw [hW] at this
    exact this
  simp [hv0] at hv

/-- **A closed subgroup is its real core plus a countable set.** -/
theorem exists_countable_add (H : AddSubgroup E) (hH : IsClosed (H : Set E)) :
    ∃ S : Set E, S.Countable ∧ ∀ h ∈ H, ∃ r ∈ rcore H, ∃ s ∈ S, h = r + s := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (rcore H)
  obtain ⟨ε, hε, hiso⟩ := exists_isolated H hH W hW.inf_eq_bot
  set S : Set E := {w | w ∈ H ∧ w ∈ W}
  have hsep : Pairwise fun x y : S => ε ≤ dist x y := by
    intro x y hxy
    by_contra hlt
    push Not at hlt
    apply hxy
    have h0 := hiso ((x : E) - y) (H.sub_mem x.2.1 y.2.1) (W.sub_mem x.2.2 y.2.2)
      (by rw [← dist_eq_norm]; exact hlt)
    exact Subtype.ext (sub_eq_zero.mp h0)
  have : DiscreteTopology S := DiscreteTopology.of_forall_le_dist hε hsep
  have : Countable S := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  refine ⟨S, Set.countable_coe_iff.mp inferInstance, fun h hh => ?_⟩
  have hmem : h ∈ rcore H ⊔ W := by rw [hW.sup_eq_top]; trivial
  obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hmem
  refine ⟨r, hr, w, ⟨?_, hw⟩, rfl⟩
  have : w = (r + w) - r := by abel
  rw [this]
  exact H.sub_mem hh (rcore_le_self hr)

variable [MeasurableSpace E] [BorelSpace E]

/-- **`H₁ + H₂ = E` forces `rcore H₁ ⊔ rcore H₂ = ⊤`** (a proper subspace is null). -/
theorem rcore_sup_eq_top (H₁ H₂ : AddSubgroup E) (h₁ : IsClosed (H₁ : Set E))
    (h₂ : IsClosed (H₂ : Set E)) (hs : ∀ x : E, ∃ a ∈ H₁, ∃ b ∈ H₂, a + b = x) :
    rcore H₁ ⊔ rcore H₂ = ⊤ := by
  by_contra hne
  obtain ⟨S₁, hS₁, hd₁⟩ := exists_countable_add H₁ h₁
  obtain ⟨S₂, hS₂, hd₂⟩ := exists_countable_add H₂ h₂
  set P := rcore H₁ ⊔ rcore H₂
  let μ : Measure E := Measure.addHaar
  have hP : μ (P : Set E) = 0 := Measure.addHaar_submodule μ P hne
  have : Countable S₁ := hS₁.to_subtype
  have : Countable S₂ := hS₂.to_subtype
  have hcov : (Set.univ : Set E) ⊆
      ⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E) := by
    intro x _
    obtain ⟨a, ha, b, hb, rfl⟩ := hs x
    obtain ⟨r₁, hr₁, s₁, hs₁, rfl⟩ := hd₁ a ha
    obtain ⟨r₂, hr₂, s₂, hs₂, rfl⟩ := hd₂ b hb
    refine Set.mem_iUnion.mpr ⟨(⟨s₁, hs₁⟩, ⟨s₂, hs₂⟩), ?_⟩
    show -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) ∈ P
    have : -(s₁ + s₂) + (r₁ + s₁ + (r₂ + s₂)) = r₁ + r₂ := by abel
    rw [this]
    exact P.add_mem (Submodule.mem_sup_left hr₁) (Submodule.mem_sup_right hr₂)
  have hnull : μ (⋃ p : S₁ × S₂, (fun x => -((p.1 : E) + p.2) + x) ⁻¹' (P : Set E)) = 0 := by
    refine measure_iUnion_null fun p => ?_
    rw [measure_preimage_add]
    exact hP
  have hu : μ Set.univ = 0 := measure_mono_null hcov hnull
  exact (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ)) hu

end Real

section Closed

variable {E : Type*} [NormedAddCommGroup E]

/-- **A subgroup cut out near `0` by functions continuous there is closed.** -/
theorem isClosed_of_local (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, ContinuousOn (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) : IsClosed (H : Set E) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hN 0 h0
  set ρ := r / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hcb : closedBall (0 : E) ρ ⊆ N :=
    (closedBall_subset_ball (by linarith)).trans hball
  have hC : IsClosed (closedBall (0 : E) ρ ∩ (H : Set E)) := by
    have : closedBall (0 : E) ρ ∩ (H : Set E) =
        closedBall (0 : E) ρ ∩ ⋂ i, (closedBall (0 : E) ρ ∩ F i ⁻¹' {F i 0}) := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hz, hzH⟩
        exact ⟨hz, fun i => ⟨hz, (hH z (hcb hz)).mp hzH i⟩⟩
      · rintro ⟨hz, hi⟩
        exact ⟨hz, (hH z (hcb hz)).mpr fun i => (hi i).2⟩
    rw [this]
    exact isClosed_closedBall.inter (isClosed_iInter fun i =>
      ((hF i).mono hcb).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
  rw [← closure_subset_iff_isClosed]
  intro x hx
  obtain ⟨h, hh, hxh⟩ := Metric.mem_closure_iff.mp hx ρ hρpos
  have hy : x - h ∈ closure (H : Set E) := by
    have hcl : x - h ∈ H.topologicalClosure :=
      H.topologicalClosure.sub_mem hx (H.le_topologicalClosure hh)
    exact hcl
  have hyb : x - h ∈ ball (0 : E) ρ := by
    rw [mem_ball, dist_zero_right, ← dist_eq_norm]
    exact hxh
  have hyC : x - h ∈ closedBall (0 : E) ρ ∩ (H : Set E) := by
    have := isOpen_ball.inter_closure ⟨hyb, hy⟩
    have hsub : closure (ball (0 : E) ρ ∩ (H : Set E)) ⊆ closedBall (0 : E) ρ ∩ (H : Set E) :=
      closure_minimal (Set.inter_subset_inter_left _ ball_subset_closedBall) hC
    exact hsub this
  have : x = (x - h) + h := by abel
  rw [this]
  exact H.add_mem hyC.2 hh

end Closed

section Complex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The complex core `{v | ℂ v ⊆ H}` of an additive subgroup. -/
def ccore (H : AddSubgroup E) : Submodule ℂ E where
  carrier := {v | ∀ t : ℂ, t • v ∈ H}
  add_mem' := by
    intro a b ha hb t
    rw [smul_add]
    exact H.add_mem (ha t) (hb t)
  zero_mem' := by
    intro t
    rw [smul_zero]
    exact H.zero_mem
  smul_mem' := by
    intro c a ha t
    rw [smul_smul]
    exact ha _

theorem mem_ccore {H : AddSubgroup E} {v : E} : v ∈ ccore H ↔ ∀ t : ℂ, t • v ∈ H := Iff.rfl

theorem ccore_le_self {H : AddSubgroup E} {v : E} (hv : v ∈ ccore H) : v ∈ H := by
  simpa using hv 1

/-- **Identity theorem step: the real core of a subgroup cut out near `0` by holomorphic
functions is complex.** -/
theorem rcore_le_ccore (H : AddSubgroup E) (N : Set E) (hN : IsOpen N) (h0 : (0 : E) ∈ N)
    {ι : Type*} (F : ι → E → ℂ) (hF : ∀ i, DifferentiableOn ℂ (F i) N)
    (hH : ∀ z ∈ N, z ∈ H ↔ ∀ i, F i z = F i 0) {w : E} (hw : w ∈ rcore H) : w ∈ ccore H := by
  have hcont : Continuous fun t : ℂ => t • w := continuous_id.smul continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hN.preimage hcont) 0 (by simpa using h0)
  have hreal : ∀ r : ℝ, ((r : ℂ) • w) ∈ H := by
    intro r
    have := hw r
    rwa [← Complex.coe_smul] at this
  have hsmall : ∀ t ∈ ball (0 : ℂ) δ, t • w ∈ H := by
    intro t ht
    refine (hH _ (hball ht)).mpr fun i => ?_
    have hd : DifferentiableOn ℂ (fun t : ℂ => F i (t • w)) (ball (0 : ℂ) δ) :=
      (hF i).comp (differentiable_id.smul_const w).differentiableOn (fun s hs => hball hs)
    have han := hd.analyticOnNhd isOpen_ball
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => F i 0) (ball (0 : ℂ) δ) :=
      analyticOnNhd_const
    have hfreq : ∃ᶠ s in 𝓝[≠] (0 : ℂ), F i (s • w) = F i 0 := by
      have htend : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
        · have := (Complex.continuous_ofReal.tendsto 0).comp
            tendsto_one_div_add_atTop_nhds_zero_nat
          simpa [Function.comp_def] using this
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
          positivity
      refine htend.frequently (Eventually.frequently ?_)
      have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)
      filter_upwards [hev] with n hn
      have hb : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ ball (0 : ℂ) δ := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        exact hn
      exact (hH _ (hball hb)).mp (hreal _) i
    exact han.eqOn_of_preconnected_of_frequently_eq hconst (convex_ball 0 δ).isPreconnected
      (mem_ball_self hδ) hfreq ht
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (‖t‖ / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have htn : t / n ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right, norm_div, Complex.norm_natCast]
    rw [div_lt_iff₀ hδ] at hn
    rw [div_lt_iff₀ hnpos]
    linarith
  have : t • w = n • ((t / n) • w) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_div_cancel₀ _ hn0]
  rw [this]
  exact H.nsmul_mem (hsmall _ htn) n

/-- **The real core of a discrete subgroup is `0`.** -/
theorem eq_zero_of_mem_rcore_discrete (Λ : AddSubgroup E) [DiscreteTopology Λ] {v : E}
    (hv : v ∈ rcore Λ) : v = 0 := by
  let f : ℝ → Λ := fun t => ⟨t • v, hv t⟩
  have hf : Continuous f := (continuous_id.smul continuous_const).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

end Complex

/-- **The real core of a discrete `ℤ`-lattice is `0`.** -/
theorem eq_zero_of_real_line_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    {v : Fin g → ℂ} (hv : ∀ t : ℝ, (t : ℂ) • v ∈ Λ) : v = 0 := by
  let f : ℝ → Λ := fun t => ⟨(t : ℂ) • v, hv t⟩
  have hf : Continuous f :=
    ((Complex.continuous_ofReal.smul continuous_const)).subtype_mk _
  have := PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0)
  simpa [f] using congrArg Subtype.val this

/-- The kernel of a function with `f (z + w) = f z * f w`, as an additive subgroup. -/
def kerSub {G : Type*} [Group G] {E : Type*} [AddGroup E] (f : E → G)
    (hf : ∀ z w, f (z + w) = f z * f w) : AddSubgroup E where
  carrier := {z | f z = 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [hf, ha, hb, mul_one]
  zero_mem' := by
    show f 0 = 1
    have h := hf 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h0 : f 0 = 1 := by
      have h := hf 0 0
      rw [add_zero] at h
      exact mul_left_cancel (h.symm.trans (mul_one _).symm)
    have h := hf (-a) a
    rw [neg_add_cancel, ha, mul_one, h0] at h
    exact h.symm

theorem mem_kerSub {G : Type*} [Group G] {E : Type*} [AddGroup E] {f : E → G}
    {hf : ∀ z w, f (z + w) = f z * f w} {z : E} : z ∈ kerSub f hf ↔ f z = 1 := Iff.rfl

theorem hom_zero {G : Type*} [Group G] {E : Type*} [AddGroup E] (f : E → G)
    (hf : ∀ z w, f (z + w) = f z * f w) : f 0 = 1 :=
  (kerSub f hf).zero_mem

/-! ## §2. Points of an affine open are determined by the values of its regular functions -/

section Pts

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Two complex points lying in an affine open `V` with the same values on `Γ(V)` are equal**
(proved: both factor as `Spec ℂ ≅ Spec Γ(Spec ℂ) → Spec Γ(V) → 𝒢`, by
`IsAffineOpen.SpecMap_appLE_fromSpec`). -/
theorem pts_eq_of_evalAt {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} {p q : 𝒢.Pts τ}
    {V : 𝒢.G.left.Opens} (hV : IsAffineOpen V) (hp : ⊤ ≤ p.left ⁻¹ᵁ V)
    (hq : ⊤ ≤ q.left ⁻¹ᵁ V) (h : ∀ s, 𝒢.evalAt p V s = 𝒢.evalAt q V s) : p = q := by
  let pl : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := p.left
  let ql : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q.left
  have hp2 : ⊤ ≤ pl ⁻¹ᵁ V := hp
  have hq2 : ⊤ ≤ ql ⁻¹ᵁ V := hq
  have heq : pl.appLE V ⊤ hp2 = ql.appLE V ⊤ hq2 := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have hp' := IsAffineOpen.SpecMap_appLE_fromSpec pl hV
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hp2
  have hq' := IsAffineOpen.SpecMap_appLE_fromSpec ql hV
    (isAffineOpen_top (Spec (CommRingCat.of ℂ))) hq2
  have hT : IsIso (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec := by
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have : (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec ≫ pl =
      (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec ≫ ql := by
    rw [← hp', ← hq', heq]
  exact Over.OverMorphism.ext
    ((IsIso.epi_of_iso (isAffineOpen_top (Spec (CommRingCat.of ℂ))).fromSpec).left_cancellation
      pl ql this)

/-- `Spec ℂ` has one point. -/
theorem top_le_preimage_of_mem {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    {V : 𝒢.G.left.Opens} (x₀ : (GroupModel.ptC (L := L) τ).left) (h : p.left x₀ ∈ V) :
    ⊤ ≤ p.left ⁻¹ᵁ V := by
  intro x _
  have : x = x₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) x x₀
  subst this
  exact h

/-- **The kernel of a holomorphic homomorphism into the complex points of a group model** is
closed, and its real core is complex (proved, from §1 and §2: near `0` it is cut out by the
regular functions of an affine open around the unit). -/
theorem kerSub_facts {A : AbVar K} (𝒢 : GroupModel A L) {τ : L →+* ℂ} {g : ℕ}
    (ψ : (Fin g → ℂ) → 𝒢.Pts τ) (hm : ∀ z w, ψ (z + w) = ψ z * ψ w)
    (ho : ∀ U, IsOpen (𝒢.dom ψ U))
    (hd : ∀ U (s : Γ(𝒢.G.left, U)),
      DifferentiableOn ℂ (fun z => 𝒢.evalAt (ψ z) U s) (𝒢.dom ψ U)) :
    IsClosed (kerSub ψ hm : Set (Fin g → ℂ)) ∧
      ∀ w ∈ rcore (kerSub ψ hm), w ∈ ccore (kerSub ψ hm) := by
  have h0 : ψ 0 = 1 := hom_zero ψ hm
  let x₀ : (GroupModel.ptC (L := L) τ).left := (default : PrimeSpectrum ℂ)
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := (ψ 0).left x₀) (U := ⊤) trivial
  have hN0 : (0 : Fin g → ℂ) ∈ 𝒢.dom ψ V := top_le_preimage_of_mem 𝒢 (ψ 0) x₀ hxV
  have hH : ∀ z ∈ 𝒢.dom ψ V, z ∈ kerSub ψ hm ↔
      ∀ s : Γ(𝒢.G.left, V), 𝒢.evalAt (ψ z) V s = 𝒢.evalAt (ψ 0) V s := by
    intro z hz
    constructor
    · intro hk s
      rw [show ψ z = ψ 0 from (mem_kerSub.mp hk).trans h0.symm]
    · intro hs
      show ψ z = 1
      rw [← h0]
      exact pts_eq_of_evalAt 𝒢 hV hz hN0 hs
  exact ⟨isClosed_of_local _ _ (ho V) hN0 (fun s z => 𝒢.evalAt (ψ z) V s)
      (fun s => (hd V s).continuousOn) hH,
    fun w hw => rcore_le_ccore _ _ (ho V) hN0 (fun s z => 𝒢.evalAt (ψ z) V s)
      (fun s => hd V s) hH hw⟩

end Pts

/-! ## §3. `ProductUnifSplits` (proved) -/

section Splits

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight
open PkgI3 (AbVar)

/-- `ℂ^{g₁+g₂} ≅ ℂ^{g₁} × ℂ^{g₂}` (`ℂ`-linear), `z ↦ (z ∘ castAdd, z ∘ natAdd)`. -/
def splitCE (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℂ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext i <;> simp

/-- **Glue S-an, proved.** -/
theorem productUnifSplits : ProductUnifSplits := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e _ _ τ g Λ _ Φ hZ hΦ
  have ⟨hm, hk, hs, ho, hd⟩ := hΦ
  -- the two components of `Φ`
  let ψ₁ : (Fin g → ℂ) → 𝒢₁.Pts τ := fun z => (ptsEquiv e τ (Φ z)).1
  let ψ₂ : (Fin g → ℂ) → 𝒢₂.Pts τ := fun z => (ptsEquiv e τ (Φ z)).2
  have hψm₁ : ∀ z w, ψ₁ (z + w) = ψ₁ z * ψ₁ w := by
    intro z w
    simp only [ψ₁, hm, map_mul, Prod.fst_mul]
  have hψm₂ : ∀ z w, ψ₂ (z + w) = ψ₂ z * ψ₂ w := by
    intro z w
    simp only [ψ₂, hm, map_mul, Prod.snd_mul]
  have hc₁ := proj_analyticClauses e hΦ (LinearMap.id : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
  have hc₂ := analyticClauses_comp 𝒢P 𝒢₂ (e.hom ≫ snd _ _) ho hd
  obtain ⟨hK₁c, hK₁r⟩ := kerSub_facts 𝒢₁ ψ₁ hψm₁ hc₁.1 hc₁.2
  obtain ⟨hK₂c, hK₂r⟩ := kerSub_facts 𝒢₂ ψ₂ hψm₂ hc₂.1 hc₂.2
  set K₁ := kerSub ψ₁ hψm₁ with hK₁
  set K₂ := kerSub ψ₂ hψm₂ with hK₂
  have hΛ : ∀ z, z ∈ Λ ↔ ψ₁ z = 1 ∧ ψ₂ z = 1 := by
    intro z
    rw [← hk]
    constructor
    · intro h
      simp [ψ₁, ψ₂, h]
    · rintro ⟨h1, h2⟩
      apply (ptsEquiv e τ).injective
      rw [map_one]
      exact Prod.ext h1 h2
  -- `K₁ + K₂ = ℂ^g`
  have hsum : ∀ x, ∃ a ∈ K₁, ∃ b ∈ K₂, a + b = x := by
    intro x
    obtain ⟨a, ha⟩ := hs ((ptsEquiv e τ).symm (1, ψ₂ x))
    have ha1 : ψ₁ a = 1 := by simp [ψ₁, ha]
    have ha2 : ψ₂ a = ψ₂ x := by simp [ψ₂, ha]
    refine ⟨a, ha1, x - a, ?_, by abel⟩
    show ψ₂ (x - a) = 1
    have := hψm₂ (x - a) a
    rw [sub_add_cancel, ha2] at this
    exact mul_right_cancel (this.symm.trans (_root_.one_mul _).symm)
  have hR : rcore K₁ ⊔ rcore K₂ = ⊤ := rcore_sup_eq_top K₁ K₂ hK₁c hK₂c hsum
  -- the complex subspaces `V₁ = ccore K₂`, `V₂ = ccore K₁`
  set V₁ := ccore K₂ with hV₁
  set V₂ := ccore K₁ with hV₂
  have hcompl : IsCompl V₁ V₂ := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hv1 hv2
      refine eq_zero_of_real_line_mem Λ fun t => ?_
      exact (hΛ _).mpr ⟨hv2 (t : ℂ), hv1 (t : ℂ)⟩
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : x ∈ rcore K₁ ⊔ rcore K₂ := by rw [hR]; trivial
      obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Submodule.mem_sup.mp hx
      rw [add_comm]
      exact Submodule.add_mem_sup (hK₂r r₂ hr₂) (hK₁r r₁ hr₁)
  -- dimensions and coordinates
  set g₁ := Module.finrank ℂ V₁ with hg₁
  set g₂ := Module.finrank ℂ V₂ with hg₂
  have hg : g₁ + g₂ = g := by
    rw [hg₁, hg₂, Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  let b₁ : V₁ ≃ₗ[ℂ] (Fin g₁ → ℂ) := (Module.finBasis ℂ V₁).equivFun
  let b₂ : V₂ ≃ₗ[ℂ] (Fin g₂ → ℂ) := (Module.finBasis ℂ V₂).equivFun
  let ι₁ : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g → ℂ) := V₁.subtype ∘ₗ b₁.symm.toLinearMap
  let ι₂ : (Fin g₂ → ℂ) →ₗ[ℂ] (Fin g → ℂ) := V₂.subtype ∘ₗ b₂.symm.toLinearMap
  let cE := Submodule.prodEquivOfIsCompl V₁ V₂ hcompl
  let π₁ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
    b₁.toLinearMap ∘ₗ LinearMap.fst ℂ V₁ V₂ ∘ₗ cE.symm.toLinearMap
  let π₂ : (Fin g → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
    b₂.toLinearMap ∘ₗ LinearMap.snd ℂ V₁ V₂ ∘ₗ cE.symm.toLinearMap
  have key₁ : ∀ z, ψ₂ (ι₁ z) = 1 := fun z => ccore_le_self (b₁.symm z).2
  have key₂ : ∀ z, ψ₁ (ι₂ z) = 1 := fun z => ccore_le_self (b₂.symm z).2
  have dec : ∀ y, y = ι₁ (π₁ y) + ι₂ (π₂ y) := by
    intro y
    have h1 := Submodule.coe_prodEquivOfIsCompl' V₁ V₂ hcompl (cE.symm y)
    have h2 : cE (cE.symm y) = y := cE.apply_symm_apply y
    calc y = cE (cE.symm y) := h2.symm
      _ = ↑(cE.symm y).1 + ↑(cE.symm y).2 := h1
      _ = ι₁ (π₁ y) + ι₂ (π₂ y) := by simp [ι₁, ι₂, π₁, π₂]
  have hπ₁ : ∀ x, π₁ (ι₁ x) = x := by
    intro x
    simp [π₁, ι₁, cE]
  have hπ₂ : ∀ x, π₂ (ι₂ x) = x := by
    intro x
    simp [π₂, ι₂, cE]
  -- the factor uniformizations and lattices
  let Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ := fun z => ψ₁ (ι₁ z)
  let Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ := fun z => ψ₂ (ι₂ z)
  let Λ₁ : Submodule ℤ (Fin g₁ → ℂ) := ZLattice.comap ℝ Λ (ι₁.restrictScalars ℝ)
  let Λ₂ : Submodule ℤ (Fin g₂ → ℂ) := ZLattice.comap ℝ Λ (ι₂.restrictScalars ℝ)
  have hΛ₁ : ∀ z, z ∈ Λ₁ ↔ ι₁ z ∈ Λ := fun z => Iff.rfl
  have hΛ₂ : ∀ z, z ∈ Λ₂ ↔ ι₂ z ∈ Λ := fun z => Iff.rfl
  have hπΛ₁ : ∀ l ∈ Λ, π₁ l ∈ Λ₁ := by
    intro l hl
    rw [hΛ₁, hΛ]
    refine ⟨?_, key₁ _⟩
    have h1 : ψ₁ (ι₁ (π₁ l) + ι₂ (π₂ l)) = 1 := by rw [← dec l]; exact ((hΛ l).mp hl).1
    rwa [hψm₁, key₂, _root_.mul_one] at h1
  have hπΛ₂ : ∀ l ∈ Λ, π₂ l ∈ Λ₂ := by
    intro l hl
    rw [hΛ₂, hΛ]
    refine ⟨key₂ _, ?_⟩
    have h1 : ψ₂ (ι₁ (π₁ l) + ι₂ (π₂ l)) = 1 := by rw [← dec l]; exact ((hΛ l).mp hl).2
    rwa [hψm₂, key₁, _root_.one_mul] at h1
  have hdisc₁ : DiscreteTopology Λ₁ :=
    ZLattice.comap_discreteTopology ℝ Λ (LinearMap.continuous_of_finiteDimensional _)
      (Subtype.val_injective.comp b₁.symm.injective)
  have hdisc₂ : DiscreteTopology Λ₂ :=
    ZLattice.comap_discreteTopology ℝ Λ (LinearMap.continuous_of_finiteDimensional _)
      (Subtype.val_injective.comp b₂.symm.injective)
  have hspan : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ := IsZLattice.span_top
  have hfull₁ : IsZLattice ℝ Λ₁ := by
    refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
    have hy : ι₁ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    have hmap : Submodule.map (π₁.restrictScalars ℝ) (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) ≤
        Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ)) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨l, hl, rfl⟩
      exact hπΛ₁ l hl
    rw [← hπ₁ x]
    exact hmap ⟨ι₁ x, hy, rfl⟩
  have hfull₂ : IsZLattice ℝ Λ₂ := by
    refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
    have hy : ι₂ x ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := by rw [hspan]; trivial
    have hmap : Submodule.map (π₂.restrictScalars ℝ) (Submodule.span ℝ (Λ : Set (Fin g → ℂ))) ≤
        Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ)) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨l, hl, rfl⟩
      exact hπΛ₂ l hl
    rw [← hπ₂ x]
    exact hmap ⟨ι₂ x, hy, rfl⟩
  have hu₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ := by
    have hcl := proj_analyticClauses e hΦ ι₁
    refine ⟨fun z w => ?_, fun z => ?_, fun a => ?_, hcl.1, hcl.2⟩
    · show ψ₁ (ι₁ (z + w)) = ψ₁ (ι₁ z) * ψ₁ (ι₁ w)
      rw [map_add, hψm₁]
    · rw [hΛ₁, hΛ]
      exact ⟨fun h => ⟨h, key₁ z⟩, fun h => h.1⟩
    · obtain ⟨y, hy⟩ := hs ((ptsEquiv e τ).symm (a, 1))
      have h1 : ψ₁ y = a := by simp [ψ₁, hy]
      refine ⟨π₁ y, ?_⟩
      show ψ₁ (ι₁ (π₁ y)) = a
      rw [dec y, hψm₁, key₂, _root_.mul_one] at h1
      exact h1
  have hu₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ := by
    have hcl := analyticClauses_comp 𝒢P 𝒢₂ (e.hom ≫ snd _ _)
      (analyticClauses_precomp 𝒢P ι₂ ho hd).1 (analyticClauses_precomp 𝒢P ι₂ ho hd).2
    refine ⟨fun z w => ?_, fun z => ?_, fun b => ?_, hcl.1, hcl.2⟩
    · show ψ₂ (ι₂ (z + w)) = ψ₂ (ι₂ z) * ψ₂ (ι₂ w)
      rw [map_add, hψm₂]
    · rw [hΛ₂, hΛ]
      exact ⟨fun h => ⟨key₂ z, h⟩, fun h => h.2⟩
    · obtain ⟨y, hy⟩ := hs ((ptsEquiv e τ).symm (1, b))
      have h1 : ψ₂ y = b := by simp [ψ₂, hy]
      refine ⟨π₂ y, ?_⟩
      show ψ₂ (ι₂ (π₂ y)) = b
      rw [dec y, hψm₂, key₁, _root_.one_mul] at h1
      exact h1
  -- the linear change of coordinates
  let T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (finCongr hg) ≪≫ₗ splitCE g₁ g₂ ≪≫ₗ
      (b₁.symm.prodCongr b₂.symm) ≪≫ₗ cE
  have hT : ∀ z, T z = ι₁ (fun i => z (Fin.cast hg (Fin.castAdd g₂ i))) +
      ι₂ (fun i => z (Fin.cast hg (Fin.natAdd g₁ i))) := by
    intro z
    show cE _ = _
    rw [Submodule.coe_prodEquivOfIsCompl']
    rfl
  refine ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, T, ⟨hdisc₁, hfull₁⟩, ⟨hdisc₂, hfull₂⟩, hu₁, hu₂,
    fun z => ?_⟩
  rw [hT z]
  unfold prodUnif
  rw [MulEquiv.eq_symm_apply]
  apply Prod.ext
  · show ψ₁ (ι₁ _ + ι₂ _) = Φ₁ _
    rw [hψm₁, key₂, _root_.mul_one]
  · show ψ₂ (ι₁ _ + ι₂ _) = Φ₂ _
    rw [hψm₂, key₁, _root_.one_mul]

end Splits

end ZInQ.ProductUnif

#print axioms ZInQ.ProductUnif.pts_eq_of_evalAt
#print axioms ZInQ.ProductUnif.kerSub_facts
#print axioms ZInQ.ProductUnif.productUnifSplits
