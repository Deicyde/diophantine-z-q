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
  (lines 864-922), `modelHeight_add_of` (lines 242-287) and §5b (lines 525-701), unchanged.
* §1 Elementary analysis (copied from `Analysis.lean`, Mathlib only).
* §2 Points of an affine open are determined by the values of its regular functions.
* §3 **`productUnifSplits : ProductUnifSplits`** (proved).
* §3b metrization's `jacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of`
  (copied from `ProdJac.lean`, itself verbatim from `scratch/metrization/`).
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


/-! Further verbatim copies from `scratch/product-height/ProductHeight.lean`: lines 242-287
(`modelHeight_add_of`) and 525-701 (§5b, product lattice), then `end LatticeProd`. -/

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (copied from g0-heightadd, proved).** If the Hodge data `D`
(dimension `g₁ + g₂`) has a nonzero section `s` whose lattice index, coefficients and period
covolumes are the products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)`. -/
theorem modelHeight_add_of {g₁ g₂ : ℕ} (D : HodgeData K (g₁ + g₂) V) (D₁ : HodgeData K g₁ V₁)
    (D₂ : HodgeData K g₂ V₂) {s : V} {s₁ : V₁} {s₂ : V₂} (hs : s ∈ D.lattice) (hs0 : s ≠ 0)
    (hs₁ : s₁ ∈ D₁.lattice) (hs₁0 : s₁ ≠ 0) (hs₂ : s₂ ∈ D₂.lattice) (hs₂0 : s₂ ≠ 0)
    (hidx : secIndex D.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂)
    (hcoeff : ∀ σ, D.coeff σ s = D₁.coeff σ s₁ * D₂.coeff σ s₂)
    (hcov : ∀ σ, ZLattice.covolume (D.periods σ) =
      ZLattice.covolume (D₁.periods σ) * ZLattice.covolume (D₂.periods σ)) :
    D.modelHeight = D₁.modelHeight + D₂.modelHeight := by
  rw [D.modelHeight_eq hs hs0, D₁.modelHeight_eq hs₁ hs₁0, D₂.modelHeight_eq hs₂ hs₂0]
  have ht : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ s) =
      torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁) *
        torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂) := by
    intro σ
    simp only [torusMetricSq, hcoeff σ, hcov σ, norm_mul]
    ring
  have hlog : ∀ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ s)) =
      Real.log (torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁)) +
        Real.log (torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂)) := by
    intro σ
    rw [ht σ]
    have := D₁.periods_discrete σ
    have := D₁.periods_isZLattice σ
    have := D₂.periods_discrete σ
    have := D₂.periods_isZLattice σ
    exact Real.log_mul (torusMetricSq_pos _ (D₁.coeff_apply_ne_zero σ hs₁0)).ne'
      (torusMetricSq_pos _ (D₂.coeff_apply_ne_zero σ hs₂0)).ne'
  have hi₁ : (secIndex D₁.lattice s₁ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₁.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
  have hi₂ : (secIndex D₂.lattice s₂ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₂.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)
  rw [hidx, Nat.cast_mul, Real.log_mul hi₁ hi₂, Finset.sum_congr rfl (fun σ _ => hlog σ),
    Finset.sum_add_distrib]
  ring

end HodgeAdd

/-! ## §5b. The product lattice (copied from `Lattice.lean`, which compiles standalone)

`Λ₁ × Λ₂` is a full discrete lattice with `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`
(`prodLattice_facts`, proved): the covolume clause of `ProductMetrizationGeo` and of S-alg for
the product lattice. -/

section LatticeProd

open Module ZSpan

section LatticeGeneral

variable {E₁ E₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁]
  [BorelSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂]
  [BorelSpace E₂]
  (Λ₁ : Submodule ℤ E₁) (Λ₂ : Submodule ℤ E₂)

omit [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂] [MeasurableSpace E₂] [BorelSpace E₂] in
theorem discreteTopology_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) := by
  let f : Λ₁.prod Λ₂ → Λ₁ × Λ₂ := fun x =>
    (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  have hf : Continuous f := by
    refine Continuous.prodMk ?_ ?_
    · exact (continuous_fst.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_snd.comp continuous_subtype_val).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  rw [discreteTopology_iff_isOpen_singleton]
  intro x
  have : ({x} : Set (Λ₁.prod Λ₂)) = f ⁻¹' {f x} := by
    ext y
    simp only [Set.mem_singleton_iff, Set.mem_preimage, hinj.eq_iff]
  rw [this]
  exact (isOpen_discrete _).preimage hf

instance instDiscreteTopologyProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] :
    DiscreteTopology (Λ₁.prod Λ₂) :=
  discreteTopology_prod Λ₁ Λ₂

instance instIsZLatticeProd [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] : IsZLattice ℝ (Λ₁.prod Λ₂) := by
  refine ⟨?_⟩
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  have hx : x ∈ Submodule.span ℝ (Λ₁ : Set E₁) := by rw [IsZLattice.span_top]; trivial
  have hy : y ∈ Submodule.span ℝ (Λ₂ : Set E₂) := by rw [IsZLattice.span_top]; trivial
  have h1 : Submodule.map (LinearMap.inl ℝ E₁ E₂) (Submodule.span ℝ (Λ₁ : Set E₁)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨ha, Λ₂.zero_mem⟩
  have h2 : Submodule.map (LinearMap.inr ℝ E₁ E₂) (Submodule.span ℝ (Λ₂ : Set E₂)) ≤
      Submodule.span ℝ ((Λ₁.prod Λ₂ : Submodule ℤ (E₁ × E₂)) : Set (E₁ × E₂)) := by
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_prod.mpr ⟨Λ₁.zero_mem, ha⟩
  have : ((x, y) : E₁ × E₂) = LinearMap.inl ℝ E₁ E₂ x + LinearMap.inr ℝ E₁ E₂ y := by simp
  rw [this]
  exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩)

/-- Unique translates into the fundamental domain of a basis, for the lattice itself. -/
theorem exists_unique_add_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {κ : Type*} [Fintype κ] (b : Basis κ ℤ L) (x : E) :
    ∃! l : L, (l : E) + x ∈ fundamentalDomain (b.ofZLatticeBasis ℝ) := by
  have hs := b.ofZLatticeBasis_span ℝ
  obtain ⟨v, hv, hu⟩ := exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) x
  refine ⟨⟨v, hs.le v.2⟩, hv, fun l hl => ?_⟩
  have := hu ⟨l, hs.ge l.2⟩ hl
  have h : ((⟨(l : E), hs.ge l.2⟩ : Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ))) : E) =
      (v : E) := congrArg Subtype.val this
  exact Subtype.ext h

theorem isAddFundamentalDomain_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂]
    [IsZLattice ℝ Λ₁] [IsZLattice ℝ Λ₂] {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    (b₁ : Basis κ₁ ℤ Λ₁) (b₂ : Basis κ₂ ℤ Λ₂) (μ₁ : Measure E₁) (μ₂ : Measure E₂) :
    IsAddFundamentalDomain (Λ₁.prod Λ₂)
      (fundamentalDomain (b₁.ofZLatticeBasis ℝ) ×ˢ fundamentalDomain (b₂.ofZLatticeBasis ℝ))
      (μ₁.prod μ₂) := by
  refine IsAddFundamentalDomain.mk' (((fundamentalDomain_measurableSet _).prod
    (fundamentalDomain_measurableSet _)).nullMeasurableSet) fun x => ?_
  obtain ⟨l₁, h₁, u₁⟩ := exists_unique_add_mem Λ₁ b₁ x.1
  obtain ⟨l₂, h₂, u₂⟩ := exists_unique_add_mem Λ₂ b₂ x.2
  refine ⟨⟨((l₁ : E₁), (l₂ : E₂)), Submodule.mem_prod.mpr ⟨l₁.2, l₂.2⟩⟩, ⟨h₁, h₂⟩, ?_⟩
  rintro ⟨⟨y₁, y₂⟩, hy⟩ hm
  obtain ⟨hm₁, hm₂⟩ := hm
  have e1 := u₁ ⟨y₁, (Submodule.mem_prod.mp hy).1⟩ hm₁
  have e2 := u₂ ⟨y₂, (Submodule.mem_prod.mp hy).2⟩ hm₂
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)

/-- **`covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`** (proved). -/
theorem covolume_prod [DiscreteTopology Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₁]
    [IsZLattice ℝ Λ₂] (μ₁ : Measure E₁) (μ₂ : Measure E₂) [μ₁.IsAddHaarMeasure]
    [μ₂.IsAddHaarMeasure] :
    ZLattice.covolume (Λ₁.prod Λ₂) (μ₁.prod μ₂) =
      ZLattice.covolume Λ₁ μ₁ * ZLattice.covolume Λ₂ μ₂ := by
  let b₁ := Free.chooseBasis ℤ Λ₁
  let b₂ := Free.chooseBasis ℤ Λ₂
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (Λ₁.prod Λ₂) (μ₁.prod μ₂)
      (isAddFundamentalDomain_prod Λ₁ Λ₂ b₁ b₂ μ₁ μ₂),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₁ μ₁ (ZLattice.isAddFundamentalDomain b₁ μ₁),
    ZLattice.covolume_eq_measure_fundamentalDomain Λ₂ μ₂ (ZLattice.isAddFundamentalDomain b₂ μ₂),
    measureReal_def, measureReal_def, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]

end LatticeGeneral

section LatticeSplit

/-- `ℂ^{g₁+g₂} ≅ ℂ^{g₁} × ℂ^{g₂}`, `z ↦ (z ∘ castAdd, z ∘ natAdd)`. -/
def splitLE (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i))
  invFun p := Fin.append p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv p := by ext i <;> simp

/-- The continuous version. -/
noncomputable def splitCL (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) ≃L[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) :=
  (splitLE g₁ g₂).toContinuousLinearEquiv

theorem splitCL_apply (g₁ g₂ : ℕ) (z : Fin (g₁ + g₂) → ℂ) :
    splitCL g₁ g₂ z = (fun i => z (Fin.castAdd g₂ i), fun i => z (Fin.natAdd g₁ i)) := rfl

theorem splitCL_measurePreserving (g₁ g₂ : ℕ) :
    MeasurePreserving (splitCL g₁ g₂) volume volume := by
  have h1 := MeasurePreserving.symm _
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (g₁ + g₂) => ℂ) finSumFinEquiv)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
  have h := h2.comp h1
  convert h using 1
  funext z
  rw [splitCL_apply]
  ext i
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inl i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_left]
  · simp only [Function.comp_apply, MeasurableEquiv.coe_sumPiEquivProdPi,
      Equiv.sumPiEquivProdPi_apply]
    show z _ = (Equiv.piCongrLeft (fun _ => ℂ) finSumFinEquiv).symm z (Sum.inr i)
    rw [Equiv.piCongrLeft_symm_apply, finSumFinEquiv_apply_right]

theorem prodLattice_eq_comap {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZLattice.comap ℝ (Λ₁.prod Λ₂) (splitCL g₁ g₂).toLinearMap := by
  ext z
  simp only [prodLattice, Submodule.mem_inf, Submodule.mem_comap]
  rfl

/-- **The product lattice is a full discrete lattice with `covol = covol Λ₁ · covol Λ₂`**
(proved). -/
theorem prodLattice_facts {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁] [IsZLattice ℝ Λ₁]
    [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂] :
    ∃ _ : DiscreteTopology (prodLattice Λ₁ Λ₂), IsZLattice ℝ (prodLattice Λ₁ Λ₂) ∧
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  have h01 : (volume : Measure (Fin g₁ → ℂ)).IsAddHaarMeasure := inferInstance
  have h02 : (volume : Measure (Fin g₂ → ℂ)).IsAddHaarMeasure := inferInstance
  have : (volume : Measure ((Fin g₁ → ℂ) × (Fin g₂ → ℂ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin g₁ → ℂ))
      (volume : Measure (Fin g₂ → ℂ))
  rw [prodLattice_eq_comap]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_comap (Λ₁.prod Λ₂) volume volume (splitCL_measurePreserving g₁ g₂)]
  exact covolume_prod Λ₁ Λ₂ volume volume

end LatticeSplit

end LatticeProd

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

/-! ## §3b. metrization's `JacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of`, on the kernel's types

Verbatim copies (only `open PkgI3 (AbVar)` added after each `open … DefFaltings …` line, and
`#print` lines dropped) from `scratch/metrization/`: `part_exists.lean` lines 30-43 (the Prop
`ZInQ.Metrization.JacDetDescends`), `part_jacdet.lean` lines 1-138, `part_jacgerm.lean`,
`part_jacscalar.lean`, `part_jacclass.lean` lines 1-139. There they are stated over the
def-faltings copy in `scratch/metrization/Base.lean`; here over the kernel's `DefFaltings`
(`ZInQKernel/HDecomp/Faltings/Models.lean`, adopted from def-faltings). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)
open PkgI3 (AbVar)

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

end ZInQ.Metrization


/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- **Glue (calculus of `jacDet`).** For an analytic uniformization `Φ` of `𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` on `g`-tuples of germs in `𝔪_ξ`
(i) depends only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`;
(ii) is additive in each slot;
(iii) scales by `τ(a)` when slot `i` is multiplied by the image of `a ∈ 𝓞_L`;
(iv) vanishes when two slots are equal.
Why true: `Φ 0 = 1` lies over `ξ`, and `dom Φ U` is open, so the germ at `0` of `f ∘ Φ` does not
depend on the representative of `f`, and `(f + f') ∘ Φ = f ∘ Φ + f' ∘ Φ`, `(ff') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)`
and `a ∘ Φ = τ(a)` near `0` (evaluation at a complex point is a ring map); for `f, f' ∈ 𝔪_ξ`,
`f ∘ Φ` and `f' ∘ Φ` vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz), which gives (i); (ii)-(iv)
are row operations on the determinant. Elementary, unproved (needs the compatibility of
`evalAt` with restriction, sums, products and stalks in Mathlib's scheme API). -/
def JacDetMultilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
      (x y : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (x + y)) =
        𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g), f i = f j → i ≠ j →
      𝒢.jacDet Φ f = 0)

/-- **`JacDetDescends` from `JacDetMultilinear` (proved).** -/
theorem jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨hcls, hadd, hsmul, halt⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  classical
  letI : Module (𝓞 L) ℂ := Module.compHom ℂ (τ.comp (algebraMap (𝓞 L) L))
  have hsm : ∀ (a : 𝓞 L) (z : ℂ), a • z = τ (algebraMap (𝓞 L) L a) * z := fun _ _ => rfl
  let lift : 𝒢.cotangent → IsLocalRing.maximalIdeal 𝒢.genStalk :=
    Function.surjInv (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective
  have hlift : ∀ v, 𝒢.dCls (lift v) = v := fun v =>
    Function.surjInv_eq (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  have hdadd : ∀ x y, 𝒢.dCls (x + y) = 𝒢.dCls x + 𝒢.dCls y := fun x y =>
    map_add (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent x y
  have hdsmul : ∀ (a : 𝓞 L) x, 𝒢.dCls (𝒢.structMap a • x) = a • 𝒢.dCls x := fun a x =>
    map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (𝒢.structMap a) x
  let ψ : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => 𝒢.jacDet Φ (fun i => lift (v i))
      map_update_add' := by
        intro _ v i x y
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x + lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdadd]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have e2 : 𝒢.jacDet Φ (fun j => lift (Function.update v i y j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
          𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) +
            𝒢.jacDet Φ (fun j => lift (Function.update v i y j))
        rw [e0, e1, e2]
        convert hadd (fun j => lift (v j)) i (lift x) (lift y)
      map_update_smul' := by
        intro _ v i a x
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (𝒢.structMap a • lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdsmul]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
          a • 𝒢.jacDet Φ (fun j => lift (Function.update v i x j))
        rw [e0, e1, hsm]
        convert hsmul (fun j => lift (v j)) i a (lift x)
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact halt (fun k => lift (v k)) i j (by simp only [hv]) hij }
  let Ψ : ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ := exteriorPower.alternatingMapLinearEquiv ψ
  let B : L →ₗ[𝓞 L] ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    LinearMap.mk₂ (𝓞 L) (fun x w => τ x * Ψ w)
      (fun x y w => by rw [map_add, add_mul])
      (fun a x w => by
        rw [hsm, Algebra.smul_def, map_mul, _root_.mul_assoc])
      (fun x w w' => by rw [map_add, mul_add])
      (fun a x w => by
        rw [map_smul, hsm, hsm, mul_left_comm])
  let T : 𝒢.hodgeSpace g →ₗ[𝓞 L] ℂ := TensorProduct.lift B
  have hT : ∀ x w, T (x ⊗ₜ[𝓞 L] w) = τ x * Ψ w := fun x w => rfl
  let c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro y t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
          rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, map_mul, _root_.mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, mul_add] }
  refine ⟨c, fun f => ?_⟩
  show T ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))) = 𝒢.jacDet Φ f
  rw [hT, map_one, _root_.one_mul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hcls _ _ fun i => hlift _

end ZInQ.Metrization


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization



/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization



/-! ## metrization: clause (i) of `JacDetMultilinear` (class invariance), proved

So `JacDetMultilinear`, hence `JacDetDescends`, is a theorem. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section ClassInv

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A section whose germ at `ξ` lies in `𝔪_ξ` vanishes at the identity complex point. -/
theorem evalAt_one_eq_zero {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  set q := (1 : 𝒢.Pts τ).left with hqdef
  have hq : ∀ x, q x = 𝒢.genericUnit := fun x => by
    rw [hqdef]
    erw [one_left_apply]
  have h : ⊤ ≤ q ⁻¹ᵁ U := by
    intro x _
    show q x ∈ U
    rw [hq]
    exact m
  unfold GroupModel.evalAt
  rw [dif_pos h]
  let q' : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q
  have h' : ⊤ ≤ q' ⁻¹ᵁ U := h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q'.appLE U ⊤ h' s) = 0
  let x : Spec (CommRingCat.of ℂ) := genericPoint (Spec (CommRingCat.of ℂ))
  have hxt : x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := by simp
  have hx : q' x ∈ U := h' hxt
  have key : q'.appLE U ⊤ h' ≫ (Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt =
      𝒢.G.left.presheaf.germ U (q' x) hx ≫ q'.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [TopCat.Presheaf.germ_res]
  have hmem : ∀ (y : 𝒢.G.left) (hy : y ∈ U), y = 𝒢.genericUnit →
      𝒢.G.left.presheaf.germ U y hy s ∈
        IsLocalRing.maximalIdeal (𝒢.G.left.presheaf.stalk y) := by
    rintro y hy rfl
    exact hs
  have h1 := hmem (q' x) hx (hq x)
  have h2 : (q'.stalkMap x).hom (𝒢.G.left.presheaf.germ U (q' x) hx s) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) :=
    map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp h1)
  have hfield : IsField ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) := Field.toIsField _
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h2
  have h4 : ((Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt) (q'.appLE U ⊤ h' s) =
      (q'.stalkMap x) (𝒢.G.left.presheaf.germ U (q' x) hx s) := by
    rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]
  have h5 : q'.appLE U ⊤ h' s = 0 := by
    apply germ_injective_of_isIntegral (U := ⊤) _ x hxt
    rw [map_zero]
    exact h4.trans h2
  rw [h5, map_zero]

/-- `germAlong Φ u` vanishes at `0` for `u ∈ 𝔪_ξ`. -/
theorem germAlong_zero_of_mem {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (u : 𝒢.genStalk)
    (hu : u ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ u 0 = 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep u
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  rw [(germAlong_eventuallyEq 𝒢 hΦ U m s).eq_of_nhds, h1]
  exact evalAt_one_eq_zero 𝒢 U m s hu

/-- `germAlong Φ (x * y) = germAlong Φ x * germAlong Φ y` near `0`. -/
theorem germAlong_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x * y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x * 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hprod : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s *
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.mul_apply, h1, h2, h3, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`. -/
theorem fderiv_germAlong_eq_zero_of_mem_sq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) :
    fderiv ℂ (𝒢.germAlong Φ t) 0 = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht (fun u hu v hv => ?_) (fun a b ha hb => ?_)
  · rw [(germAlong_mul_eventuallyEq 𝒢 hΦ u v).fderiv_eq,
      fderiv_mul (germAlong_differentiableAt 𝒢 hΦ u) (germAlong_differentiableAt 𝒢 hΦ v),
      germAlong_zero_of_mem 𝒢 hΦ u hu, germAlong_zero_of_mem 𝒢 hΦ v hv]
    ext v
    simp
  · rw [(germAlong_add_eventuallyEq 𝒢 hΦ a b).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ a) (germAlong_differentiableAt 𝒢 hΦ b), ha, hb,
      add_zero]

/-- **Clause (i) of `JacDetMultilinear`, proved: `jacDet` depends only on the classes `df_i`.** -/
theorem jacDet_congr_dCls {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (h : ∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) : 𝒢.jacDet Φ f = 𝒢.jacDet Φ f' := by
  have hrow : ∀ i, fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 =
      fderiv ℂ (𝒢.germAlong Φ (f' i : 𝒢.genStalk)) 0 := by
    intro i
    have hsq : ((f i : 𝒢.genStalk) - f' i) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2 :=
      (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal 𝒢.genStalk)).mp (h i)
    have hdecomp : (f i : 𝒢.genStalk) = f' i + ((f i : 𝒢.genStalk) - f' i) := by ring
    rw [hdecomp, (germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _),
      fderiv_germAlong_eq_zero_of_mem_sq 𝒢 hΦ _ hsq, add_zero]
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply, hrow i]

end ClassInv

/-- **`JacDetClassInvariant`, proved.** -/
theorem jacDetClassInvariant : JacDetClassInvariant := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ f f' h
  exact jacDet_congr_dCls 𝒢 hΦ f f' h

/-- **`JacDetDescends`, proved** (no hypotheses). -/
theorem jacDetDescends : JacDetDescends :=
  jacDetDescends_of (jacDetMultilinear_of (jacDetClassScalar_of jacDetClassInvariant))

end ZInQ.Metrization


/-! Further verbatim copies from `scratch/metrization/` (only `open PkgI3 (AbVar)` added, the
declarations after the cut points dropped): `part_prodgeo.lean` up to `ProductLatticeFacts`
(exclusive), `part_prodlat.lean` up to `blockLinearEquiv` (exclusive), `part_produnif.lean` up to
`productUniformization_of` (exclusive), `part_prodsplit.lean` up to `productHodgeCompat_of`
(exclusive), `part_prodjac.lean` up to `productMetrizationGeo_of'''` (exclusive),
`part_produnif2.lean` up to `productMetrizationGeo_of_local` (exclusive). -/


/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

/-- The first `g₁` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def leftBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd g₂ i)

/-- The last `g₂` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def rightBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (Fin.natAdd g₁ j)

/-- The product lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁} × ℂ^{g₂} = ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
noncomputable def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) : Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (leftBlock g₁ g₂).toAddMonoidHom.toIntLinearMap ⊓
    Λ₂.comap (rightBlock g₁ g₂).toAddMonoidHom.toIntLinearMap

/-- The product map `ℂ^{g₁+g₂} → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ ≅ 𝒢P(ℂ)_τ`, `z ↦ e⁻¹(Φ₁(z'), Φ₂(z''))`. -/
noncomputable def prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ :=
  fun z => lift (Φ₁ (leftBlock g₁ g₂ z)) (Φ₂ (rightBlock g₁ g₂ z)) ≫ e.inv

end ZInQ.Metrization


/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

end Proof

end ZInQ.Metrization


/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

section ProdPtsAlg

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}

theorem prodPts_comp_fst (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ fst _ _ = Φ₁ (leftBlock g₁ g₂ z) := by
  simp [prodPts]

theorem prodPts_comp_snd (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ snd _ _ = Φ₂ (rightBlock g₁ g₂ z) := by
  simp [prodPts]

theorem pts_ext {p q : 𝒢P.Pts τ} (h1 : p ≫ e.hom ≫ fst _ _ = q ≫ e.hom ≫ fst _ _)
    (h2 : p ≫ e.hom ≫ snd _ _ = q ≫ e.hom ≫ snd _ _) : p = q := by
  rw [← cancel_mono e.hom]
  apply CartesianMonoidalCategory.hom_ext
  · simpa using h1
  · simpa using h2

/-- **The algebraic clauses of `IsAnalyticUniformization` for `prodPts` (proved).** -/
theorem prodPts_alg (hfst : IsMonHom (e.hom ≫ fst _ _)) (hsnd : IsMonHom (e.hom ≫ snd _ _))
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodPts e Φ₁ Φ₂ (z + w) = prodPts e Φ₁ Φ₂ z * prodPts e Φ₁ Φ₂ w) ∧
    (∀ z, prodPts e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodPts e Φ₁ Φ₂) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · apply pts_ext e
    · rw [MonObj.mul_comp, prodPts_comp_fst, prodPts_comp_fst, prodPts_comp_fst, map_add,
        h₁.1]
    · rw [MonObj.mul_comp, prodPts_comp_snd, prodPts_comp_snd, prodPts_comp_snd, map_add,
        h₂.1]
  · constructor
    · intro h
      have e1 : Φ₁ (leftBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_fst e Φ₁ Φ₂ z, h, MonObj.one_comp]
      have e2 : Φ₂ (rightBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_snd e Φ₁ Φ₂ z, h, MonObj.one_comp]
      exact mem_prodLattice.mpr ⟨(h₁.2.1 _).mp e1, (h₂.2.1 _).mp e2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_prodLattice.mp hz
      apply pts_ext e
      · rw [prodPts_comp_fst, MonObj.one_comp, (h₁.2.1 _).mpr hz1]
      · rw [prodPts_comp_snd, MonObj.one_comp, (h₂.2.1 _).mpr hz2]
  · obtain ⟨x, hx⟩ := h₁.2.2.1 (p ≫ e.hom ≫ fst _ _)
    obtain ⟨y, hy⟩ := h₂.2.2.1 (p ≫ e.hom ≫ snd _ _)
    refine ⟨Fin.append x y, pts_ext e ?_ ?_⟩
    · rw [prodPts_comp_fst, leftBlock_append, hx]
    · rw [prodPts_comp_snd, rightBlock_append, hy]

end ProdPtsAlg

/-- **Glue (the analytic half of the product uniformization).** With the hypotheses of
`ProductUniformization`: each `dom (prodPts e Φ₁ Φ₂) U` is open and each regular function on `U`
is holomorphic along `prodPts e Φ₁ Φ₂` there. Why true: as in `ProductUniformization` (basic opens
`D(h)` of products of affine opens; regular functions `a/hⁿ`, `a, h ∈ R₁ ⊗_{𝓞_L} R₂`). STANDARD,
unproved. -/
def ProductUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodPts e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)), DifferentiableOn ℂ
        (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) (𝒢P.dom (prodPts e Φ₁ Φ₂) U))

end ZInQ.Metrization


/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

/-- **Glue (analysis: the Jacobian of the product uniformization is block diagonal).** If
`prodPts e Φ₁ Φ₂` is an analytic uniformization and `f = (p₁*f₁, p₂*f₂)`, then
`jacDet (prodPts e Φ₁ Φ₂) f = jacDet Φ₁ f₁ · jacDet Φ₂ f₂`. Why true: `p₁ ∘ prodPts = Φ₁ ∘ leftBlock`
(`prodPts_comp_fst`), so near `0` the germ `(p₁*f₁ᵢ) ∘ prodPts` is `f₁ᵢ ∘ Φ₁ ∘ leftBlock` (the
representatives agree on an open `V ∋ ξ` and `dom (prodPts) V` is open), whose derivative
vanishes on the last `g₂` coordinates; the matrix is block diagonal (`Matrix.det_fromBlocks_zero₂₁`
after `finSumFinEquiv`). Elementary, unproved (needs the `evalAt`/stalk compatibilities of
`JacDetMultilinear` and functoriality of `evalAt` along morphisms). -/
def ProductJacobian : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _))
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂) →
    ∀ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal 𝒢₁.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal 𝒢₂.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) →
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) →
      𝒢P.jacDet (prodPts e Φ₁ Φ₂) f = 𝒢₁.jacDet Φ₁ f₁ * 𝒢₂.jacDet Φ₂ f₂

end ZInQ.Metrization


/-! ## metrization: `ProductJacobian`, proved (block-diagonal Jacobian of `prodPts`) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

section ProdJac

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Pull-back of a germ is the germ of the pulled-back section. -/
theorem pullGerm_germ {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) [IsMonHom φ]
    (U : ℋ.G.left.Opens) (m : ℋ.genericUnit ∈ U) (s : Γ(ℋ.G.left, U)) :
    (pullGerm φ).hom (ℋ.G.left.presheaf.germ U ℋ.genericUnit m s) =
      𝒢.G.left.presheaf.germ (φ.left ⁻¹ᵁ U) 𝒢.genericUnit
        (by show φ.left 𝒢.genericUnit ∈ U; rw [map_genericUnit_of_isMonHom φ]; exact m)
        (φ.left.app U s) := by
  unfold pullGerm
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- `evalAt` along a morphism of models. -/
theorem evalAt_comp {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) {τ : L →+* ℂ}
    (p : 𝒢.Pts τ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)) :
    𝒢.evalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) = ℋ.evalAt (p ≫ φ) U s := by
  have hp' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := hp
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp']
  rw [show (p ≫ φ).left.appLE U ⊤ hp' = φ.left.app U ≫ p.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hp from
    Scheme.Hom.comp_appLE p.left φ.left U ⊤ hp']
  rfl

variable {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
  {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
  {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem germAlong_pull_fst_eventuallyEq (hΦ₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₁.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ fst _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₁.germAlong Φ₁ t (leftBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₁.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (leftBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (leftBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₁ hΦ₁ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ fst _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ fst _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₁.germAlong Φ₁ (𝒢₁.G.left.presheaf.germ U 𝒢₁.genericUnit m s) (leftBlock g₁ g₂ z) =
      𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_fst]

theorem germAlong_pull_snd_eventuallyEq (hΦ₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₂.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ snd _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₂.germAlong Φ₂ t (rightBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₂.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (rightBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (rightBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₂ hΦ₂ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ snd _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ snd _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₂.germAlong Φ₂ (𝒢₂.G.left.presheaf.germ U 𝒢₂.genericUnit m s) (rightBlock g₁ g₂ z) =
      𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_snd]

/-- Derivative of `F ∘ ℓ` for a linear `ℓ` on `ℂ^{g₁+g₂}` (chain rule). -/
theorem fderiv_comp_linear {n : ℕ} (ℓ : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (w : Fin (g₁ + g₂) → ℂ) :
    fderiv ℂ (fun z => F (ℓ z)) 0 w = fderiv ℂ F 0 (ℓ w) := by
  let ℓc := LinearMap.toContinuousLinearMap ℓ
  have hfun : (fun z => F (ℓ z)) = F ∘ ℓc := by
    funext z; simp [ℓc]
  have hF' : DifferentiableAt ℂ F (ℓc 0) := by rw [map_zero]; exact hF
  rw [hfun, fderiv_comp _ hF' ℓc.differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  simp [ℓc]

end ProdJac

/-- **`ProductJacobian`, proved.** -/
theorem productJacobian : ProductJacobian := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hΦP f₁ f₂ f hf1 hf2
  have hl : ∀ (i : Fin g₁) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.castAdd g₂ i) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (leftBlock g₁ g₂ w) := by
    intro i w
    rw [hf1 i, (germAlong_pull_fst_eventuallyEq e hΦ₁ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (leftBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₁ hΦ₁ _) w
  have hr : ∀ (j : Fin g₂) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.natAdd g₁ j) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ j : 𝒢₂.genStalk)) 0 (rightBlock g₁ g₂ w) := by
    intro j w
    rw [hf2 j, (germAlong_pull_snd_eventuallyEq e hΦ₂ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (rightBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₂ hΦ₂ _) w
  have hL1 : ∀ j : Fin g₁, leftBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  have hL2 : ∀ j : Fin g₂, leftBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR1 : ∀ j : Fin g₁, rightBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR2 : ∀ j : Fin g₂, rightBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  let J₁ : Matrix (Fin g₁) (Fin g₁) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (Pi.single j 1)
  let J₂ : Matrix (Fin g₂) (Fin g₂) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ i : 𝒢₂.genStalk)) 0 (Pi.single j 1)
  have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j : Fin (g₁ + g₂) =>
        fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f i : 𝒢P.genStalk)) 0 (Pi.single j 1)) =
      Matrix.fromBlocks J₁ 0 0 J₂ := by
    ext (i | i) (j | j)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, J₁]
      rw [hl, hL1 j]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [hl, hL2, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hr, hR1, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, J₂]
      rw [hr, hR2]
  unfold GroupModel.jacDet
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, hblock, Matrix.det_fromBlocks_zero₂₁]

end ZInQ.Metrization


/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology
open PkgI3 (AbVar)

/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

section Local

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
  {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem leftBlock_differentiable : Differentiable ℂ (leftBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (leftBlock g₁ g₂)).differentiable
  simpa using h

theorem rightBlock_differentiable : Differentiable ℂ (rightBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (rightBlock g₁ g₂)).differentiable
  simpa using h

/-- The local statement: every point of `dom (prodPts) U` has an open neighbourhood inside
`dom (prodPts) U` on which `z ↦ s(prodPts z)` is holomorphic. -/
theorem prodPts_local (hLS : ProductLocalStructure) (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (z₀ : Fin (g₁ + g₂) → ℂ) (hz₀ : z₀ ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U) :
    ∃ N : Set (Fin (g₁ + g₂) → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) N := by
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ U s (Φ₁ (leftBlock g₁ g₂ z₀)) (Φ₂ (rightBlock g₁ g₂ z₀)) hz₀
  let O : Set (Fin (g₁ + g₂) → ℂ) :=
    leftBlock g₁ g₂ ⁻¹' 𝒢₁.dom Φ₁ V₁ ∩ rightBlock g₁ g₂ ⁻¹' 𝒢₂.dom Φ₂ V₂
  have hO : IsOpen O :=
    ((h₁.2.2.2.1 V₁).preimage (leftBlock_differentiable).continuous).inter
      ((h₂.2.2.2.1 V₂).preimage (rightBlock_differentiable).continuous)
  have hd1 : ∀ σ : Γ(𝒢₁.G.left, V₁),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ σ) O := fun σ =>
    (h₁.2.2.2.2 V₁ σ).comp (leftBlock_differentiable).differentiableOn (fun z hz => hz.1)
  have hd2 : ∀ σ : Γ(𝒢₂.G.left, V₂),
      DifferentiableOn ℂ (fun z => 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ σ) O := fun σ =>
    (h₂.2.2.2.2 V₂ σ).comp (rightBlock_differentiable).differentiableOn (fun z hz => hz.2)
  let H : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k)
  let Afun : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k)
  have hH : DifferentiableOn ℂ H O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k))
      (fun k _ => (hd1 (c k)).mul (hd2 (d k)))
    convert this using 1
    funext z
    simp [H, Finset.sum_apply]
  have hA : DifferentiableOn ℂ Afun O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k))
      (fun k _ => (hd1 (a k)).mul (hd2 (b k)))
    convert this using 1
    funext z
    simp [Afun, Finset.sum_apply]
  let N := O ∩ H ⁻¹' {0}ᶜ
  have hN : IsOpen N := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : ∀ z ∈ N, z ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s = Afun z / H z := by
    intro z hz
    obtain ⟨hmem, heq⟩ := hall _ _ hz.1.1 hz.1.2 hz.2
    refine ⟨hmem, ?_⟩
    rw [eq_div_iff hz.2]
    exact heq
  refine ⟨N, hN, ⟨⟨hV₁, hV₂⟩, hne⟩, fun z hz => (hsub z hz).1, ?_⟩
  have hdiv : DifferentiableOn ℂ (fun z => Afun z * (H z)⁻¹) N :=
    (hA.mono Set.inter_subset_left).mul
      ((hH.mono Set.inter_subset_left).inv (fun z hz => hz.2))
  refine hdiv.congr fun z hz => ?_
  rw [(hsub z hz).2, div_eq_mul_inv]

end Local

/-- **`ProductUniformizationAnalytic` from `ProductLocalStructure` (proved).** -/
theorem productUniformizationAnalytic_of (hLS : ProductLocalStructure) :
    ProductUniformizationAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, hsub, -⟩ := prodPts_local e hLS h₁ h₂ U 0 z₀ hz₀
    exact ⟨N, hsub, hN, hz₀N⟩
  · intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, -, hd⟩ := prodPts_local e hLS h₁ h₂ U s z₀ hz₀
    exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

end ZInQ.Metrization


namespace ZInQ.ProductUnif

/-! ## §4. S-alg (`ProductMetrizationOfProductUnif`): reduction to three smaller glue Props

`productMetrizationOfProductUnif_of : HodgeLatticeTheorem → ProductUnifDims → JacDetDescends →
ProductHodgeAdd → ProductMetrizationOfProductUnif` (proved). `HodgeLatticeTheorem` is the kernel's
glue Prop (`ZInQKernel/HDecomp/Faltings/Models.lean`); the other three are new glue. -/

section SAlg

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight
open PkgI3 (AbVar)

/-- **Glue S-alg-1 (dimensions and nonsingularity in product form).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂`
have homomorphic components, and at `τ` let the metrization `MP` (dimension `g`) be in product
form: period lattice `Λ₁ × Λ₂` and coefficient map computed by `Φ₁ × Φ₂`, for full-lattice
analytic uniformizations `Φᵢ : ℂ^{gᵢ} → 𝒢ᵢ(ℂ)_τ`, `g₁ + g₂ = g`. Then `g₁ = dim A`, `g₂ = dim B`,
and both factor Jacobians are nonsingular on some `gᵢ`-tuple of germs.

Why true (STANDARD; algebra and calculus, no AN3). Write `nᵢ` for the dimension of the cotangent
space `𝔪/𝔪²` of `𝒢ᵢ` at the generic unit (`= dim` of the factor, a regular local ring of the
smooth generic fibre). Via `e`, `𝔪_P/𝔪_P² = 𝔪₁/𝔪₁² ⊕ 𝔪₂/𝔪₂²` (the unit of a product), so
`hodgeSpace_P g = L ⊗ ⋀^g(cot₁ ⊕ cot₂)` and `MP.hodge.finrank_eq_one` gives `g ∈ {0, n₁ + n₂}`.
If `g = 0`, the `Φᵢ : ℂ⁰ → 𝒢ᵢ(ℂ)_τ` are onto, so `A_τ(ℂ)`, `B_τ(ℂ)` are trivial and `dim A = dim B
= 0`. Otherwise `MP.hodge.coeff_ne_zero` and the coefficient formula give `f` with
`jacDet (Φ₁ × Φ₂) f ≠ 0`; the derivative at `0` of a germ along `Φ₁ × Φ₂` depends only on its
class in `cot₁ ⊕ cot₂` and is block-shaped, so the nonsingular `g × g` Jacobian forces `g₁ ≤ n₁`,
`g₂ ≤ n₂`, hence equality, and nonsingular diagonal blocks. Unproved. -/
def ProductUnifDims : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂ ∧ (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0)

/-- **Glue S-alg-2 (the Jacobian determinant descends to the Hodge line).** For a group model `𝒢`
of `A_L` with `dim A = d` and an analytic uniformization `Φ : ℂ^d → 𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(fᵢ ∘ Φ)/∂zⱼ(0))` on `d`-tuples of germs in `𝔪_ξ` is the restriction to
wedges of a `τ`-semilinear map `hodgeSpace d → ℂ`.

Why true (STANDARD; calculus). The derivative at `0` of `germAlong Φ f` does not depend on the
representative (`dom Φ U` is open and contains `0`), is additive in `f`, satisfies
`d(a f) = τ(a) df` for `a ∈ 𝓞_L` and `d(fh) = f(1) dh + h(1) df = 0` for `f, h ∈ 𝔪_ξ` (clause 5,
Leibniz). So `df ↦ d(f ∘ Φ)(0)` is a `τ`-semilinear map on `𝔪/𝔪²`; the determinant is
alternating multilinear, so it factors through `⋀^d_{𝓞_L}`, then through `L ⊗_{𝓞_L} ⋀^d`
(`l ⊗ ω ↦ τ(l) c(ω)`). Unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (d : ℕ), A.dim = d → ∀ (τ : L →+* ℂ) (Λ : Submodule ℤ (Fin d → ℂ))
    (Φ : (Fin d → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace d →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue S-alg-3 (additivity of the height for a product-form metrization).** Let
`e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components, `g₁ + g₂ = g`, and let `D₁`, `D₂` be Hodge
data of the factors with the genuine lattices `⋀^{gᵢ} ω_{𝒢ᵢ}`, such that at every `τ` there are
analytic uniformizations `Φᵢ` of the factors with kernels the periods of `Dᵢ`, computing the
coefficients of `Dᵢ`, while `MP` has periods `D₁.periods × D₂.periods` and coefficients computed
by `Φ₁ × Φ₂`. Then `h(D₁) + h(D₂) ≤ h(MP)`.

Why true (STANDARD; equality holds). `ω_{MP} = ω₁ ⊕ ω₂` (unit of a product; this is a statement
about the conormal lattices `omega`, not only the generic cotangent spaces), so
`s = p₁*s₁ ∧ p₂*s₂ ∈ ⋀^g ω_{MP}` for bases `sᵢ` of `⋀^{gᵢ} ω_{𝒢ᵢ}` and
`secIndex s = secIndex s₁ · secIndex s₂`; the Jacobian of `Φ₁ × Φ₂` on `p₁*f ∧ p₂*h` is block
diagonal, so the coefficients multiply; `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`
(`prodLattice_facts` of product-height, proved, plus a coordinate permutation `Fin.cast`); then
`modelHeight_add_of` (product-height, proved). Unproved as a whole. -/
def ProductHodgeAdd : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    D₁.modelHeight + D₂.modelHeight ≤ MP.hodge.modelHeight

theorem natCast_eq_of_dim {K : Type} [Field K] {A : AbVar K} {m n : ℕ} (hm : A.dim = m)
    (hn : A.dim = n) : m = n := by
  have h : ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hm.symm.trans hn
  exact_mod_cast WithBot.coe_injective h

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends`, `ProductHodgeAdd`
(proved).** The factor metrizations are built here: dimension `dᵢ = dim` (constant in `τ` by
`ProductUnifDims`), lattice `⋀^{dᵢ} ω_{𝒢ᵢ}` (`HodgeLatticeTheorem`), periods `Λᵢ(τ)`, coefficient
maps from `JacDetDescends`, nonzero by the nonsingular factor Jacobians. -/
theorem productMetrizationOfProductUnif_of (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hP : ProductHodgeAdd) : ProductMetrizationOfProductUnif := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ hform
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨d₁, d₂, hd, Λ₁₀, Λ₂₀, Φ₁₀, Φ₂₀, hl₁₀, hl₂₀, hu₁₀, hu₂₀, hper₀, hco₀⟩ := hform τ₀
  obtain ⟨hA, hB, -, -⟩ :=
    hD K A B C L 𝒢₁ 𝒢₂ g MP e τ₀ d₁ d₂ hd Λ₁₀ Λ₂₀ Φ₁₀ Φ₂₀ hl₁₀ hl₂₀ hu₁₀ hu₂₀ hper₀ hco₀
  have norm : ∀ τ : L →+* ℂ, ∃ (Λ₁ : Submodule ℤ (Fin d₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin d₂ → ℂ))
      (Φ₁ : (Fin d₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin d₂ → ℂ) → 𝒢₂.Pts τ),
      (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
      (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hd i)) ∈ prodLattice Λ₁ Λ₂) ∧
      (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hd i))) f) ∧
      (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0) := by
    intro τ
    obtain ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco⟩ := hform τ
    obtain ⟨hA', hB', hn₁, hn₂⟩ :=
      hD K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
    obtain rfl : g₁ = d₁ := natCast_eq_of_dim hA' hA
    obtain rfl : g₂ = d₂ := natCast_eq_of_dim hB' hB
    exact ⟨Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco, hn₁, hn₂⟩
  choose Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco hn₁ hn₂ using norm
  obtain ⟨hfr₁, hlat₁⟩ := hH K A L 𝒢₁ d₁ hA
  obtain ⟨hfr₂, hlat₂⟩ := hH K B L 𝒢₂ d₂ hB
  choose c₁ hc₁ using fun τ => hJ K A L 𝒢₁ d₁ hA τ (Λ₁ τ) (Φ₁ τ) (hu₁ τ)
  choose c₂ hc₂ using fun τ => hJ K B L 𝒢₂ d₂ hB τ (Λ₂ τ) (Φ₂ τ) (hu₂ τ)
  let D₁ : HodgeData L d₁ (𝒢₁.hodgeSpace d₁) :=
    { lattice := 𝒢₁.detLattice d₁
      finrank_eq_one := hfr₁
      isLattice := hlat₁
      periods := Λ₁
      periods_discrete := fun τ => (hl₁ τ).fst
      periods_isZLattice := fun τ => (hl₁ τ).snd
      coeff := c₁
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₁ τ
        apply hf
        rw [← hc₁ τ f, h]
        rfl }
  let D₂ : HodgeData L d₂ (𝒢₂.hodgeSpace d₂) :=
    { lattice := 𝒢₂.detLattice d₂
      finrank_eq_one := hfr₂
      isLattice := hlat₂
      periods := Λ₂
      periods_discrete := fun τ => (hl₂ τ).fst
      periods_isZLattice := fun τ => (hl₂ τ).snd
      coeff := c₂
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₂ τ
        apply hf
        rw [← hc₂ τ f, h]
        rfl }
  let M₁ : MetrizedModel A L d₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := rfl, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L d₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := rfl, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  refine ⟨d₁, d₂, M₁, M₂, rfl, rfl, ?_⟩
  exact hP K A B C L 𝒢₁ 𝒢₂ g MP e d₁ d₂ hd D₁ D₂ rfl rfl
    (fun τ => ⟨Φ₁ τ, Φ₂ τ, hu₁ τ, hu₂ τ, hc₁ τ, hc₂ τ, hper τ, hco τ⟩)

/-- **Glue S-alg-3a (sections of the Hodge lattices in product form).** Under the hypotheses of
`ProductHodgeAdd`, there are nonzero `s ∈ ⋀^g ω_{MP}`, `sᵢ ∈ ⋀^{gᵢ} ω_{𝒢ᵢ}` whose lattice indices
and coefficients multiply.

Why true (STANDARD). `ω_{MP} = ω₁ ⊕ ω₂` (pull back along the projections, restrict along the unit
sections of the other factor), so `s = p₁*s₁ ∧ p₂*s₂` generates `⋀^g ω_{MP} = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂`
locally where the `sᵢ` do, and `secIndex s = secIndex s₁ · secIndex s₂` (the index of `𝓞_L s₁ ⊗ 𝓞_L s₂`
in a tensor product of invertible modules is multiplicative). For coefficients: write `s₁`, `s₂`
as `𝓞_L`-combinations of wedges; on `p₁*f ∧ p₂*h` the Jacobian of `Φ₁ × Φ₂` at `0` is block
diagonal, so `coeff_P(s) = coeff₁(s₁) · coeff₂(s₂)`. Unproved. -/
def ProductHodgeSections : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    ∃ (s : MP.model.hodgeSpace g) (s₁ : 𝒢₁.hodgeSpace g₁) (s₂ : 𝒢₂.hodgeSpace g₂),
      s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ D₁.lattice ∧ s₁ ≠ 0 ∧ s₂ ∈ D₂.lattice ∧ s₂ ≠ 0 ∧
      secIndex MP.hodge.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂ ∧
      ∀ τ, MP.hodge.coeff τ s = D₁.coeff τ s₁ * D₂.coeff τ s₂

/-- The covolume of a lattice in product form, up to the coordinate cast (proved, from
product-height's `prodLattice_facts`). -/
theorem covolume_of_cast {g g₁ g₂ : ℕ} (hg : g₁ + g₂ = g) (Λ : Submodule ℤ (Fin g → ℂ))
    (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁]
    [IsZLattice ℝ Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂]
    (h : ∀ z, z ∈ Λ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) :
    ZLattice.covolume Λ = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  subst hg
  have hΛ : Λ = prodLattice Λ₁ Λ₂ := by
    ext z
    rw [h z]
    rfl
  subst hΛ
  obtain ⟨-, -, hc⟩ := prodLattice_facts Λ₁ Λ₂
  exact hc

/-- **`ProductHodgeAdd` from `ProductHodgeSections` (proved).** The covolumes multiply
(`covolume_of_cast`) and `modelHeight_add_of` gives equality of heights. -/
theorem productHodgeAdd_of (h : ProductHodgeSections) : ProductHodgeAdd := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  obtain ⟨s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hco⟩ :=
    h K A B C L 𝒢₁ 𝒢₂ g MP e g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  have hcov : ∀ τ, ZLattice.covolume (MP.hodge.periods τ) =
      ZLattice.covolume (D₁.periods τ) * ZLattice.covolume (D₂.periods τ) := by
    intro τ
    obtain ⟨-, -, -, -, -, -, hper, -⟩ := hform τ
    have := D₁.periods_discrete τ
    have := D₁.periods_isZLattice τ
    have := D₂.periods_discrete τ
    have := D₂.periods_isZLattice τ
    exact covolume_of_cast hg _ _ _ hper
  subst hg
  exact (modelHeight_add_of MP.hodge D₁ D₂ hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hco hcov).ge

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends` and
`ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of hH hD hJ (productHodgeAdd_of hS)

/-- **`JacDetDescends` (S-alg-2), proved**: metrization's `jacDetDescends` (§3b, no dimension
hypothesis needed). -/
theorem jacDetDescends' : JacDetDescends :=
  fun K _ A L _ _ _ 𝒢 d _ τ Λ Φ hΦ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ d Λ Φ hΦ

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims` and `ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of'' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of' hH hD jacDetDescends' hS

/-- `prodUnif` (product-height) is metrization's `prodPts` (proved). -/
theorem prodUnif_eq_prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    prodUnif e Φ₁ Φ₂ = ZInQ.Metrization.prodPts e Φ₁ Φ₂ := by
  funext z
  unfold prodUnif
  rw [MulEquiv.symm_apply_eq]
  apply Prod.ext
  · exact (ZInQ.Metrization.prodPts_comp_fst e Φ₁ Φ₂ z).symm
  · exact (ZInQ.Metrization.prodPts_comp_snd e Φ₁ Φ₂ z).symm

/-- product-height's `prodLattice` is metrization's (proved). -/
theorem prodLattice_eq_metrization {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZInQ.Metrization.prodLattice Λ₁ Λ₂ := by
  ext z
  exact Iff.rfl

/-- **`ProductHodgeSections` from metrization's `ProductUniformizationAnalytic` and
`ProductHodgeLattice` (proved).** The factor metrizations are assembled from the hypotheses;
`ProductHodgeLattice` gives the sections and the index; metrization's `productJacobian`
(proved, §3b) gives the multiplicativity of the coefficients, applied to `prodPts = prodUnif`,
which is an analytic uniformization by `prodPts_alg` and `ProductUniformizationAnalytic`. -/
theorem productHodgeSections_of (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductHodgeSections := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e he₁ he₂ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  subst hg
  choose Φ₁ Φ₂ hu₁ hu₂ hc₁ hc₂ hper hco using hform
  let M₁ : MetrizedModel A L g₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := hl₁, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L g₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := hl₂, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  obtain ⟨-, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L MP.model g₁ g₂ M₁ M₂ e he₁ he₂
  refine ⟨(a₁ * a₂) • MP.model.wedge f, a₁ • 𝒢₁.wedge f₁, a₂ • 𝒢₂.wedge f₂, ?_, hs0, hs₁, hs₁0,
    hs₂, hs₂0, ?_, fun τ => ?_⟩
  · rw [MP.lattice_eq]
    exact hs
  · rw [MP.lattice_eq]
    exact hidx
  · obtain ⟨hhom, hker, hsurj⟩ := ZInQ.Metrization.prodPts_alg e he₁ he₂ (hu₁ τ) (hu₂ τ)
    obtain ⟨hopen, hdiff⟩ := hPA K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
      (hu₁ τ) (hu₂ τ)
    have hjac := ZInQ.Metrization.productJacobian K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _
      (Φ₁ τ) (Φ₂ τ) (hu₁ τ) (hu₂ τ) ⟨hhom, hker, hsurj, hopen, hdiff⟩ f₁ f₂ f hf1 hf2
    have hfun : (fun z => prodUnif e (Φ₁ τ) (Φ₂ τ) (fun i => z (Fin.cast rfl i))) =
        ZInQ.Metrization.prodPts e (Φ₁ τ) (Φ₂ τ) := by
      rw [← prodUnif_eq_prodPts]
      rfl
    have hc := hco τ f
    rw [hfun] at hc
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
    simp only [smul_eq_mul]
    ring

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, metrization's
`ProductUniformizationAnalytic` and `ProductHodgeLattice` (proved).** -/
theorem productMetrizationOfProductUnif_of_metrization (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of'' hH hD (productHodgeSections_of hPA hL)

/-- **The same with `ProductLocalStructure` (metrization's glue, pure algebraic geometry) in place
of `ProductUniformizationAnalytic` (proved, via metrization's `productUniformizationAnalytic_of`).** -/
theorem productMetrizationOfProductUnif_of_local (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_metrization hH hD
    (ZInQ.Metrization.productUniformizationAnalytic_of hLS) hL

end SAlg

end ZInQ.ProductUnif

#print axioms ZInQ.ProductUnif.pts_eq_of_evalAt
#print axioms ZInQ.ProductUnif.kerSub_facts
#print axioms ZInQ.ProductUnif.productUnifSplits
#print axioms ZInQ.ProductUnif.productMetrizationOfProductUnif_of
#print axioms ZInQ.ProductUnif.productHodgeAdd_of
#print axioms ZInQ.ProductUnif.productMetrizationOfProductUnif_of'
#print axioms ZInQ.ProductUnif.jacDetDescends'
#print axioms ZInQ.ProductUnif.productMetrizationOfProductUnif_of''
#print axioms ZInQ.ProductUnif.productHodgeSections_of
#print axioms ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
