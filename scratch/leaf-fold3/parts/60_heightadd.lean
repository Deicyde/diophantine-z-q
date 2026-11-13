-- (leaf-fold2: copied from scratch/g0-assemble2/parts/60_heightadd.lean; 0 HDec name-resolution edits)
/-! ## g0-heightadd: lines 390-473 of scratch/g0-heightadd/part_heightadd.lean and the G0HeightAdd section of part_prod.lean (lines 1-92) -/
section G0HeightAddSec
noncomputable section

/-! ## Glue P2 (`ProductModelHeight`) from four smaller Props

`ProductModelHeight` (h5-neron) compares, for a product model `𝒢P ≅ 𝒢₁ × 𝒢₂`, the heights of
the three group models (infima over metrizations). It follows from:
* `AnalyticUniformizationUnique` (def-faltings, already stated: the uniqueness half of AN3);
* `MetrizationDimUnique` (new glue): two metrizations of one group model have the same `g`;
* `MetrizationExists` (new glue): every group model has a metrization;
* `ProductMetrization` (new glue P2a): metrizations of `𝒢₁`, `𝒢₂` give one of `𝒢P` whose height
  is the sum (the construction direction; equality). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings H5Neron

/-- **Glue P2a (product of metrized models).** If `𝒢P ≅ 𝒢₁ × 𝒢₂` (`IsProductModel`) and `M₁`, `M₂`
are metrizations of `𝒢₁`, `𝒢₂` of dimensions `g₁`, `g₂`, then `𝒢P` has a metrization of
dimension `g₁ + g₂` whose model height is the sum. Why true (STANDARD): the cotangent space at
the identity of `𝒢₁ ×_{𝓞_L} 𝒢₂` is `ω₁ ⊕ ω₂` (and `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` as lattices),
`⋀^{g₁+g₂}(ω₁ ⊕ ω₂) = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂`, the product `Φ₁ × Φ₂ : ℂ^{g₁+g₂} → 𝒢₁(ℂ) × 𝒢₂(ℂ)`
is an analytic uniformization with kernel `Λ₁ × Λ₂` whose Jacobian determinant on product
wedges is the product, `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`, and the Arakelov degree of a
tensor product of Hermitian lines is the sum (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1;
locators UNVERIFIED). Unproved: Mathlib has no computation of the stalk of a fibre product of
schemes. -/
def ProductMetrization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ MP : MetrizedModel C L (g₁ + g₂), MP.model = 𝒢P ∧
        MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight

/-- **Glue (existence of metrizations; correctness of def-faltings' definition).** Every smooth
group model `𝒢` of `A_L` carries a metrization (of dimension `dim A`). Why true (STANDARD): the
Hodge data of `𝒢` exist by `HodgeLatticeTheorem` and the uniformization of each `𝒢(ℂ)_τ` by
`AnalyticUniformizationExists` (Mumford, *Abelian varieties* §1, UNVERIFIED), with the
coefficient map `coeff_τ(1 ⊗ df) = jacDet Φ f`. This is the same caveat as on `LeafAdopt.H5`
(the index set of the infimum is nonempty), for each model separately. Unproved. -/
def MetrizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢

/-- **Glue (the dimension of a metrization).** Two metrizations of the same group model have
the same dimension (both equal `dim A`: the `MetrizedModel` docstring's argument: for
`0 < g ≠ dim A` the Hodge space is not a line, and `g = 0` is excluded for `dim A ≥ 1` by the
surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)`; STANDARD, unproved). -/
def MetrizationDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization bounds the height of its model from above. -/
theorem height_le_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le h le_rfl))

/-- Given AN3-uniqueness and `MetrizationDimUnique`, a metrization computes the height of its
model (from below; with `height_le_of_model`, equality). -/
theorem le_height_of_model (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L} (h : M.model = 𝒢) :
    (M.hodge.modelHeight : EReal) ≤ 𝒢.height := by
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hD K A L g g' M M' (h.trans hM'.symm)
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' (h.trans hM'.symm)]

/-- **Glue P2 (`ProductModelHeight`) from `AnalyticUniformizationUnique`,
`MetrizationDimUnique`, `MetrizationExists` and `ProductMetrization`.** -/
theorem productModelHeight_of (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hP : ProductMetrization) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP, hMP, hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  calc 𝒢₁.height + 𝒢₂.height
      ≤ (M₁.hodge.modelHeight : EReal) + (M₂.hodge.modelHeight : EReal) :=
        add_le_add (height_le_of_model M₁ h₁) (height_le_of_model M₂ h₂)
    _ = (MP.hodge.modelHeight : EReal) := by rw [hh, EReal.coe_add]
    _ ≤ 𝒢P.height := le_height_of_model hU hD MP hMP

end ZInQ.G0HeightAdd

/-! ## P2a split: the Arakelov-degree half proved

`ProductMetrization` (P2a) = a geometric construction (`ProductMetrizationGeo`: the product
metrization with a product section `η = η₁ ∧ η₂` for which the index, the coefficients and the
covolumes are multiplicative) + the height computation (`modelHeight_add_of`, proved). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings H5Neron

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (proved).** If the Hodge data `D` (dimension `g₁ + g₂`)
has a nonzero section `s` whose lattice index, coefficients and period covolumes are the
products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)` (Faltings' formula `HodgeData.modelHeight_eq` and `log` of products). -/
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

/-- **Glue P2a-geo (the product metrization, geometric half of P2a).** For `𝒢P ≅ 𝒢₁ × 𝒢₂` and
metrizations `M₁`, `M₂`, there is a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero
sections `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` such that the lattice index, the coefficients
and the period covolumes of `s` are the products of those of `s₁`, `s₂`. Why true (STANDARD):
take `s = p₁*s₁ ∧ p₂*s₂`; `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` gives `⋀^{top}ω_{𝒢P} = ⋀ω_{𝒢₁} ⊗ ⋀ω_{𝒢₂}`, and
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` is the product (norms of ideals are
multiplicative); `Φ₁ × Φ₂` (coordinates `Fin.append`) is an analytic uniformization of
`𝒢P(ℂ)_τ = 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with period lattice `Λ₁ × Λ₂`, block-diagonal Jacobian
(so `jacDet` multiplies), and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`. Unproved (stalks of fibre
products of schemes are not in Mathlib). -/
def ProductMetrizationGeo : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ (MP : MetrizedModel C L (g₁ + g₂)) (s : MP.model.hodgeSpace (g₁ + g₂))
        (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
        MP.model = 𝒢P ∧ s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
        s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
        secIndex MP.hodge.lattice s = secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
        (∀ σ, MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ * M₂.hodge.coeff σ s₂) ∧
        (∀ σ, ZLattice.covolume (MP.hodge.periods σ) =
          ZLattice.covolume (M₁.hodge.periods σ) * ZLattice.covolume (M₂.hodge.periods σ))

/-- **P2a from P2a-geo (proved).** -/
theorem productMetrization_of_geo (h : ProductMetrizationGeo) : ProductMetrization := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  obtain ⟨MP, s, s₁, s₂, hMP, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hc, hcov⟩ :=
    h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  exact ⟨MP, hMP, modelHeight_add_of MP.hodge M₁.hodge M₂.hodge hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hc hcov⟩

end ZInQ.G0HeightAdd
end
end G0HeightAddSec
