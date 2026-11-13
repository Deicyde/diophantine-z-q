
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

namespace HSyn.G0Split

/-- **`HeightAdditivity` from N1, `r.h5`, U and three glue Props, with P2a reduced to its
geometric half.** -/
theorem heightAdditivity_of_geo (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hD : ZInQ.G0HeightAdd.MetrizationDimUnique) (hE : ZInQ.G0HeightAdd.MetrizationExists)
    (hG : ZInQ.G0HeightAdd.ProductMetrizationGeo) : HeightAdditivity :=
  heightAdditivity_of_split hN1 h5 hU hD hE (ZInQ.G0HeightAdd.productMetrization_of_geo hG)

end HSyn.G0Split

#print axioms ZInQ.G0HeightAdd.modelHeight_add_of
#print axioms ZInQ.G0HeightAdd.productMetrization_of_geo
#print axioms HSyn.G0Split.heightAdditivity_of_geo
