/-! ## unif-dims: `ProductUnifDims` from T35 (`UniformizationExists`)

The dimension half (`ProductUnifDimsEq`) holds because the dimension of an analytic uniformization
of `𝒢(ℂ)_τ` is determined by the group `𝒢(ℂ)_τ` (its 2-torsion has `4^g` elements,
`ZInQ.UnifDims.dim_eq_of_unif`), and T35 supplies one uniformization of dimension `dim A`
(`AnalyticUniformizationOfDim`, metrization2's transport of T35 to group models). The
nonsingularity half is metrization2's `jacDetNondegenerate` (proved, no hypotheses). The product
structure and the metrization `MP` are not used. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

/-- An abelian variety has finite dimension (copied from metrization's `abVar_dim_finite`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **The dimension of an analytic uniformization is `dim A`** (from `AnalyticUniformizationOfDim`,
i.e. from T35). Any full-lattice analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` has `g = dim A`. Only
the algebraic clauses (homomorphism, kernel, onto) of the two uniformizations are used. -/
theorem dim_eq_of_isAnalyticUniformization (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : A.dim = (g : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ := hU K A L 𝒢 τ n hn
  have := dim_eq_of_unif Φ Λ Φ' Λ' hd hz hd' hz' hΦ.1 hΦ.2.1 hΦ.2.2.1 hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [hn, this]

/-- **`ProductUnifDimsEq` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDimsEq_of (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDimsEq := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ _ _
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨dim_eq_of_isAnalyticUniformization hU 𝒢₁ τ Λ₁ Φ₁ hd₁ hz₁ hu₁,
    dim_eq_of_isAnalyticUniformization hU 𝒢₂ τ Λ₂ Φ₂ hd₂ hz₂ hu₂⟩

/-- **`ProductUnifDims` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDims_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDims :=
  ZInQ.ProductUnif.productUnifDims_of (productUnifDimsEq_of hU)
    ZInQ.Metrization2.jacDetNondegenerate

/-- **`ProductUnifDims` from the textbook leaf T35 `UniformizationExists` (proved).** -/
theorem productUnifDims_of_uniformizationExists (hT : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductUnif.ProductUnifDims :=
  productUnifDims_of_unifOfDim
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT)

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.dim_eq_of_unif
#print axioms ZInQ.UnifDims.dim_eq_of_isAnalyticUniformization
#print axioms ZInQ.UnifDims.productUnifDimsEq_of
#print axioms ZInQ.UnifDims.productUnifDims_of_unifOfDim
#print axioms ZInQ.UnifDims.productUnifDims_of_uniformizationExists
#print axioms ZInQ.Metrization2.jacDetNondegenerate
#print axioms ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists
