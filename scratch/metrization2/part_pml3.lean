/-! ## metrization2: `ProductMapLocalStructure`, hence `JacDetNondegenerate` and
`ProductLocalStructure`, proved -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **`ProductMapLocalStructure`, proved** (from `core_local` with `S = Spec 𝓞_L`,
`W = m⁻¹(U)`, `t = m^*s`). -/
theorem productMapLocalStructure : ProductMapLocalStructure := by
  intro K _ A B C L _ _ _ ℋ 𝒢₁ 𝒢₂ m τ U s p₁ p₂ hp
  have hw : ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), p₁'.left ≫ 𝒢₁.G.hom = p₂'.left ≫ 𝒢₂.G.hom :=
    fun p₁' p₂' => (Over.w p₁').trans (Over.w p₂').symm
  obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
    core_local 𝒢₁.G.hom 𝒢₂.G.hom (m.left ⁻¹ᵁ U) (m.left.app U s) p₁.left p₂.left (hw p₁ p₂) hp
  refine ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, fun p₁' p₂' h1' h2' hne' => ?_⟩
  obtain ⟨hmem, heq⟩ := hall p₁'.left p₂'.left (hw p₁' p₂') h1' h2' hne'
  refine ⟨hmem, ?_⟩
  have hev : ℋ.evalAt (lift p₁' p₂' ≫ m) U s =
      ev (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) (m.left ⁻¹ᵁ U) (m.left.app U s) :=
    ev_comp (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) m.left U s
  rw [hev]
  exact heq

/-- **`JacDetNondegenerate`, proved** (no hypotheses). -/
theorem jacDetNondegenerate : ZInQ.Metrization.JacDetNondegenerate :=
  jacDetNondegenerate_of productMapLocalStructure

/-- **metrization's `ProductLocalStructure`, proved** (no hypotheses). -/
theorem productLocalStructure : ZInQ.Metrization.ProductLocalStructure :=
  productLocalStructure_of productMapLocalStructure

end ZInQ.Metrization2

#print axioms ZInQ.Metrization2.productMapLocalStructure
#print axioms ZInQ.Metrization2.jacDetNondegenerate
#print axioms ZInQ.Metrization2.productLocalStructure
