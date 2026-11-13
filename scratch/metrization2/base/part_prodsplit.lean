
/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

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

/-- **`ProductHodgeCompat` from `ProductUniformization`, `ProductHodgeLattice` and
`ProductJacobian` (proved).** -/
theorem productHodgeCompat_of (hPU : ProductUniformization) (hL : ProductHodgeLattice)
    (hJ : ProductJacobian) : ProductHodgeCompat := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨hfr, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  refine ⟨hfr, (a₁ * a₂) • 𝒢P.wedge f, a₁ • M₁.model.wedge f₁, a₂ • M₂.model.wedge f₂, hs, hs0,
    hs₁, hs₁0, hs₂, hs₂0, hidx, ?_⟩
  intro τ Φ₁ Φ₂ h₁ hc₁ h₂ hc₂ c hc
  have hΦP := hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂
  have hjac := hJ K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ Φ₁ Φ₂ h₁ h₂ hΦP
    f₁ f₂ f hf1 hf2
  rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
  simp only [smul_eq_mul]
  ring

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization, with `ProductHodgeCompat` split.** -/
theorem heightAdditivity_of_metrization''' (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hJ : ZInQ.Metrization.JacDetMultilinear) (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) (hPJ : ZInQ.Metrization.ProductJacobian) :
    HeightAdditivity :=
  heightAdditivity_of_metrization'' hN1 h5 hU hH hUD hJ hN hPA
    (ZInQ.Metrization.productHodgeCompat_of (ZInQ.Metrization.productUniformization_of hPA)
      hPL hPJ)

end HSyn.G0Split

#print axioms ZInQ.Metrization.map_genericUnit_of_isMonHom
#print axioms ZInQ.Metrization.productHodgeCompat_of
#print axioms HSyn.G0Split.heightAdditivity_of_metrization'''
