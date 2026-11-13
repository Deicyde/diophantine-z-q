
/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

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

/-- **Glue (pure Mathlib): product lattices.** If `Λ₁ ⊂ ℂ^{g₁}`, `Λ₂ ⊂ ℂ^{g₂}` are full lattices,
so is `Λ₁ × Λ₂ ⊂ ℂ^{g₁+g₂}`, and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂` (the product of fundamental
domains is a fundamental domain; `volume` on `Fin (g₁+g₂) → ℂ` is the product measure under
`Fin.append`). STANDARD; provable from Mathlib, not yet proved. -/
def ProductLatticeFacts : Prop :=
  ∀ (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    [DiscreteTopology Λ₁] [DiscreteTopology Λ₂], IsZLattice ℝ Λ₁ → IsZLattice ℝ Λ₂ →
    ∃ (_ : DiscreteTopology (prodLattice Λ₁ Λ₂)) (_ : IsZLattice ℝ (prodLattice Λ₁ Λ₂)),
      ZLattice.covolume (prodLattice Λ₁ Λ₂) = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂

/-- **Glue (the product uniformization).** For an isomorphism `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` of
`𝓞_L`-schemes whose components are homomorphisms, and analytic uniformizations `Φᵢ` of `𝒢ᵢ(ℂ)_τ`
with kernels `Λᵢ`, `prodPts e Φ₁ Φ₂` is an analytic uniformization of `𝒢P(ℂ)_τ` with kernel
`Λ₁ × Λ₂`. Why true: the homomorphism, kernel and surjectivity clauses follow from `e` and the
universal property of `⊗` (points of a product are pairs of points); openness of `dom` and
holomorphy: a Zariski open of `𝒢₁ ×_{𝓞_L} 𝒢₂` is covered by basic opens `D(h)` of products
`Spec(R₁ ⊗ R₂)` of affine opens, and a regular function there is `a/hⁿ` with
`a, h ∈ R₁ ⊗_{𝓞_L} R₂`, i.e. sums of products of functions holomorphic along `Φ₁` resp. `Φ₂`
(STANDARD). Unproved (Mathlib lacks the affine-cover description of fibre products used here). -/
def ProductUniformization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂)

/-- **Glue (the Hodge line of a product, with its coefficient).** For `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` as in
`ProductUniformization` and metrizations `M₁`, `M₂` of `𝒢₁`, `𝒢₂`: `hodgeSpace (g₁+g₂)` of `𝒢P` is
an `L`-line, and there are nonzero `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` with
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]` such that, at every `τ`, every `τ`-semilinear map `c`
that sends wedges to the Jacobians of `prodPts e Φ₁ Φ₂` (for uniformizations `Φᵢ` computing `Mᵢ`'s
coefficients) has `c s = coeff₁(s₁) · coeff₂(s₂)`. Why true (STANDARD): take `s₁ = a₁ · 1⊗df₁`,
`s₂ = a₂ · 1⊗df₂` and `s = p₁*s₁ ∧ p₂*s₂ = a₁a₂ · 1 ⊗ d(p₁*f₁) ∧ d(p₂*f₂)`. Algebra: for the
smooth group scheme `𝒢₁ ×_{𝓞_L} 𝒢₂`, `e*Ω¹ = e₁*Ω¹ ⊕ e₂*Ω¹`, so `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` (and the
cotangent space at `ξ` is the direct sum, so `⋀^{g₁+g₂}` is the tensor product of the two lines);
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` in `⋀ω₁ ⊗ ⋀ω₂` is the product. Analysis:
`(p₁*f) ∘ prodPts = f ∘ Φ₁ ∘ leftBlock` near `0`, so the Jacobian matrix of `d(p₁*f₁) ∧ d(p₂*f₂)`
is block diagonal and `jacDet` is the product. Unproved (stalks and differentials of fibre products
of schemes are not in Mathlib). -/
def ProductHodgeCompat : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G), IsMonHom (e.hom ≫ fst _ _) →
    IsMonHom (e.hom ≫ snd _ _) →
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (s : 𝒢P.hodgeSpace (g₁ + g₂)) (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
      s ∈ 𝒢P.detLattice (g₁ + g₂) ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
      s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) s =
        secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
      ∀ (τ : L →+* ℂ) (Φ₁ : (Fin g₁ → ℂ) → M₁.model.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → M₂.model.Pts τ),
        M₁.model.IsAnalyticUniformization τ (M₁.hodge.periods τ) Φ₁ →
        (∀ f, M₁.hodge.coeff τ (M₁.model.wedge f) = M₁.model.jacDet Φ₁ f) →
        M₂.model.IsAnalyticUniformization τ (M₂.hodge.periods τ) Φ₂ →
        (∀ f, M₂.hodge.coeff τ (M₂.model.wedge f) = M₂.model.jacDet Φ₂ f) →
        ∀ c : 𝒢P.hodgeSpace (g₁ + g₂) →ₛₗ[τ] ℂ,
          (∀ f, c (𝒢P.wedge f) = 𝒢P.jacDet (prodPts e Φ₁ Φ₂) f) →
          c s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂

/-- **`ProductMetrizationGeo` from `JacDetDescends`, `ProductUniformization`,
`ProductLatticeFacts` and `ProductHodgeCompat` (proved).** `MP` has lattice `⋀^{g₁+g₂}ω_{𝒢P}`,
periods `Λ₁ × Λ₂` and coefficients from `prodPts e Φ₁ Φ₂`. -/
theorem productMetrizationGeo_of (hJ : JacDetDescends) (hPU : ProductUniformization)
    (hPL : ProductLatticeFacts) (hPC : ProductHodgeCompat) :
    ZInQ.G0HeightAdd.ProductMetrizationGeo := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  subst h₁ h₂
  obtain ⟨e, hfst, hsnd, -⟩ := hP
  obtain ⟨hfr, s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcoeff⟩ :=
    hPC K A B C L 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  choose Φ₁ hΦ₁ hc₁ using M₁.arch
  choose Φ₂ hΦ₂ hc₂ using M₂.arch
  have hΦP := fun τ => hPU K A B C L 𝒢P M₁.model M₂.model e hfst hsnd τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
    (hΦ₁ τ) (hΦ₂ τ)
  choose c hc using fun τ => hJ K C L 𝒢P τ (g₁ + g₂) _ _ (hΦP τ)
  have hlatf : ∀ τ : L →+* ℂ, ∃ (_ : DiscreteTopology
      (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)))
      (_ : IsZLattice ℝ (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ))),
      ZLattice.covolume (prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)) =
        ZLattice.covolume (M₁.hodge.periods τ) * ZLattice.covolume (M₂.hodge.periods τ) := by
    intro τ
    haveI := M₁.hodge.periods_discrete τ
    haveI := M₂.hodge.periods_discrete τ
    exact hPL g₁ g₂ _ _ (M₁.hodge.periods_isZLattice τ) (M₂.hodge.periods_isZLattice τ)
  choose hdisc hZ hcov using hlatf
  have hcs : ∀ τ, c τ s = M₁.hodge.coeff τ s₁ * M₂.hodge.coeff τ s₂ := fun τ =>
    hcoeff τ (Φ₁ τ) (Φ₂ τ) (hΦ₁ τ) (hc₁ τ) (hΦ₂ τ) (hc₂ τ) (c τ) (hc τ)
  have hc0 : ∀ τ, c τ ≠ 0 := by
    intro τ h0
    have h := hcs τ
    rw [h0, LinearMap.zero_apply] at h
    exact mul_ne_zero (M₁.hodge.coeff_apply_ne_zero τ hs₁0)
      (M₂.hodge.coeff_apply_ne_zero τ hs₂0) h.symm
  have hlat : ∃ t ∈ 𝒢P.detLattice (g₁ + g₂), t ≠ 0 ∧ secIndex (𝒢P.detLattice (g₁ + g₂)) t ≠ 0 :=
    ⟨s, hs, hs0, by
      rw [hidx]
      exact mul_ne_zero (M₁.hodge.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
        (M₂.hodge.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)⟩
  let MP : MetrizedModel C L (g₁ + g₂) :=
    { model := 𝒢P
      hodge :=
        { lattice := 𝒢P.detLattice (g₁ + g₂)
          finrank_eq_one := hfr
          isLattice := hlat
          periods := fun τ => prodLattice (M₁.hodge.periods τ) (M₂.hodge.periods τ)
          periods_discrete := hdisc
          periods_isZLattice := hZ
          coeff := c
          coeff_ne_zero := hc0 }
      lattice_eq := rfl
      arch := fun τ => ⟨prodPts e (Φ₁ τ) (Φ₂ τ), hΦP τ, hc τ⟩ }
  exact ⟨MP, s, s₁, s₂, rfl, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hcs, hcov⟩

end ZInQ.Metrization

#print axioms ZInQ.Metrization.productMetrizationGeo_of
