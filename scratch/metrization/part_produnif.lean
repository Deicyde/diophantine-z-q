
/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

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

/-- **`ProductUniformization` from `ProductUniformizationAnalytic` (proved).** -/
theorem productUniformization_of (h : ProductUniformizationAnalytic) : ProductUniformization := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  obtain ⟨hhom, hker, hsurj⟩ := prodPts_alg e hfst hsnd h₁ h₂
  obtain ⟨hopen, hdiff⟩ := h K A B C L 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hhom, hker, hsurj, hopen, hdiff⟩

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization, with `ProductUniformization` reduced to its
analytic half.** -/
theorem heightAdditivity_of_metrization' (hN1 : ZInQ.H5Neron.NeronModelExists) (h5 : LeafAdopt.H5)
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim) (hJ : ZInQ.Metrization.JacDetDescends)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) : HeightAdditivity :=
  heightAdditivity_of_metrization hN1 h5 hU hH hUD hJ hN
    (ZInQ.Metrization.productUniformization_of hPA) hPC

end HSyn.G0Split

#print axioms ZInQ.Metrization.prodPts_alg
#print axioms ZInQ.Metrization.productUniformization_of
#print axioms HSyn.G0Split.heightAdditivity_of_metrization'
