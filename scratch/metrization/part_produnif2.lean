
/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

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

/-- **`ProductMetrizationGeo` from `ProductLocalStructure` and `ProductHodgeLattice`.** -/
theorem productMetrizationGeo_of_local (hLS : ProductLocalStructure)
    (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo :=
  productMetrizationGeo_of''' (productUniformizationAnalytic_of hLS) hPL

end ZInQ.Metrization

namespace HSyn.G0Split

/-- **`HeightAdditivity` after task metrization (final form, v3).** -/
theorem heightAdditivity_of_metrization_v3 (hN1 : ZInQ.H5Neron.NeronModelExists)
    (h5 : LeafAdopt.H5) (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)
    (hN : ZInQ.Metrization.JacDetNondegenerate)
    (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) : HeightAdditivity :=
  heightAdditivity_of_metrization_v2 hN1 h5 hU hH hUD hN
    (ZInQ.Metrization.productUniformizationAnalytic_of hLS) hPL

end HSyn.G0Split

#print axioms ZInQ.Metrization.productUniformizationAnalytic_of
#print axioms HSyn.G0Split.heightAdditivity_of_metrization_v3
