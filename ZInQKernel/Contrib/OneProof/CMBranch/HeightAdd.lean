import ZInQKernel.Contrib.OneProof.CMBranch
import ZInQKernel.OneProof.H.TailI
import ZInQKernel.Contrib.HeightBC.Main

/-! # cm-branch2: `HeightAdditivityUpper` proved (manuscript L620-621, "additivity")

`CMBranch.HeightAdditivityUpper` (`h_F(A × Z) ≤ h_F(A) + h_F(Z)`, the half of Faltings' additivity that the
chain did not need) follows from the definition of the stable height as an infimum over metrized models:
metrized models `M₁` of `A` and `M₂` of `Z` nearly realizing the two infima are base-changed to a common
number field (`G0StableBC.MetrizationBaseChange`, proved in the tree from `HodgeLineBaseChange`), and
their product is a metrized model of `P ≅ A × Z` with height `h(M₁) + h(M₂)` (`G0HeightAdd.ProductMetrization`).

`ProductMetrization` comes from task metrization's reduction (`scratch/metrization/part_prodgeo.lean`,
`part_prodlat.lean`, `part_produnif.lean`, `part_prodsplit.lean`, copied verbatim below into the namespace
`ZInQ.Metrization.CMB2`, with `AbVar` written `PkgI3.AbVar`): `ProductMetrizationGeo` from
`JacDetDescends`, `ProductUniformization`, `ProductLatticeFacts` and `ProductHodgeCompat`, all proved in the
tree or here, except `ProductHodgeLattice`, which unif-dims proved from `ProductCotangent`,
`TangentDimAtOrigin` (both proved) and T35 (`ZInQ.LeafPush2.UniformizationExists`, the chain's textbook
field `t35`). So `HeightAdditivityUpper` is proved from T35 alone.
-/

set_option maxHeartbeats 1000000

namespace HDec.ZInQ.Metrization.CMB2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings MeasureTheory

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
  ∀ (K : Type) [Field K] (A B C : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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
  ∀ (K : Type) [Field K] (A B C : PkgI3.AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
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

/-- `ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` over `ℝ`. -/
noncomputable def blockLinearEquiv (g₁ g₂ : ℕ) :
    (Fin (g₁ + g₂) → ℂ) ≃ₗ[ℝ] (Fin g₁ → ℂ) × (Fin g₂ → ℂ) where
  toFun z := (leftBlock g₁ g₂ z, rightBlock g₁ g₂ z)
  invFun p := Fin.append p.1 p.2
  map_add' z w := by ext <;> simp
  map_smul' c z := by ext <;> simp
  left_inv z := eq_of_blocks (by simp) (by simp)
  right_inv p := by ext <;> simp

/-- `blockLinearEquiv` preserves `volume`. -/
theorem measurePreserving_blockLinearEquiv (g₁ g₂ : ℕ) :
    MeasurePreserving (blockLinearEquiv g₁ g₂) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)
    (finSumFinEquiv (m := g₁) (n := g₂)).symm
  have h2 := (volume_measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin g₁ ⊕ Fin g₂ => ℂ)).symm
  have hc := h2.comp h1
  convert hc using 1
  funext z
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inl i : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.castAdd g₂ i) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl
  · simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.coe_sumPiEquivProdPi, Equiv.sumPiEquivProdPi_apply,
      MeasurableEquiv.coe_piCongrLeft]
    rw [show (Sum.inr j : Fin g₁ ⊕ Fin g₂) = finSumFinEquiv.symm (Fin.natAdd g₁ j) by simp,
      Equiv.piCongrLeft_apply_apply]
    rfl

/-- A full lattice has a measurable fundamental domain with unique translates, whose volume is
the covolume. -/
theorem exists_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    ∃ F : Set E, MeasurableSet F ∧ (∀ x, ∃! g : Λ, (g : E) + x ∈ F) ∧
      ZLattice.covolume Λ ν = ν.real F := by
  let b := Module.Free.chooseBasis ℤ Λ
  let b' := b.ofZLatticeBasis ℝ Λ
  have hspan : Submodule.span ℤ (Set.range b') = Λ := b.ofZLatticeBasis_span ℝ Λ
  refine ⟨ZSpan.fundamentalDomain b', ZSpan.fundamentalDomain_measurableSet b', fun x => ?_,
    ZLattice.covolume_eq_measure_fundamentalDomain Λ ν (ZLattice.isAddFundamentalDomain b ν)⟩
  obtain ⟨⟨v, hv⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b' x
  refine ⟨⟨v, hspan ▸ hv⟩, h1, fun w hw => ?_⟩
  have h3 := h2 ⟨w, hspan.symm ▸ w.2⟩ hw
  have h4 : (w : E) = v := congrArg Subtype.val h3
  exact Subtype.ext h4

/-- **`ProductLatticeFacts`, proved.** -/
theorem productLatticeFacts : ProductLatticeFacts := by
  intro g₁ g₂ Λ₁ Λ₂ _ _ hZ₁ hZ₂
  -- discreteness: inject into `Λ₁ × Λ₂`
  have hdisc : DiscreteTopology (prodLattice Λ₁ Λ₂) := by
    let f : prodLattice Λ₁ Λ₂ → Λ₁ × Λ₂ := fun z =>
      (⟨leftBlock g₁ g₂ z, z.2.1⟩, ⟨rightBlock g₁ g₂ z, z.2.2⟩)
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · refine Continuous.prodMk ?_ ?_
      · exact Continuous.subtype_mk
          ((leftBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
      · exact Continuous.subtype_mk
          ((rightBlock g₁ g₂).continuous_of_finiteDimensional.comp continuous_subtype_val) _
    · intro z w h
      have h1 := congrArg (fun p => (p.1 : Fin g₁ → ℂ)) h
      have h2 := congrArg (fun p => (p.2 : Fin g₂ → ℂ)) h
      exact Subtype.ext (eq_of_blocks h1 h2)
  -- full rank
  have hZ : IsZLattice ℝ (prodLattice Λ₁ Λ₂) := by
    refine ⟨?_⟩
    rw [eq_top_iff]
    rintro z -
    have hz : z = Fin.append (leftBlock g₁ g₂ z) 0 + Fin.append 0 (rightBlock g₁ g₂ z) :=
      eq_of_blocks (by funext i; simp) (by funext j; simp)
    rw [hz]
    refine Submodule.add_mem _ ?_ ?_
    · let ι₁ : (Fin g₁ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inl ℝ _ _
      have hι : ∀ x, ι₁ x = Fin.append x 0 := fun x => rfl
      have hle : (Submodule.span ℝ (Λ₁ : Set (Fin g₁ → ℂ))).map ι₁ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨x, hx, rfl⟩
        rw [hι]
        exact ⟨by simpa using hx, by simp [Submodule.zero_mem]⟩
      apply hle
      rw [hZ₁.span_top]
      exact ⟨leftBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
    · let ι₂ : (Fin g₂ → ℂ) →ₗ[ℝ] (Fin (g₁ + g₂) → ℂ) :=
        (blockLinearEquiv g₁ g₂).symm.toLinearMap ∘ₗ LinearMap.inr ℝ _ _
      have hι : ∀ y, ι₂ y = Fin.append 0 y := fun y => rfl
      have hle : (Submodule.span ℝ (Λ₂ : Set (Fin g₂ → ℂ))).map ι₂ ≤
          Submodule.span ℝ (prodLattice Λ₁ Λ₂ : Set (Fin (g₁ + g₂) → ℂ)) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨y, hy, rfl⟩
        rw [hι]
        exact ⟨by simp [Submodule.zero_mem], by simpa using hy⟩
      apply hle
      rw [hZ₂.span_top]
      exact ⟨rightBlock g₁ g₂ z, Submodule.mem_top, hι _⟩
  refine ⟨hdisc, hZ, ?_⟩
  -- covolume
  obtain ⟨F₁, hF₁m, hF₁u, hF₁c⟩ := exists_fd Λ₁ volume
  obtain ⟨F₂, hF₂m, hF₂u, hF₂c⟩ := exists_fd Λ₂ volume
  let φ := blockLinearEquiv g₁ g₂
  have hφm : Measurable φ := (measurePreserving_blockLinearEquiv g₁ g₂).measurable
  let F : Set (Fin (g₁ + g₂) → ℂ) := φ ⁻¹' (F₁ ×ˢ F₂)
  have hFd : IsAddFundamentalDomain (prodLattice Λ₁ Λ₂) F volume := by
    refine IsAddFundamentalDomain.mk' ((hφm (hF₁m.prod hF₂m)).nullMeasurableSet) fun z => ?_
    obtain ⟨a, ha, hau⟩ := hF₁u (leftBlock g₁ g₂ z)
    obtain ⟨b, hb, hbu⟩ := hF₂u (rightBlock g₁ g₂ z)
    refine ⟨⟨Fin.append (a : Fin g₁ → ℂ) (b : Fin g₂ → ℂ),
      mem_prodLattice.mpr ⟨by simpa using a.2, by simpa using b.2⟩⟩, ?_, fun w hw => ?_⟩
    · beta_reduce
      rw [Submodule.vadd_def, vadd_eq_add]
      show (leftBlock g₁ g₂ _, rightBlock g₁ g₂ _) ∈ F₁ ×ˢ F₂
      simpa using ⟨ha, hb⟩
    · beta_reduce at hw
      rw [Submodule.vadd_def, vadd_eq_add] at hw
      have hw' : (leftBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z),
          rightBlock g₁ g₂ ((w : Fin (g₁ + g₂) → ℂ) + z)) ∈ F₁ ×ˢ F₂ := hw
      simp only [map_add, Set.mem_prod] at hw'
      have e1 := hau ⟨leftBlock g₁ g₂ w, w.2.1⟩ hw'.1
      have e2 := hbu ⟨rightBlock g₁ g₂ w, w.2.2⟩ hw'.2
      apply Subtype.ext
      apply eq_of_blocks
      · simpa using congrArg Subtype.val e1
      · simpa using congrArg Subtype.val e2
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hFd, hF₁c, hF₂c,
    (measurePreserving_blockLinearEquiv g₁ g₂).measureReal_preimage
      (hF₁m.prod hF₂m).nullMeasurableSet,
    Measure.volume_eq_prod, measureReal_def, measureReal_def, measureReal_def,
    Measure.prod_prod, ENNReal.toReal_mul]


/-- **`ProductUniformization` from `ProductUniformizationAnalytic` (proved).** -/
theorem productUniformization_of (h : ProductUniformizationAnalytic) : ProductUniformization := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  obtain ⟨hhom, hker, hsurj⟩ := prodPts_alg e hfst hsnd h₁ h₂
  obtain ⟨hopen, hdiff⟩ := h K A B C L 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  exact ⟨hhom, hker, hsurj, hopen, hdiff⟩


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


end HDec.ZInQ.Metrization.CMB2

namespace HDec.CMBranch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`ProductMetrization` (P2a) from T35** (task metrization's reduction; every other input is proved
in the tree). -/
theorem productMetrization_of_t35 (hT35 : _root_.ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.G0HeightAdd.ProductMetrization :=
  ZInQ.G0HeightAdd.productMetrization_of_geo
    (ZInQ.Metrization.CMB2.productMetrizationGeo_of ZInQ.Metrization.jacDetDescends
      (ZInQ.Metrization.CMB2.productUniformization_of
        (ZInQ.Metrization.productUniformizationAnalytic_of
          ZInQ.Metrization2.productLocalStructure))
      ZInQ.Metrization.CMB2.productLatticeFacts
      (ZInQ.Metrization.CMB2.productHodgeCompat_of
        (ZInQ.Metrization.CMB2.productUniformization_of
          (ZInQ.Metrization.productUniformizationAnalytic_of
            ZInQ.Metrization2.productLocalStructure))
        (ZInQ.UnifDims.productHodgeLattice_of_cotangent ZInQ.UnifDims.productCotangent
          HSyn.tangentDimAtOrigin_proved3 hT35)
        ZInQ.Metrization.productJacobian))

/-- **`MetrizationBaseChange`, proved** (the chain's `HodgeLineBaseChange`, as in `CMBranch/Open4.lean`). -/
theorem metrizationBaseChange_proved : G0StableBC.MetrizationBaseChange :=
  G0StableBC.metrizationBaseChange_of_hodgeLine
    (_root_.ZInQ.HeightBC.g0_hodgeLine_iff.mpr (_root_.ZInQ.HeightBC.hodgeLineBaseChange_of_glue4
      HSyn.hodgeBCInjective_proved3 HSyn.cotangentSpanBC_proved HSyn.omegaBaseChange_proved3
      HSyn.uniformizationLiftAnalytic_proved))

open _root_.ZInQ.DefFaltings in
/-- **`HeightAdditivityUpper` from `ProductMetrization` and `MetrizationBaseChange`.** For `ε > 0` choose
metrized models `M₁` of `A` (over `E₁`) and `M₂` of `Z` (over `E₂`) with heights `< a + ε/2`, `< z + ε/2`;
base-change both to a compositum `L'` (same heights); the product group model of `P ≅ A × Z` over `L'`
(`H5Neron.productGroupModelExists`) carries a metrization of height `h(M₁) + h(M₂)`, so `p < a + z + ε`. -/
theorem heightAdditivityUpper_of (hPM : ZInQ.G0HeightAdd.ProductMetrization)
    (hMBC : G0StableBC.MetrizationBaseChange) : HeightAdditivityUpper := by
  intro L _ _ P A Z hprod a z p ha hz hp
  obtain ⟨p₁, p₂, h₁, h₂, hiso⟩ := hprod
  have hfst : IsMonHom ((asIso (lift p₁ p₂)).hom ≫ fst A.X Z.X) := by
    rw [asIso_hom, CartesianMonoidalCategory.lift_fst]; exact h₁
  have hsnd : IsMonHom ((asIso (lift p₁ p₂)).hom ≫ snd A.X Z.X) := by
    rw [asIso_hom, CartesianMonoidalCategory.lift_snd]; exact h₂
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hA : stableFaltingsHeight A < ((a + ε / 2 : ℝ) : EReal) := by
    rw [ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hZ : stableFaltingsHeight Z < ((z + ε / 2 : ℝ) : EReal) := by
    rw [hz]; exact EReal.coe_lt_coe_iff.mpr (by linarith)
  unfold stableFaltingsHeight at hA hZ
  obtain ⟨E₁, hE₁⟩ := iInf_lt_iff.mp hA
  obtain ⟨g₁, hg₁⟩ := iInf_lt_iff.mp hE₁
  obtain ⟨M₁, hM₁⟩ := iInf_lt_iff.mp hg₁
  obtain ⟨E₂, hE₂⟩ := iInf_lt_iff.mp hZ
  obtain ⟨g₂, hg₂⟩ := iInf_lt_iff.mp hE₂
  obtain ⟨M₂, hM₂⟩ := iInf_lt_iff.mp hg₂
  have hM₁' : M₁.hodge.modelHeight < a + ε / 2 := EReal.coe_lt_coe_iff.mp hM₁
  have hM₂' : M₂.hodge.modelHeight < z + ε / 2 := EReal.coe_lt_coe_iff.mp hM₂
  obtain ⟨L', i1, i2, i3, i4, i5, t1, t2⟩ := _root_.ZInQ.H5Neron.compositum L E₁.L E₂.L
  obtain ⟨𝒢₁, h𝒢₁⟩ := G0StableBC.groupModelBaseChangeExists L A E₁.L L' M₁.model
  obtain ⟨N₁, ψ₁, hN₁, hψ₁⟩ := hMBC L A E₁.L L' M₁.model 𝒢₁ h𝒢₁ g₁ M₁ rfl
  obtain ⟨𝒢₂, h𝒢₂⟩ := G0StableBC.groupModelBaseChangeExists L Z E₂.L L' M₂.model
  obtain ⟨N₂, ψ₂, hN₂, hψ₂⟩ := hMBC L Z E₂.L L' M₂.model 𝒢₂ h𝒢₂ g₂ M₂ rfl
  have hh₁ := G0StableBC.modelHeight_eq_of_isHodgeBaseChange M₁.hodge N₁.hodge ψ₁ hψ₁
  have hh₂ := G0StableBC.modelHeight_eq_of_isHodgeBaseChange M₂.hodge N₂.hodge ψ₂ hψ₂
  obtain ⟨𝒢P, h𝒢P⟩ := _root_.ZInQ.H5Neron.productGroupModelExists L A Z P (asIso (lift p₁ p₂))
    hfst hsnd L' 𝒢₁ 𝒢₂
  obtain ⟨MP, -, hMP⟩ := hPM L A Z P (asIso (lift p₁ p₂)) L' 𝒢P 𝒢₁ 𝒢₂ h𝒢P g₁ g₂ N₁ N₂ hN₁ hN₂
  have hle := stableFaltingsHeight_le P MP
  rw [hp] at hle
  have hp' : p ≤ MP.hodge.modelHeight := EReal.coe_le_coe_iff.mp hle
  linarith

/-- **`HeightAdditivityUpper` from T35** (`UniformizationExists`, the chain's textbook field `t35`). -/
theorem heightAdditivityUpper_of_t35 (hT35 : _root_.ZInQ.LeafPush2.UniformizationExists) :
    HeightAdditivityUpper :=
  heightAdditivityUpper_of (productMetrization_of_t35 hT35) metrizationBaseChange_proved

end HDec.CMBranch
