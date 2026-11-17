import ZInQKernel.Contrib.OneProof.PazukiInputs

/-! Development file for `CountablePointsDefinedOver` (pazuki-route). -/

set_option linter.style.haveILetI false

noncomputable section

namespace PazukiRouteCP

open CategoryTheory AlgebraicGeometry Limits Polynomial

/-- Copy of `PazukiRoute.CountablePointsDefinedOver`. -/
def CountablePointsDefinedOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (Z : Over (Spec (CommRingCat.of K))),
    LocallyOfFiniteType Z.hom →
    Set.Countable {x : Spec (CommRingCat.of ℂ) ⟶ Z.left | x ≫ Z.hom = Spec.map (CommRingCat.ofHom σ)} →
    ∀ x : Spec (CommRingCat.of ℂ) ⟶ Z.left, x ≫ Z.hom = Spec.map (CommRingCat.ofHom σ) →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (_ : σ'.comp (algebraMap K K') = σ) (y : Spec (CommRingCat.of K') ⟶ Z.left),
      y ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
        x = Spec.map (CommRingCat.ofHom σ') ≫ y

/-- `ℂ` under another name, to carry a second algebra structure. -/
def CTwo : Type := ℂ

/-- The polynomial ring over a countable field is countable. -/
theorem countable_polynomial (K : Type) [Field K] [Countable K] : Countable K[X] :=
  Function.Injective.countable (f := fun p : K[X] => p.toFinsupp) Polynomial.toFinsupp_injective

/-- Over a countable field `K ⊆ ℂ` (through `σ`), two elements of `ℂ` transcendental over `σ(K)` are conjugate
under a ring endomorphism of `ℂ` fixing `σ(K)` (both are part of transcendence bases of `ℂ` of the same
cardinality `#ℂ`). -/
theorem exists_ringHom_eval {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) (a c : ℂ)
    (ha : Function.Injective (eval₂RingHom σ a)) (hc : Function.Injective (eval₂RingHom σ c)) :
    ∃ τ : ℂ →+* ℂ, τ.comp σ = σ ∧ τ a = c := by
  letI fC : Field CTwo := inferInstanceAs (Field ℂ)
  letI : IsAlgClosed CTwo := inferInstanceAs (IsAlgClosed ℂ)
  let fa : K[X] →+* ℂ := eval₂RingHom σ a
  let fc : K[X] →+* CTwo := eval₂RingHom σ c
  letI ia : Algebra K[X] ℂ := fa.toAlgebra
  letI ic : Algebra K[X] CTwo := fc.toAlgebra
  haveI : FaithfulSMul K[X] ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 ha
  haveI : FaithfulSMul K[X] CTwo := (faithfulSMul_iff_algebraMap_injective _ _).2 hc
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K[X] ℂ
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K[X] CTwo
  haveI : Countable K[X] := countable_polynomial K
  have hR : Cardinal.mk K[X] ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hC' : Cardinal.aleph0 < Cardinal.mk CTwo := hC
  have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hC
  have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hC'
  have h12 : Cardinal.mk s = Cardinal.mk t := h1.symm.trans ((show Cardinal.mk ℂ = Cardinal.mk CTwo from rfl).trans h2)
  obtain ⟨e⟩ := Cardinal.eq.1 h12
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let E : Algebra.adjoin K[X] (Set.range ((↑) : s → ℂ)) ≃ₐ[K[X]]
      Algebra.adjoin K[X] (Set.range ((↑) : t → CTwo)) :=
    hs.1.aevalEquiv.symm.trans ((AlgEquiv.ofAlgHom (MvPolynomial.rename e) (MvPolynomial.rename e.symm)
      (by ext; simp) (by ext; simp)).trans ht.1.aevalEquiv)
  let τ : ℂ ≃+* CTwo := IsAlgClosure.equivOfEquiv ℂ CTwo E.toRingEquiv
  have key : ∀ p : K[X], τ (fa p) = fc p := by
    intro p
    have h := IsAlgClosure.equivOfEquiv_algebraMap ℂ CTwo E.toRingEquiv
      (algebraMap K[X] (Algebra.adjoin K[X] (Set.range ((↑) : s → ℂ))) p)
    rw [← IsScalarTower.algebraMap_apply] at h
    have h' : E.toRingEquiv (algebraMap K[X] (Algebra.adjoin K[X] (Set.range ((↑) : s → ℂ))) p) =
        algebraMap K[X] (Algebra.adjoin K[X] (Set.range ((↑) : t → CTwo))) p := E.commutes p
    rw [h', ← IsScalarTower.algebraMap_apply] at h
    exact h
  refine ⟨(τ : ℂ →+* CTwo), ?_, ?_⟩
  · ext k
    have h := key (Polynomial.C k)
    have h' : fa (Polynomial.C k) = σ k := Polynomial.eval₂_C σ a
    rw [h'] at h
    exact h.trans (Polynomial.eval₂_C σ c)
  · have h := key Polynomial.X
    have h' : fa Polynomial.X = a := Polynomial.eval₂_X σ a
    rw [h'] at h
    exact h.trans (Polynomial.eval₂_X σ c)

/-- Elements of `ℂ` algebraic over a countable `σ(K)` are countably many. -/
theorem countable_not_injective {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) :
    Set.Countable {c : ℂ | ¬ Function.Injective (eval₂RingHom σ c)} := by
  haveI : Countable K[X] := countable_polynomial K
  refine (Set.countable_iUnion (fun p : K[X] => Finset.countable_toSet ((p.map σ).roots.toFinset))).mono ?_
  intro c hc
  simp only [Set.mem_ofPred_eq, injective_iff_map_eq_zero, not_forall] at hc
  obtain ⟨p, hp0, hp⟩ := hc
  refine Set.mem_iUnion.2 ⟨p, ?_⟩
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp)]
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  exact hp0

/-- **If a finitely generated `K`-algebra `R` (`K` countable) has countably many `K`-homomorphisms to `ℂ`, every
value of every such homomorphism is algebraic over `σ(K)`.** -/
theorem not_injective_of_countable {K : Type} [Field K] [Countable K] (σ : K →+* ℂ) {R : Type} [CommRing R]
    (φK : K →+* R) (ψ : R →+* ℂ) (hψ : ψ.comp φK = σ)
    (hcount : Set.Countable {ψ' : R →+* ℂ | ψ'.comp φK = σ}) (r : R) :
    ¬ Function.Injective (eval₂RingHom σ (ψ r)) := by
  intro ha
  classical
  let T := {c : ℂ | Function.Injective (eval₂RingHom σ c)}
  have hT : ¬ T.Countable := by
    intro hT
    apply not_countable_complex
    have : (Set.univ : Set ℂ) = T ∪ {c : ℂ | ¬ Function.Injective (eval₂RingHom σ c)} := by
      ext c; simp [T, em]
    rw [this]
    exact hT.union (countable_not_injective σ)
  apply hT
  have hex : ∀ c ∈ T, ∃ τ : ℂ →+* ℂ, τ.comp σ = σ ∧ τ (ψ r) = c :=
    fun c hc => exists_ringHom_eval σ (ψ r) c ha hc
  let f : ℂ → (R →+* ℂ) := fun c => if hc : c ∈ T then (hex c hc).choose.comp ψ else ψ
  refine Set.MapsTo.countable_of_injOn (f := f) ?_ ?_ hcount
  · intro c hc
    simp only [Set.mem_ofPred_eq, f, hc, ↓reduceDIte]
    rw [RingHom.comp_assoc, hψ]
    exact (hex c hc).choose_spec.1
  · intro c hc c' hc' h
    have h1 := (hex c hc).choose_spec.2
    have h2 := (hex c' hc').choose_spec.2
    have h3 := congrArg (fun g : R →+* ℂ => g r) h
    simp only [f, hc, hc', ↓reduceDIte, RingHom.comp_apply] at h3
    rw [← h1, ← h2, h3]

/-- A number field is countable. -/
theorem countable_numberField (K : Type) [Field K] [NumberField K] : Countable K :=
  Function.Injective.countable (Module.finBasis ℚ K).equivFun.injective

/-- **`CountablePointsDefinedOver` (proved).** Take an affine open `U = Spec R` of `Z` containing the image of `x`
(`R` of finite type over `K`); `x` is `Spec ψ` for `ψ : R → ℂ` over `σ`; the `K`-homomorphisms `R → ℂ` over `σ` give
distinct points, so they are countably many and the values of `ψ` are algebraic over `σ(K)`
(`not_injective_of_countable`); the image `ψ(R)` is then a number field `K'` and `x` factors through `Spec K'`. -/
theorem countablePointsDefinedOver_proof : CountablePointsDefinedOver := by
  intro K _ _ σ Z hZ hS x hx
  haveI : Countable K := countable_numberField K
  let z : Z.left := x (IsLocalRing.closedPoint ℂ)
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have hxU : Set.range x ⊆ Set.range (Scheme.Opens.ι U) := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint ℂ), Scheme.Opens.range_ι]
    exact hzU
  let x₁ := IsOpenImmersion.lift (Scheme.Opens.ι U) x hxU
  have hx₁ : x₁ ≫ (Scheme.Opens.ι U) = x := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let g : Spec Γ(Z.left, U) ⟶ Spec (CommRingCat.of K) := e.inv ≫ (Scheme.Opens.ι U) ≫ Z.hom
  let φK : CommRingCat.of K ⟶ Γ(Z.left, U) := Spec.preimage g
  have hg : Spec.map φK = g := Spec.map_preimage g
  let ψ : Γ(Z.left, U) ⟶ CommRingCat.of ℂ := Spec.preimage (x₁ ≫ e.hom)
  have hψ' : Spec.map ψ = x₁ ≫ e.hom := Spec.map_preimage _
  have hxψ : x = Spec.map ψ ≫ e.inv ≫ (Scheme.Opens.ι U) := by
    rw [hψ', Category.assoc, e.hom_inv_id_assoc, hx₁]
  have hψK : φK ≫ ψ = CommRingCat.ofHom σ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hg, ← hx]
    simp only [g, hxψ, Category.assoc]
  have hψK' : ψ.hom.comp φK.hom = σ := by
    rw [← CommRingCat.hom_comp, hψK]; rfl
  haveI : LocallyOfFiniteType g := by
    simp only [g]; infer_instance
  have hft : φK.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hg]
    infer_instance
  -- the `K`-homomorphisms `R → ℂ` over `σ` are countably many
  have hcount : Set.Countable {ψ' : Γ(Z.left, U) →+* ℂ | ψ'.comp φK.hom = σ} := by
    refine Set.MapsTo.countable_of_injOn
      (f := fun ψ' => Spec.map (CommRingCat.ofHom ψ') ≫ e.inv ≫ (Scheme.Opens.ι U)) ?_ ?_ hS
    · intro ψ' hψ'
      change (Spec.map (CommRingCat.ofHom ψ') ≫ e.inv ≫ (Scheme.Opens.ι U)) ≫ Z.hom = _
      simp only [Category.assoc]
      change Spec.map (CommRingCat.ofHom ψ') ≫ g = _
      rw [← hg, ← Spec.map_comp]
      congr 1
      ext k
      exact congrArg (fun f : K →+* ℂ => f k) hψ'
    · intro ψ₁ _ ψ₂ _ h
      have h' := (cancel_mono (e.inv ≫ (Scheme.Opens.ι U))).1 h
      have h'' := Spec.map_injective h'
      exact congrArg CommRingCat.Hom.hom h''
  have halg : ∀ r, ¬ Function.Injective (eval₂RingHom σ (ψ r)) :=
    not_injective_of_countable σ φK.hom ψ.hom hψK' hcount
  -- the image field
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra K Γ(Z.left, U) := φK.hom.toAlgebra
  haveI : Algebra.FiniteType K Γ(Z.left, U) := hft
  let ψA : Γ(Z.left, U) →ₐ[K] ℂ :=
    { ψ.hom with commutes' := fun k => congrArg (fun f : K →+* ℂ => f k) hψK' }
  let S0 : Subalgebra K ℂ := ψA.range
  haveI : Algebra.FiniteType K S0 :=
    Algebra.FiniteType.of_surjective ψA.rangeRestrict ψA.rangeRestrict_surjective
  haveI : Algebra.IsIntegral K S0 := by
    constructor
    rintro ⟨_, ⟨r, rfl⟩⟩
    have h := halg r
    simp only [injective_iff_map_eq_zero, not_forall] at h
    obtain ⟨p, hp, hp0⟩ := h
    have hi : IsIntegral K (ψA r) := IsAlgebraic.isIntegral ⟨p, hp0, hp⟩
    exact (isIntegral_algHom_iff (S0.val) Subtype.val_injective).1 hi
  haveI : Module.Finite K S0 := Algebra.IsIntegral.finite
  have hfield : IsField S0 :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap K S0).injective).1 (Field.toIsField K)
  let E : IntermediateField K ℂ := S0.toIntermediateField' hfield
  have hE : E.toSubalgebra = S0 := toSubalgebra_toIntermediateField' S0 hfield
  haveI : Module.Finite K E := by
    change Module.Finite K E.toSubalgebra
    rw [hE]; infer_instance
  haveI : NumberField E := NumberField.of_module_finite K E
  have hmem : ∀ r, ψ r ∈ E := fun r => by
    change ψ r ∈ E.toSubalgebra
    rw [hE]; exact ⟨r, rfl⟩
  let ψE : Γ(Z.left, U) →+* E := ψ.hom.codRestrict E hmem
  have hψE : (E.val : E →+* ℂ).comp ψE = ψ.hom := rfl
  refine ⟨E, inferInstance, inferInstance, inferInstance, (E.val : E →+* ℂ), ?_,
    Spec.map (CommRingCat.ofHom ψE) ≫ e.inv ≫ (Scheme.Opens.ι U), ?_, ?_⟩
  · ext k; rfl
  · simp only [Category.assoc]
    change Spec.map (CommRingCat.ofHom ψE) ≫ g = _
    rw [← hg, ← Spec.map_comp]
    congr 1
    ext k
    change ψ (φK k) = σ k
    exact congrArg (fun f : K →+* ℂ => f k) hψK'
  · rw [hxψ]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 3

end PazukiRouteCP
