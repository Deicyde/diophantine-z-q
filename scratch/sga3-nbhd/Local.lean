import ZInQKernel.Contrib.OneProof.SGA3IdComp

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted

namespace SGA3Nbhd

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

/-- In the fibre `G_t` (subspace topology) of a smooth group scheme, the component of `e(t)` is open. -/
theorem isOpen_cc_fibre [Smooth G.hom] (t : S) (he : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ G.hom ⁻¹' {t}) :
    IsOpen (connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t})) := by
  let φ := G.hom.fiberHomeo t
  let φF := G.hom.fiberToSpecResidueField t
  have hsm : Smooth φF := show Smooth (pullback.snd G.hom (S.fromSpecResidueField t)) from inferInstance
  have hnb : ∀ y : G.hom ⁻¹' {t}, ∃ W : Set (G.hom ⁻¹' {t}), IsOpen W ∧ _root_.IsPreconnected W ∧ y ∈ W := by
    intro y
    obtain ⟨V, hVo, -, hVi, hyV⟩ := @SGA3IdComp.exists_irred_nbhd_of_smooth _ _ _ φF hsm (φ.symm y)
    refine ⟨φ '' V, φ.isOpenMap V hVo, hVi.2.isPreconnected.image _ φ.continuous.continuousOn, ?_⟩
    exact ⟨φ.symm y, hyV, φ.apply_symm_apply y⟩
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨W, hWo, hWc, hzW⟩ := hnb z
  refine ⟨W, ?_, hWo, hzW⟩
  rw [connectedComponent_eq hz]
  exact hWc.subset_connectedComponent hzW

/-- Over a closed point `t`, the points of `G_t` outside the identity component form a closed set of `G`. -/
theorem isClosed_fibre_diff [Smooth G.hom] (t : S) (ht : IsClosed ({t} : Set S)) :
    IsClosed (G.hom ⁻¹' {t} \ connectedComponentIn (G.hom ⁻¹' {t}) ((η[G] : 𝟙_ (Over S) ⟶ G).left t)) := by
  have he : (η[G] : 𝟙_ (Over S) ⟶ G).left t ∈ G.hom ⁻¹' {t} := SGA3IdComp.hom_e G t
  have hF : IsClosed (G.hom ⁻¹' {t}) := ht.preimage G.hom.continuous
  rw [connectedComponentIn_eq_image he]
  have : G.hom ⁻¹' {t} \ Subtype.val '' connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t}) =
      Subtype.val '' (connectedComponent (⟨_, he⟩ : G.hom ⁻¹' {t}))ᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact ⟨⟨x, hx⟩, fun h => hx' ⟨_, h, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rintro ⟨y', hy', hyy'⟩
      exact hy (Subtype.ext hyy' ▸ hy')
  rw [this]
  exact hF.isClosedMap_subtype_val _ (isOpen_cc_fibre G t he).isClosed_compl

/-- **`G⁰` is open when the fibres off a finite set of closed points are preconnected.** -/
theorem isOpen_idCompSet_of_finite [Smooth G.hom] (T : Set S) (hT : T.Finite)
    (hTc : ∀ t ∈ T, IsClosed ({t} : Set S))
    (hpre : ∀ t ∉ T, _root_.IsPreconnected (G.hom ⁻¹' {t})) : IsOpen (idCompSet G) := by
  have hc : (idCompSet G)ᶜ = ⋃ t ∈ T,
      (G.hom ⁻¹' {t} \ connectedComponentIn (G.hom ⁻¹' {t}) ((η[G] : 𝟙_ (Over S) ⟶ G).left t)) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff, Set.mem_preimage,
      Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      refine ⟨G.hom x, ?_, rfl, hx⟩
      by_contra hT'
      apply hx
      show x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G] : 𝟙_ (Over S) ⟶ G).left (G.hom x))
      exact (hpre _ hT').subset_connectedComponentIn (SGA3IdComp.hom_e G _) le_rfl rfl
    · rintro ⟨t, -, rfl, hx⟩
      exact hx
  rw [← isClosed_compl_iff, hc]
  exact hT.isClosed_biUnion fun t ht => isClosed_fibre_diff G t (hTc t ht)


/-- **Over a DVR**: `G⁰` is open as soon as the generic fibre is preconnected; the generic fibre is detected
by any field `F` with an injective `R → F` (`pullback G.hom (Spec F → Spec R)` maps onto it). -/
theorem isOpen_idCompSet_dvr {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [Smooth G.hom]
    {F : Type} [Field F] (φ : R →+* F) (hφ : Function.Injective φ)
    (hc : _root_.IsPreconnected
      (Set.univ : Set ↥(pullback (C := Scheme.{0}) G.hom (Spec.map (CommRingCat.ofHom φ))))) :
    IsOpen (idCompSet G) := by
  refine isOpen_idCompSet_of_finite G {IsLocalRing.closedPoint R} (Set.finite_singleton _) ?_ ?_
  · rintro t rfl
    exact IsLocalRing.isClosed_singleton_closedPoint R
  · intro t ht
    have ht0 : t.asIdeal = ⊥ := by
      by_contra h
      have hm : t.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h t.isPrime
      exact ht (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm))
    have hr : G.hom ⁻¹' {t} = Set.range (pullback.fst G.hom (Spec.map (CommRingCat.ofHom φ))) := by
      rw [Scheme.Pullback.range_fst]
      congr 1
      ext u
      simp only [Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro rfl
        refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F), ?_⟩
        apply PrimeSpectrum.ext
        rw [ht0]
        show Ideal.comap φ ⊥ = ⊥
        exact Ideal.comap_bot_of_injective _ hφ
      · rintro ⟨v, rfl⟩
        apply PrimeSpectrum.ext
        rw [ht0]
        have hv : v.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right v.isPrime.ne_top
        show Ideal.comap φ v.asIdeal = ⊥
        rw [hv]
        exact Ideal.comap_bot_of_injective _ hφ
    rw [hr, ← Set.image_univ]
    exact hc.image _ (pullback.fst G.hom (Spec.map (CommRingCat.ofHom φ))).continuous.continuousOn

open ReductSplit in
/-- **`G⁰` of a group model over a DVR is open** (`ReductSplit.GroupModelO`: smooth, generic fibre `≅ A`,
geometrically integral). No leaf: the special fibre is closed, its identity component is open in it, and
the generic fibre is connected. -/
theorem isOpen_idCompSet_groupModelO {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    [IsDiscreteValuationRing O] (𝒩 : GroupModelO A O) : IsOpen (idCompSet 𝒩.G) := by
  refine isOpen_idCompSet_dvr 𝒩.G (algebraMap O K) (FaithfulSMul.algebraMap_injective O K) ?_
  haveI : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  let e : pullback 𝒩.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O K))) ≅ A.X.left :=
    (Over.forget _).mapIso 𝒩.gen
  have h1 : _root_.IsPreconnected (Set.univ : Set A.X.left) :=
    (IrreducibleSpace.isIrreducible_univ _).2.isPreconnected
  have h2 := h1.image _ (Scheme.homeoOfIso e.symm).continuous.continuousOn
  rwa [Set.image_univ_of_surjective (Scheme.homeoOfIso e.symm).surjective] at h2

end SGA3Nbhd

#print axioms SGA3Nbhd.isOpen_idCompSet_groupModelO
#print axioms SGA3Nbhd.isOpen_idCompSet_of_finite
