import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: analytic uniformizations transport along generic isomorphisms

`isAnalyticUniformization_comp`: if `f : 𝒢 → 𝒩` is a homomorphism of group models that is an
isomorphism on generic fibres and `Φ : ℂ^g → 𝒢(ℂ)_τ` is an analytic uniformization with period
lattice `Λ`, then `z ↦ Φ(z) ≫ f` is an analytic uniformization of `𝒩(ℂ)_τ` with the same `Λ`.
This is the archimedean half of the glue `HeightAntitone` (all except the Jacobian determinants,
which depend on the germ comparison along `f`). Includes `Pts.lean`. -/

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- `ptC τ = Over.map (jL L) (Spec ℂ over L via τ)`. -/
noncomputable def ptCIso (τ : L →+* ℂ) :
    GroupModel.ptC (L := L) τ ≅ (Over.map (jL L)).obj (Over.mk (Spec.map (CommRingCat.ofHom τ))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- Complex points of a group model are complex points of its generic fibre. -/
noncomputable def ptsEquiv (𝒢 : GroupModel A L) (τ : L →+* ℂ) :
    𝒢.Pts τ ≃ (Over.mk (Spec.map (CommRingCat.ofHom τ)) ⟶ (Over.pullback (jL L)).obj 𝒢.G) :=
  ((ptCIso τ).homCongr (Iso.refl 𝒢.G)).trans ((Over.mapPullbackAdj (jL L)).homEquiv _ _)

theorem ptsEquiv_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    ptsEquiv 𝒩 τ (p ≫ f) = ptsEquiv 𝒢 τ p ≫ (Over.pullback (jL L)).map f := by
  simp only [ptsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **A morphism of group models that is an isomorphism on generic fibres is bijective on
complex points** (at every `τ : L → ℂ`). -/
theorem pts_comp_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) :
    Function.Bijective (fun p : 𝒢.Pts τ => p ≫ f) := by
  have key : (fun p : 𝒢.Pts τ => p ≫ f) = (ptsEquiv 𝒩 τ).symm ∘
      (fun q => q ≫ (Over.pullback (jL L)).map f) ∘ ptsEquiv 𝒢 τ := by
    funext p
    simp only [Function.comp, ← ptsEquiv_comp, Equiv.symm_apply_apply]
  rw [key]
  refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
  exact ⟨fun a b h => (cancel_mono _).mp h, fun c => ⟨c ≫ inv ((Over.pullback (jL L)).map f),
    by simp⟩⟩


/-- Values of regular functions along a morphism: `s(p ≫ f) = (f^* s)(p)`. -/
theorem evalAt_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (U : 𝒩.G.left.Opens) (s : Γ(𝒩.G.left, U)) :
    𝒩.evalAt (p ≫ f) U s = 𝒢.evalAt p (f.left ⁻¹ᵁ U) (f.left.app U s) := by
  unfold GroupModel.evalAt
  by_cases h : ⊤ ≤ p.left ⁻¹ᵁ (f.left ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (p ≫ f).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem dom_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) {τ : L →+* ℂ} {g : ℕ}
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (U : 𝒩.G.left.Opens) :
    𝒩.dom (fun z => Φ z ≫ f) U = 𝒢.dom Φ (f.left ⁻¹ᵁ U) := rfl

/-- **Analytic uniformizations transport along generic isomorphisms** (proved). -/
theorem isAnalyticUniformization_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (h : 𝒢.IsAnalyticUniformization τ Λ Φ) :
    𝒩.IsAnalyticUniformization τ Λ (fun z => Φ z ≫ f) := by
  obtain ⟨hmul, hker, hsurj, hopen, hdiff⟩ := h
  have hb := pts_comp_bijective 𝒢 𝒩 f τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z w
    simp only
    rw [hmul, MonObj.mul_comp]
  · intro z
    rw [← hker z]
    constructor
    · intro h1
      apply hb.1
      have h1' : Φ z ≫ f = 1 := h1
      show Φ z ≫ f = 1 ≫ f
      rw [h1', MonObj.one_comp]
    · intro h1
      simp only
      rw [h1, MonObj.one_comp]
  · intro q
    obtain ⟨p, rfl⟩ := hb.2 q
    obtain ⟨z, rfl⟩ := hsurj p
    exact ⟨z, rfl⟩
  · intro U
    rw [dom_comp]
    exact hopen _
  · intro U s
    rw [dom_comp]
    simp only [evalAt_comp]
    exact hdiff _ _


/-- A homomorphism of group models sends `ξ_𝒢` to `ξ_𝒩` (as in `Stalk.lean`). -/
theorem map_genericUnit' (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    f.left 𝒢.genericUnit = 𝒩.genericUnit := by
  have h : 𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
    have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
    exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this
  have h2 := congrArg (fun φ => φ (genericPt L)) h
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h2

/-! ### Jacobian determinants along a generic isomorphism -/

/-- Restriction does not change values at points that land in the smaller open. -/
theorem evalAt_res (𝒢 : GroupModel A L) {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens}
    (i : W ⟶ U) (hp : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U s = 𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) := by
  unfold GroupModel.evalAt
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hp.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  rw [dif_pos hU, dif_pos hp]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The point `Spec ℂ → Spec 𝓞_L` (through `τ`) is the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : PrimeSpectrum ℂ) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  change PrimeSpectrum.comap (τ.comp (algebraMap (𝓞 L) L)) x = _
  haveI := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  show τ (algebraMap (𝓞 L) L a) ∈ x.asIdeal ↔ a ∈ (⊥ : Ideal (𝓞 L))
  rw [hx, Ideal.mem_bot, Ideal.mem_bot, map_eq_zero_iff _ τ.injective]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞 L) L)

/-- The unit complex point lands in every open containing `ξ`. -/
theorem one_mem_dom (𝒢 : GroupModel A L) (τ : L →+* ℂ) {W : 𝒢.G.left.Opens}
    (hW : 𝒢.genericUnit ∈ W) : ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x ∈ W
  rw [Over.comp_left, Scheme.Hom.comp_apply]
  show (η[𝒢.G] : 𝟙_ _ ⟶ 𝒢.G).left ((GroupModel.ptC τ).hom x) ∈ W
  have hx : (GroupModel.ptC (L := L) τ).hom x = genericPt L := ptC_hom_apply τ x
  rw [hx]
  exact hW

/-- `Φ(0) = 1` for a homomorphism `Φ`. -/
theorem map_zero_of_hom {G : Type*} [Group G] {g : ℕ} (Φ : (Fin g → ℂ) → G)
    (h : ∀ z w, Φ (z + w) = Φ z * Φ w) : Φ 0 = 1 := by
  have := h 0 0
  rw [add_zero] at this
  exact (mul_eq_left.mp this.symm)

/-- **The germ along `Φ ≫ f` of `t` agrees near `0` with the germ along `Φ` of `φ(t)`**, for any
map `φ : 𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` compatible with `f^*` on sections (the stalk map of `f`). -/
theorem germAlong_comp_eventuallyEq (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : 𝒩.genStalk) :
    𝒩.germAlong (fun z => Φ z ≫ f) t =ᶠ[nhds 0] 𝒢.germAlong Φ (φ t) := by
  obtain ⟨hmul, -, -, hopen, -⟩ := hΦ
  set U := (𝒩.exists_rep t).choose
  set m := (𝒩.exists_rep t).choose_spec.choose
  set s := (𝒩.exists_rep t).choose_spec.choose_spec.choose
  have hs : 𝒩.G.left.presheaf.germ U 𝒩.genericUnit m s = t :=
    (𝒩.exists_rep t).choose_spec.choose_spec.choose_spec
  have hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U := by
    show f.left 𝒢.genericUnit ∈ U
    rw [map_genericUnit' 𝒢 𝒩 f]; exact m
  set U' := (𝒢.exists_rep (φ t)).choose
  set m' := (𝒢.exists_rep (φ t)).choose_spec.choose
  set s' := (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose
  have hs' : 𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' = φ t :=
    (𝒢.exists_rep (φ t)).choose_spec.choose_spec.choose_spec
  have heq : 𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) =
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' := by
    rw [hs', ← hs, hφ U m hx' s]
  obtain ⟨W, mW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq _ _ hx' m' _ _ heq
  have hnhds : 𝒢.dom Φ W ∈ nhds (0 : Fin g → ℂ) := by
    refine (hopen W).mem_nhds ?_
    show ⊤ ≤ (Φ 0).left ⁻¹ᵁ W
    rw [map_zero_of_hom Φ hmul]
    exact one_mem_dom 𝒢 τ mW
  filter_upwards [hnhds] with z hz
  show 𝒩.evalAt (Φ z ≫ f) U s = 𝒢.evalAt (Φ z) U' s'
  rw [evalAt_comp, evalAt_res 𝒢 (Φ z) iU hz, hW, ← evalAt_res 𝒢 (Φ z) iV hz]

/-- **Jacobian determinants along a generic isomorphism** (proved): with `φ` as above,
`jacDet (Φ ≫ f) t = jacDet Φ (φ ∘ t)`. -/
theorem jacDet_comp_map (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (φ : 𝒩.genStalk → 𝒢.genStalk)
    (hφ : ∀ (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
      (s : Γ(𝒩.G.left, U)), φ (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
        𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s))
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (ht : ∀ i, (t' i : 𝒢.genStalk) = φ (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' := by
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [(germAlong_comp_eventuallyEq 𝒢 𝒩 f Λ Φ hΦ φ hφ (t i)).fderiv_eq, ht i]

/-- The comparison `𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}` along a homomorphism `f` (`f(ξ_𝒢) = ξ_𝒩`). -/
noncomputable def genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.genStalk ⟶ 𝒢.genStalk :=
  𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes ≫
    f.left.stalkMap 𝒢.genericUnit

/-- `genMap` is `f^*` on germs. -/
theorem genMap_germ (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (U : 𝒩.G.left.Opens) (hx : 𝒩.genericUnit ∈ U) (hx' : 𝒢.genericUnit ∈ f.left ⁻¹ᵁ U)
    (s : Γ(𝒩.G.left, U)) : (genMap 𝒢 𝒩 f) (𝒩.G.left.presheaf.germ U 𝒩.genericUnit hx s) =
      𝒢.G.left.presheaf.germ (f.left ⁻¹ᵁ U) 𝒢.genericUnit hx' (f.left.app U s) := by
  unfold genMap
  rw [CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- **Jacobian determinants along a homomorphism**, with the stalk map (proved). -/
theorem jacDet_comp_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    {τ : L →+* ℂ} {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk)
    (t' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (ht : ∀ i, (t' i : 𝒢.genStalk) = genMap 𝒢 𝒩 f (t i)) :
    𝒩.jacDet (fun z => Φ z ≫ f) t = 𝒢.jacDet Φ t' :=
  jacDet_comp_map 𝒢 𝒩 f Λ Φ hΦ (genMap 𝒢 𝒩 f) (genMap_germ 𝒢 𝒩 f) t t' ht

/-! ### The induced map on cotangent spaces -/

theorem isIso_stalkSpecializes_genMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    IsIso (𝒩.G.left.presheaf.stalkSpecializes
      (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes) :=
  Iso.isIso_hom (𝒩.G.left.presheaf.stalkCongr (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).symm)

theorem genMap_mem_maximalIdeal (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : 𝒩.genStalk) (ht : t ∈ IsLocalRing.maximalIdeal 𝒩.genStalk) :
    genMap 𝒢 𝒩 f t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  haveI := isIso_stalkSpecializes_genMap 𝒢 𝒩 f
  set e := 𝒩.G.left.presheaf.stalkSpecializes
    (Inseparable.of_eq (map_genericUnit' 𝒢 𝒩 f)).specializes
  have h1 : e t ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    intro hu
    apply ht
    have := hu.map (inv e).hom
    rwa [← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply] at this
  have h2 := map_nonunit (f.left.stalkMap 𝒢.genericUnit).hom _ h1
  exact h2

/-- `genMap` is compatible with the structure maps from `𝓞_L`. -/
theorem genMap_structMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (r : 𝓞 L) :
    genMap 𝒢 𝒩 f (𝒩.structMap r) = 𝒢.structMap r := by
  have e1 : 𝒩.structMap r = 𝒩.G.left.presheaf.germ ⊤ 𝒩.genericUnit trivial
      (𝒩.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  have e2 : 𝒢.structMap r = 𝒢.G.left.presheaf.germ ⊤ 𝒢.genericUnit trivial
      (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv r)) := rfl
  rw [e1, e2, genMap_germ 𝒢 𝒩 f ⊤ (show 𝒩.genericUnit ∈ (⊤ : 𝒩.G.left.Opens) from trivial)
    (show 𝒢.genericUnit ∈ f.left ⁻¹ᵁ (⊤ : 𝒩.G.left.Opens) from trivial)]
  have hw : f.left ≫ 𝒩.G.hom = 𝒢.G.hom := Over.w f
  have : 𝒢.G.hom.appTop = 𝒩.G.hom.appTop ≫ f.left.appTop := by
    rw [← hw, Scheme.Hom.comp_appTop]
  rw [this, CommRingCat.comp_apply]
  rfl

/-- **The induced `𝓞_L`-linear map `ω_{𝒩_L} → ω_{𝒢_L}` on cotangent spaces at `ξ`** (`f^*`). -/
noncomputable def cotMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒩.cotangent →ₗ[𝓞 L] 𝒢.cotangent where
  toFun x := Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
    (IsLocalRing.maximalIdeal 𝒢.genStalk) (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    (fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht) x
  map_add' x y := map_add _ x y
  map_smul' r x := by
    obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ x
    let ψ := (genMap 𝒢 𝒩 f).hom.toIntAlgHom
    have h : IsLocalRing.maximalIdeal 𝒩.genStalk ≤
        (IsLocalRing.maximalIdeal 𝒢.genStalk).comap ψ :=
      fun t ht => genMap_mem_maximalIdeal 𝒢 𝒩 f t ht
    change Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (𝒩.structMap r • Ideal.toCotangent _ m) =
      𝒢.structMap r • Ideal.mapCotangent (IsLocalRing.maximalIdeal 𝒩.genStalk)
        (IsLocalRing.maximalIdeal 𝒢.genStalk) ψ h (Ideal.toCotangent _ m)
    rw [← (Ideal.toCotangent _).map_smul, Ideal.mapCotangent_toCotangent,
      Ideal.mapCotangent_toCotangent, ← (Ideal.toCotangent _).map_smul]
    congr 1
    apply Subtype.ext
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, ψ, RingHom.toIntAlgHom_apply]
    rw [genMap_structMap]

theorem cotMap_dCls (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (t : IsLocalRing.maximalIdeal 𝒩.genStalk) :
    cotMap 𝒢 𝒩 f (𝒩.dCls t) =
      𝒢.dCls ⟨genMap 𝒢 𝒩 f t, genMap_mem_maximalIdeal 𝒢 𝒩 f t t.2⟩ := rfl

/-! ### `f^*` maps `ω_𝒩` into `ω_𝒢` (step R1) -/

theorem stalkSpecializes_stalkSpecializes_apply {X : Scheme.{0}} {x y z : X} (h : x ⤳ y)
    (h' : y ⤳ z) (t : X.presheaf.stalk z) :
    X.presheaf.stalkSpecializes h (X.presheaf.stalkSpecializes h' t) =
      X.presheaf.stalkSpecializes (h.trans h') t := by
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]

theorem stalkSpecializes_self_apply {X : Scheme.{0}} {x : X} (h : x ⤳ x)
    (t : X.presheaf.stalk x) : X.presheaf.stalkSpecializes h t = t := by
  rw [show h = specializes_refl x from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

theorem unitSection_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] :
    𝒢.unitSection ≫ f.left = 𝒩.unitSection := by
  have := congrArg CommaMorphism.left (IsMonHom.one_hom (f := f))
  exact (Over.comp_left (f := η[𝒢.G]) (g := f)).symm.trans this

/-- At each point `s` of `Spec 𝓞_L`, `f^*` maps the local lattice `(ω_𝒩)_s` into `(ω_𝒢)_s`. -/
theorem cotMap_omegaAt (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f]
    (s : Spec (CommRingCat.of (𝓞 L))) (m : 𝒩.cotangent) (hm : m ∈ 𝒩.omegaAt s) :
    cotMap 𝒢 𝒩 f m ∈ 𝒢.omegaAt s := by
  have hE := unitSection_comp 𝒢 𝒩 f
  have hp : f.left (𝒢.unitSection s) = 𝒩.unitSection s :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg (fun φ => φ s) hE)
  let T := 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).specializes
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, hmem, rfl⟩ := hx
    set g' := f.left.stalkMap (𝒢.unitSection s) (T g)
    have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' =
        genMap 𝒢 𝒩 f (𝒩.G.left.presheaf.stalkSpecializes (𝒩.specializes_genericUnit s) g) := by
      rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
      unfold genMap
      rw [CommRingCat.comp_apply]
      congr 1
      rw [stalkSpecializes_stalkSpecializes_apply, stalkSpecializes_stalkSpecializes_apply]
    have hker : g' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
      rw [RingHom.mem_ker]
      have h1 := Scheme.Hom.stalkMap_comp 𝒢.unitSection f.left s
      have h2 := Scheme.Hom.stalkMap_congr_hom _ _ hE s
      have h1' : (𝒢.unitSection.stalkMap s) g' = ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h1
        exact this.symm
      have h2' : ((𝒢.unitSection ≫ f.left).stalkMap s) (T g) =
          (𝒩.unitSection.stalkMap s) ((𝒩.G.left.presheaf.stalkCongr
            (Inseparable.of_eq (hE ▸ rfl))).hom (T g)) := by
        have := congrArg (fun φ => (ConcreteCategory.hom φ) (T g)) h2
        exact this
      rw [h1', h2']
      have h4 : ∀ y : 𝒩.G.left.presheaf.stalk (𝒩.unitSection s), y = g →
          (𝒩.unitSection.stalkMap s) y = 0 := by
        rintro y rfl; exact hg
      apply h4
      show 𝒩.G.left.presheaf.stalkSpecializes (Inseparable.of_eq hp).symm.specializes (T g) = g
      exact (stalkSpecializes_stalkSpecializes_apply _ _ g).trans (stalkSpecializes_self_apply _ g)
    have hmem' : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) g' ∈
        IsLocalRing.maximalIdeal 𝒢.genStalk := by
      rw [hspec]; exact genMap_mem_maximalIdeal 𝒢 𝒩 f _ hmem
    apply Submodule.subset_span
    refine ⟨g', hker, hmem', ?_⟩
    rw [cotMap_dCls]
    congr 1
    exact Subtype.ext hspec.symm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-- **Step R1: `f^* (ω_𝒩) ⊆ ω_𝒢`** (proved). -/
theorem cotMap_omega (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (m : 𝒩.cotangent)
    (hm : m ∈ 𝒩.omega) : cotMap 𝒢 𝒩 f m ∈ 𝒢.omega := by
  rw [GroupModel.omega, Submodule.mem_iInf] at hm ⊢
  exact fun s => cotMap_omegaAt 𝒢 𝒩 f s m (hm s)

/-! ### The map of Hodge lines (step R2, lattice part) -/

/-- `L ⊗ ⋀^g f^* : 𝒩.hodgeSpace g → 𝒢.hodgeSpace g`, `L`-linear. -/
noncomputable def hodgeMap (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ) :
    𝒩.hodgeSpace g →ₗ[L] 𝒢.hodgeSpace g :=
  (exteriorPower.map g (cotMap 𝒢 𝒩 f)).baseChange L

theorem hodgeMap_wedge (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (v : Fin g → 𝒩.cotangent) :
    hodgeMap 𝒢 𝒩 f g ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g v) =
      (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => cotMap 𝒢 𝒩 f (v i)) := by
  rw [hodgeMap, LinearMap.baseChange_tmul, exteriorPower.map_apply_ιMulti]
  rfl

/-- **`L ⊗ ⋀^g f^*` maps `⋀^g ω_𝒩` into `⋀^g ω_𝒢`** (proved, from R1). -/
theorem hodgeMap_detLattice (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] (g : ℕ)
    (x : 𝒩.hodgeSpace g) (hx : x ∈ 𝒩.detLattice g) : hodgeMap 𝒢 𝒩 f g x ∈ 𝒢.detLattice g := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    rw [hodgeMap_wedge]
    apply Submodule.subset_span
    exact ⟨fun i => ⟨cotMap 𝒢 𝒩 f (v i), cotMap_omega 𝒢 𝒩 f _ (v i).2⟩, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul L r y, LinearMap.map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem hodgeMap_wedgeGerm (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f] {g : ℕ}
    (t : Fin g → IsLocalRing.maximalIdeal 𝒩.genStalk) :
    hodgeMap 𝒢 𝒩 f g (𝒩.wedge t) =
      𝒢.wedge (fun i => ⟨genMap 𝒢 𝒩 f (t i), genMap_mem_maximalIdeal 𝒢 𝒩 f _ (t i).2⟩) := by
  unfold GroupModel.wedge
  rw [hodgeMap_wedge]
  rfl

/-! ### Assembly: `HeightAntitone` from two algebraic statements -/

section Assembly

variable {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]
  [AddCommGroup V'] [Module L V'] [Module (𝓞 L) V'] [IsScalarTower (𝓞 L) L V']

omit [Algebra K L] in
/-- In a Hodge line, every nonzero lattice vector has finite index. -/
theorem secIndex_ne_zero_of_mem {g : ℕ} (D : HodgeData L g V) {v : V} (hv : v ∈ D.lattice)
    (hv0 : v ≠ 0) : secIndex D.lattice v ≠ 0 := by
  obtain ⟨s, hs, hs0, hsi⟩ := D.isLattice
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs0).mp D.finrank_eq_one v
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) c
  have hb0 : (b : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 L) L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 L) L)).mpr hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, zero_smul] at hc
    exact hv0 hc.symm
  have key : b • v = a • s := by
    rw [← hc, ← algebraMap_smul L b, smul_smul, ← algebraMap_smul L a]
    congr 1
    field_simp
  have h1 := secIndex_smul D.lattice hv hv0 b
  have h2 := secIndex_smul D.lattice hs hs0 a
  rw [key, h2] at h1
  intro h
  rw [h, mul_zero] at h1
  have hna : (Algebra.norm ℤ a).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ha0)
  exact mul_ne_zero hna hsi h1

omit [NumberField L] in
theorem map_span_singleton_toAddSubgroup (H : V' →ₗ[L] V) (v₀ : V') :
    (Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom =
      (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup := by
  ext x
  simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
    LinearMap.toAddMonoidHom_coe]
  constructor
  · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c • v₀, ⟨c, rfl⟩, by rw [← algebraMap_smul L c, ← algebraMap_smul L c, map_smul]⟩

omit [NumberField L] in
/-- Indices along an injective map into a lattice. -/
theorem secIndex_le_of_map (H : V' →ₗ[L] V) (hH : Function.Injective H)
    (Λ' : Submodule (𝓞 L) V') (Λ : Submodule (𝓞 L) V) (hle : ∀ x ∈ Λ', H x ∈ Λ) {v₀ : V'}
    (hv₀ : v₀ ∈ Λ') (hne : secIndex Λ (H v₀) ≠ 0) :
    secIndex Λ' v₀ ≠ 0 ∧ secIndex Λ' v₀ ≤ secIndex Λ (H v₀) := by
  have hinj : Function.Injective H.toAddMonoidHom := hH
  have e1 : secIndex Λ' v₀ = ((Submodule.span (𝓞 L) {v₀}).toAddSubgroup.map H.toAddMonoidHom).relIndex
      (Λ'.toAddSubgroup.map H.toAddMonoidHom) :=
    (AddSubgroup.relIndex_map_map_of_injective _ _ hinj).symm
  rw [map_span_singleton_toAddSubgroup] at e1
  have hAB : (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup ≤ Λ'.toAddSubgroup.map H.toAddMonoidHom := by
    rw [← map_span_singleton_toAddSubgroup]
    exact AddSubgroup.map_mono (fun x hx => by
      simp only [Submodule.mem_toAddSubgroup] at hx ⊢
      exact (Submodule.span_le.mpr (by simpa using hv₀)) hx)
  have hBC : Λ'.toAddSubgroup.map H.toAddMonoidHom ≤ Λ.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩
    exact hle y hy
  have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hAB hBC
  have hne' : secIndex Λ (H v₀) = (Submodule.span (𝓞 L) {H v₀}).toAddSubgroup.relIndex
      Λ.toAddSubgroup := rfl
  rw [e1]
  have hmul' := hmul.trans hne'.symm
  exact ⟨left_ne_zero_of_mul (hmul'.symm ▸ hne), Nat.le_of_dvd (Nat.pos_of_ne_zero hne)
    (Dvd.intro _ hmul')⟩

omit [NumberField L] in
/-- Pull back Hodge data along an injective `L`-linear map onto a new lattice. -/
noncomputable def pullHodge {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) : HodgeData L g V' where
  lattice := Λ'
  finrank_eq_one := hfin
  isLattice := hlat
  periods := D.periods
  periods_discrete := D.periods_discrete
  periods_isZLattice := D.periods_isZLattice
  coeff τ := (D.coeff τ).comp H
  coeff_ne_zero τ := by
    obtain ⟨s, -, hs0, -⟩ := hlat
    intro h
    have h1 := LinearMap.congr_fun h s
    have hHs : H s ≠ 0 := fun h0 => hs0 (hH (h0.trans (map_zero H).symm))
    exact D.coeff_apply_ne_zero τ hHs h1

omit [Algebra K L] in
theorem modelHeight_pullHodge_le {g : ℕ} (D : HodgeData L g V) (H : V' →ₗ[L] V)
    (hH : Function.Injective H) (Λ' : Submodule (𝓞 L) V') (hfin : Module.finrank L V' = 1)
    (hlat : ∃ s ∈ Λ', s ≠ 0 ∧ secIndex Λ' s ≠ 0) (hle : ∀ x ∈ Λ', H x ∈ D.lattice) :
    (pullHodge D H hH Λ' hfin hlat).modelHeight ≤ D.modelHeight := by
  obtain ⟨v₀, hv₀, hv0, -⟩ := hlat
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hH (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem D (hle v₀ hv₀) hHv0
  obtain ⟨hpos, hle'⟩ := secIndex_le_of_map H hH Λ' D.lattice hle hv₀ hne
  rw [(pullHodge D H hH Λ' hfin _).modelHeight_eq hv₀ hv0,
    D.modelHeight_eq (hle v₀ hv₀) hHv0]
  have hd : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  apply div_le_div_of_nonneg_right _ hd.le
  have : Real.log (secIndex Λ' v₀) ≤ Real.log (secIndex D.lattice (H v₀)) :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hpos) (by exact_mod_cast hle')
  show Real.log (secIndex Λ' v₀) - (1 / 2) * ∑ σ : L →+* ℂ,
      Real.log (torusMetricSq (D.periods σ) (D.coeff σ (H v₀))) ≤ _
  linarith

end Assembly

/-- **Glue (stated): `L ⊗ ⋀^g f^*` is bijective for a generic isomorphism** (it is induced by the
ring isomorphism `genMap`, `stalkIso_of_genericIso`; STANDARD algebra). -/
def HodgeMapBijective : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) [IsMonHom f], IsIso ((Over.pullback (jL L)).map f) →
    ∀ g : ℕ, Function.Bijective (hodgeMap 𝒢 𝒩 f g)

/-- **Glue (stated): a Hodge line contains a nonzero lattice vector.** If `hodgeSpace g` is an
`L`-line, then `⋀^g ω_𝒩 ≠ 0` (`ω_𝒩` spans `ω_{A_L}`: `OmegaSpans`, proved in hodge-lattice; then
the wedges of `ω_𝒩` span the line; STANDARD). -/
def HodgeLatticeNonzero : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒩 : GroupModel A L) (g : ℕ), Module.finrank L (𝒩.hodgeSpace g) = 1 →
      ∃ v₀ ∈ 𝒩.detLattice g, v₀ ≠ 0

/-- **Glue (as in `Minimal.lean`)** -/
def HeightAntitone : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G), IsMonHom f →
    IsIso ((Over.pullback (jL L)).map f) → 𝒩.height ≤ 𝒢.height

/-- **`HeightAntitone` from `HodgeMapBijective` and `HodgeLatticeNonzero`** (proved). -/
theorem heightAntitone_of (hb : HodgeMapBijective) (hn : HodgeLatticeNonzero) :
    HeightAntitone := by
  intro K _ A L _ _ _ 𝒢 𝒩 f hm hi
  haveI := hm
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun M => le_iInf fun hM => ?_
  subst hM
  have hbij := hb K A L M.model 𝒩 f hi g
  set H := hodgeMap M.model 𝒩 f g
  have hfin : Module.finrank L (𝒩.hodgeSpace g) = 1 :=
    (LinearEquiv.ofBijective H hbij).finrank_eq.trans M.hodge.finrank_eq_one
  obtain ⟨v₀, hv₀, hv0⟩ := hn K A L 𝒩 g hfin
  have hle : ∀ x ∈ 𝒩.detLattice g, H x ∈ M.hodge.lattice := fun x hx => by
    rw [M.lattice_eq]; exact hodgeMap_detLattice _ _ f g x hx
  have hHv0 : H v₀ ≠ 0 := fun h0 => hv0 (hbij.1 (h0.trans (map_zero H).symm))
  have hne := secIndex_ne_zero_of_mem M.hodge (hle v₀ hv₀) hHv0
  have hlat : ∃ s ∈ 𝒩.detLattice g, s ≠ 0 ∧ secIndex (𝒩.detLattice g) s ≠ 0 :=
    ⟨v₀, hv₀, hv0, (secIndex_le_of_map H hbij.1 _ _ hle hv₀ hne).1⟩
  let M' : MetrizedModel A L g :=
    { model := 𝒩
      hodge := pullHodge M.hodge H hbij.1 (𝒩.detLattice g) hfin hlat
      lattice_eq := rfl
      arch := fun τ => by
        obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
        refine ⟨fun z => Φ z ≫ f, isAnalyticUniformization_comp _ _ f τ _ Φ hΦ, fun t => ?_⟩
        show M.hodge.coeff τ (H (𝒩.wedge t)) = _
        rw [hodgeMap_wedgeGerm, hc, jacDet_comp_genMap M.model 𝒩 f _ Φ hΦ t
          (fun i => ⟨genMap M.model 𝒩 f (t i), genMap_mem_maximalIdeal _ _ f _ (t i).2⟩)
          (fun i => rfl)] }
  calc (⨅ (g' : ℕ) (M'' : MetrizedModel A L g') (_ : M''.model = 𝒩),
        (M''.hodge.modelHeight : EReal)) ≤ (M'.hodge.modelHeight : EReal) :=
        iInf_le_of_le g (iInf_le_of_le M' (iInf_le_of_le rfl le_rfl))
    _ ≤ (M.hodge.modelHeight : EReal) :=
        EReal.coe_le_coe_iff.mpr (modelHeight_pullHodge_le M.hodge H hbij.1 _ hfin hlat hle)

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.pts_comp_bijective
#print axioms ZInQ.H5Glue.evalAt_comp
#print axioms ZInQ.H5Glue.isAnalyticUniformization_comp
#print axioms ZInQ.H5Glue.germAlong_comp_eventuallyEq
#print axioms ZInQ.H5Glue.jacDet_comp_map
#print axioms ZInQ.H5Glue.jacDet_comp_genMap
#print axioms ZInQ.H5Glue.genMap_structMap
#print axioms ZInQ.H5Glue.cotMap
#print axioms ZInQ.H5Glue.cotMap_dCls
#print axioms ZInQ.H5Glue.cotMap_omega
#print axioms ZInQ.H5Glue.hodgeMap_detLattice
#print axioms ZInQ.H5Glue.hodgeMap_wedgeGerm
#print axioms ZInQ.H5Glue.modelHeight_pullHodge_le
#print axioms ZInQ.H5Glue.heightAntitone_of
