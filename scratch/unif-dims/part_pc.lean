
/-! # unif-dims: toward `ProductCotangent` — cotangent maps of unit-preserving morphisms -/


open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A germ of a global section, pulled back. -/
theorem Scheme.Hom.stalkMapAt_germ_top {X Y : Scheme.{u}} (f : X ⟶ Y) {x : X} {y : Y}
    (h : f x = y) (s : Γ(Y, ⊤)) :
    (f.stalkMapAt h).hom (Y.presheaf.germ ⊤ y (TopologicalSpace.Opens.mem_top _) s) =
      X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top _) (f.appTop s) := by
  subst h
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.germ_stalkMap_apply]
  rfl

/-- Stalk maps between given points commute with specialization. -/
theorem Scheme.Hom.stalkMapAt_stalkSpecializes {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X}
    {y y' : Y} (hx : x ⤳ x') (hy : y ⤳ y') (h : f x = y) (h' : f x' = y') (r : Y.presheaf.stalk y') :
    X.presheaf.stalkSpecializes hx ((f.stalkMapAt h').hom r) =
      (f.stalkMapAt h).hom (Y.presheaf.stalkSpecializes hy r) := by
  subst h h'
  rw [Scheme.Hom.stalkMapAt_rfl, Scheme.Hom.stalkMapAt_rfl,
    ← Scheme.Hom.stalkSpecializes_stalkMap_apply]

end AlgebraicGeometry

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

section CotMap

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- The stalk map at the generic units of a morphism of models preserving them. -/
noncomputable abbrev germMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.genStalk →+* 𝒢.genStalk :=
  (φ.left.stalkMapAt h).hom

/-- A morphism of models over `Spec 𝓞_L` is compatible with the structure maps. -/
theorem germMap_structMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (c : 𝓞 L) : germMap 𝒢 ℋ φ h (ℋ.structMap c) = 𝒢.structMap c := by
  rw [HodgeLattice.structMap_eq, HodgeLattice.structMap_eq, germMap,
    Scheme.Hom.stalkMapAt_germ_top]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- **The cotangent map** `cot_ℋ → cot_𝒢`, `df ↦ d(φ* f)`. -/
noncomputable def cotMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.cotangent →ₗ[𝓞 L] 𝒢.cotangent := by
  let ρ := germMap 𝒢 ℋ φ h
  letI : Module ℋ.genStalk 𝒢.cotangent := Module.compHom _ ρ
  let f : IsLocalRing.maximalIdeal ℋ.genStalk →ₗ[ℋ.genStalk] 𝒢.cotangent :=
    { toFun := fun x => 𝒢.dCls ⟨ρ x, map_nonunit ρ _ x.2⟩
      map_add' := fun x y => by
        simp only [GroupModel.dCls]
        have e : (⟨ρ ↑(x + y), map_nonunit ρ _ (x + y).2⟩ :
            IsLocalRing.maximalIdeal 𝒢.genStalk) =
            (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) +
              ⟨ρ y, map_nonunit ρ _ y.2⟩ := Subtype.ext (by simp)
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_add _ _ _
      map_smul' := fun r x => by
        simp only [GroupModel.dCls, RingHom.id_apply]
        have e : (⟨ρ ↑(r • x), map_nonunit ρ _ (r • x).2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
            ρ r • (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) :=
          Subtype.ext (by simp [ρ])
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_smul _ _ _ }
  let j0 : ℋ.cotangent →ₗ[ℋ.genStalk] 𝒢.cotangent := Ideal.Cotangent.lift f (fun x y => by
    refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
    show ρ (↑x * ↑y) ∈ _
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul (map_nonunit ρ _ x.2) (map_nonunit ρ _ y.2))
  exact
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun c x => by
        show j0 (ℋ.structMap c • x) = 𝒢.structMap c • j0 x
        rw [j0.map_smul]
        show ρ (ℋ.structMap c) • j0 x = _
        rw [germMap_structMap] }

theorem cotMap_dCls (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (f : IsLocalRing.maximalIdeal ℋ.genStalk) :
    cotMap 𝒢 ℋ φ h (ℋ.dCls f) =
      𝒢.dCls ⟨germMap 𝒢 ℋ φ h f, map_nonunit (germMap 𝒢 ℋ φ h) _ f.2⟩ := by
  rfl


theorem cotMap_comp {B : AbVar K} (𝒦 : GroupModel B L) (φ : 𝒢.G ⟶ ℋ.G) (ψ : ℋ.G ⟶ 𝒦.G)
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) (h' : ψ.left ℋ.genericUnit = 𝒦.genericUnit)
    (h'' : (φ ≫ ψ).left 𝒢.genericUnit = 𝒦.genericUnit) :
    cotMap 𝒢 𝒦 (φ ≫ ψ) h'' = cotMap 𝒢 ℋ φ h ∘ₗ cotMap ℋ 𝒦 ψ h' := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒦.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒦 (φ ≫ ψ) h'' (𝒦.dCls f) = cotMap 𝒢 ℋ φ h (cotMap ℋ 𝒦 ψ h' (𝒦.dCls f))
  rw [cotMap_dCls, cotMap_dCls, cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ φ ψ) h'' (by rw [← h', ← h]; rfl),
    Scheme.Hom.stalkMapAt_comp φ.left ψ.left h h']
  rfl

theorem cotMap_id (h : (𝟙 𝒢.G : 𝒢.G ⟶ 𝒢.G).left 𝒢.genericUnit = 𝒢.genericUnit) :
    cotMap 𝒢 𝒢 (𝟙 𝒢.G) h = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒢 (𝟙 𝒢.G) h (𝒢.dCls f) = 𝒢.dCls f
  rw [cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.id_left 𝒢.G) h h, Scheme.Hom.stalkMapAt_id]
  rfl

/-- A morphism of models preserving the unit sections maps every `e(s)` to `e(s)`. -/
theorem map_unitSection (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (s : Spec (CommRingCat.of (𝓞 L))) : φ.left (𝒢.unitSection s) = ℋ.unitSection s := by
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  rw [← h2]
  rfl

/-- **Functoriality of `ω`.** A morphism of models preserving the unit sections maps
`ω_ℋ` into `ω_𝒢` under the cotangent map. -/
theorem omega_map_le (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.omega.map (cotMap 𝒢 ℋ φ h) ≤ 𝒢.omega := by
  refine le_iInf fun s => (Submodule.map_mono (iInf_le _ s)).trans ?_
  rw [GroupModel.omegaAt, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, hf, hfm, rfl⟩, rfl⟩
  have hs := map_unitSection 𝒢 ℋ φ hφ s
  set f' := (φ.left.stalkMapAt hs).hom f with hf'
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  have hker : f' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
    rw [RingHom.mem_ker] at hf ⊢
    have e1 := Scheme.Hom.stalkMapAt_comp 𝒢.unitSection φ.left (rfl : 𝒢.unitSection s = _) hs
      (by rw [← hs]; rfl)
    rw [Scheme.Hom.stalkMapAt_congr h2 _ rfl, Scheme.Hom.stalkMapAt_rfl,
      Scheme.Hom.stalkMapAt_rfl] at e1
    rw [hf', ← CommRingCat.comp_apply, ← e1, hf]
  have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' =
      germMap 𝒢 ℋ φ h (ℋ.G.left.presheaf.stalkSpecializes (ℋ.specializes_genericUnit s) f) :=
    Scheme.Hom.stalkMapAt_stalkSpecializes φ.left _ _ h hs f
  have hm : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [hspec]; exact map_nonunit (germMap 𝒢 ℋ φ h) _ hfm
  apply Submodule.subset_span
  refine ⟨f', hker, hm, ?_⟩
  rw [cotMap_dCls]
  congr 2
  exact hspec.symm

theorem cotMap_congr {φ φ' : 𝒢.G ⟶ ℋ.G} (e : φ = φ') (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (h' : φ'.left 𝒢.genericUnit = ℋ.genericUnit) : cotMap 𝒢 ℋ φ h = cotMap 𝒢 ℋ φ' h' := by
  subst e; rfl

end CotMap

section Helpers

variable {X : AbVar K} (𝒢 : GroupModel X L)

/-- The unit section is a section of the structure morphism (copied from infra-stalks). -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  simpa using Over.w η[𝒢.G]

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  unfold GroupModel.genericUnit
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

theorem rationalOver_genericUnit : RationalOver 𝒢.G.hom 𝒢.genericUnit :=
  rationalOver_of_section _ _ (unitSection_comp_hom 𝒢) (genericPt L)

omit [Algebra K L] in
/-- The stalk of `Spec 𝓞_L` at its generic point is a field (copied from infra-stalks). -/
theorem maximalIdeal_stalk_genericPt :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) = ⊥ := by
  have h : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
    rw [genericPoint_eq_bot_of_affine]; rfl
  refine (IsLocalRing.isField_iff_maximalIdeal_eq).mp ?_
  rw [h]
  exact Field.toIsField (Spec (CommRingCat.of (𝓞 L))).functionField

end Helpers

section Trivial

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- A morphism of models that factors through `Spec 𝓞_L` kills `𝔪` at the generic units. -/
theorem germMap_eq_zero_of_factor (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (b : Spec (CommRingCat.of (𝓞 L)) ⟶ ℋ.G.left) (hφ : φ.left = 𝒢.G.hom ≫ b)
    (a : ℋ.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal ℋ.genStalk) : germMap 𝒢 ℋ φ h a = 0 := by
  have h1 : 𝒢.G.hom 𝒢.genericUnit = genericPt L := hom_genericUnit 𝒢
  have h2 : b (genericPt L) = ℋ.genericUnit := by
    rw [← h, hφ, Scheme.Hom.comp_apply, h1]
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr hφ h (by rw [Scheme.Hom.comp_apply, h1, h2]),
    Scheme.Hom.stalkMapAt_comp 𝒢.G.hom b h1 h2]
  have hz : (b.stalkMapAt h2).hom a = 0 := by
    have hm := map_nonunit (b.stalkMapAt h2).hom a ha
    rw [maximalIdeal_stalk_genericPt] at hm
    exact (Submodule.mem_bot _).mp hm
  rw [CommRingCat.comp_apply, hz, map_zero]

end Trivial

section Product

variable {A B C : AbVar K} (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]

/-- `x ↦ (x, 1)`. -/
noncomputable def inc₁ : 𝒢₁.G ⟶ 𝒢P.G := lift (𝟙 _) (toUnit _ ≫ η[𝒢₂.G]) ≫ e.inv

/-- `y ↦ (1, y)`. -/
noncomputable def inc₂ : 𝒢₂.G ⟶ 𝒢P.G := lift (toUnit _ ≫ η[𝒢₁.G]) (𝟙 _) ≫ e.inv

theorem eta_e : η[𝒢P.G] ≫ e.hom = lift η[𝒢₁.G] η[𝒢₂.G] := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, IsMonHom.one_hom, lift_fst]
  · rw [Category.assoc, IsMonHom.one_hom, lift_snd]

theorem eta_inc₁ : η[𝒢₁.G] ≫ inc₁ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₁, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem eta_inc₂ : η[𝒢₂.G] ≫ inc₂ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₂, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem inc₁_p₁ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = 𝟙 _ := by simp [inc₁]
theorem inc₁_p₂ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = toUnit _ ≫ η[𝒢₂.G] := by simp [inc₁]
theorem inc₂_p₁ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = toUnit _ ≫ η[𝒢₁.G] := by simp [inc₂]
theorem inc₂_p₂ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = 𝟙 _ := by simp [inc₂]

theorem toUnit_eta_left {X Y : AbVar K} (𝒳 : GroupModel X L) (𝒴 : GroupModel Y L) :
    (toUnit 𝒳.G ≫ η[𝒴.G]).left = 𝒳.G.hom ≫ 𝒴.unitSection := rfl

theorem hp₁ : (e.hom ≫ fst _ _).left 𝒢P.genericUnit = 𝒢₁.genericUnit :=
  map_unitSection 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (genericPt L)
theorem hp₂ : (e.hom ≫ snd _ _).left 𝒢P.genericUnit = 𝒢₂.genericUnit :=
  map_unitSection 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (genericPt L)
theorem hi₁ : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₁.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)
theorem hi₂ : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₂.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)

/-- A retraction on stalks. -/
theorem retract_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) {x : X}
    {y : Y} (hf : f x = y) (hg : g y = x) (a : X.presheaf.stalk x) :
    (f.stalkMapAt hf).hom ((g.stalkMapAt hg).hom a) = a := by
  subst hf
  have h1 : (f ≫ g).stalkMapAt hg = g.stalkMapAt hg ≫ f.stalkMapAt rfl :=
    Scheme.Hom.stalkMapAt_comp f g rfl hg hg
  rw [← CommRingCat.comp_apply, ← h1]
  have key : ∀ (k : X ⟶ X) (_ : k = 𝟙 X) (h : k x = x), (k.stalkMapAt h).hom a = a := by
    intro k hk h; subst hk; rw [Scheme.Hom.stalkMapAt_id]; rfl
  exact key _ hfg hg

/-- germ-level retraction identities -/
theorem germ_retract₁ (a : 𝒢₁.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₁_p₁]; rfl) _ _ a

theorem germ_retract₂ (a : 𝒢₂.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₂_p₂]; rfl) _ _ a

theorem germ_cross₁₂ (a : 𝒢₂.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₂.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _)).left 𝒢₁.genericUnit = 𝒢₂.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₁, hp₂]
  have := germMap_eq_zero_of_factor 𝒢₁ 𝒢₂ _ hc 𝒢₂.unitSection
    (by rw [inc₁_p₂]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₁, hp₂]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

theorem germ_cross₂₁ (a : 𝒢₁.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₁.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _)).left 𝒢₂.genericUnit = 𝒢₁.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₂, hp₁]
  have := germMap_eq_zero_of_factor 𝒢₂ 𝒢₁ _ hc 𝒢₁.unitSection
    (by rw [inc₂_p₁]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₂, hp₁]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

end Product

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.cotMap_dCls
#print axioms ZInQ.UnifDims.cotMap_comp
#print axioms ZInQ.UnifDims.cotMap_id
#print axioms ZInQ.UnifDims.omega_map_le
