import ZInQKernel.Contrib.NeronC.NeronGroup

/-! # neron-ext: Néron models over `Spec 𝓞_L` glue from a Zariski cover (part 1: setup, restriction) -/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Limits
open NumberField

namespace NeronExt

section Setup

variable (L : Type) [Field L] [NumberField L]

/-- `Spec 𝓞_L`. -/
noncomputable abbrev S : Scheme.{0} := Spec (CommRingCat.of (𝓞 L))

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jL : Spec (CommRingCat.of L) ⟶ S L := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- The generic fibre functor `X ↦ X ×_{𝓞_L} L`. -/
noncomputable abbrev gf : Over (S L) ⥤ Over (Spec (CommRingCat.of L)) := Over.pullback (jL L)

theorem denseRange_jL : DenseRange (jL L) := by
  rw [Spec.map_base]
  show DenseRange (PrimeSpectrum.comap (algebraMap (𝓞 L) L))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro x hx
  rw [RingHom.mem_ker] at hx
  rw [FaithfulSMul.algebraMap_injective (𝓞 L) L (hx.trans (map_zero _).symm)]
  exact zero_mem _

/-- A nonempty open of `Spec 𝓞_L` contains the generic point. -/
theorem jL_preimage_eq_top {U : (S L).Opens} (hU : (U : Set (S L)).Nonempty) :
    (jL L) ⁻¹ᵁ U = ⊤ := by
  obtain ⟨p, hp⟩ := (denseRange_jL L).exists_mem_open U.isOpen hU
  refine top_unique (fun q _ => ?_)
  have : q = p := Subsingleton.elim _ _
  subst this
  exact hp

/-- `X` lies over the open `U`. -/
def Supp (U : (S L).Opens) (X : Over (S L)) : Prop := X.hom ⁻¹ᵁ U = ⊤

theorem mem_of_supp {U : (S L).Opens} {X : Over (S L)} (h : Supp L U X) (x : X.left) :
    X.hom x ∈ U := by
  have : x ∈ X.hom ⁻¹ᵁ U := by rw [h]; trivial
  exact this

/-- An open immersion of `Z`-schemes which is surjective over an open `U ⊆ Z` induces an isomorphism
after base change along any `j : T → Z` landing in `U`. -/
theorem isIso_pb_map {Z T : Scheme.{0}} (j : T ⟶ Z) {X X' : Over Z} (ι : X' ⟶ X)
    [IsOpenImmersion ι.left] (U : Z.Opens)
    (hU : j ⁻¹ᵁ U = ⊤) (hr : ∀ x : X.left, X.hom x ∈ U → x ∈ Set.range ι.left) :
    IsIso ((Over.pullback j).map ι) := by
  have hrange : Set.range (pullback.fst X.hom j) ⊆ Set.range ι.left := by
    rintro _ ⟨z, rfl⟩
    apply hr
    have h1 : X.hom (pullback.fst X.hom j z) = j (pullback.snd X.hom j z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    have : pullback.snd X.hom j z ∈ j ⁻¹ᵁ U := by rw [hU]; trivial
    exact this
  let a : pullback X.hom j ⟶ X'.left := IsOpenImmersion.lift ι.left _ hrange
  have ha : a ≫ ι.left = pullback.fst X.hom j := IsOpenImmersion.lift_fac _ _ _
  have hc : a ≫ X'.hom = pullback.snd X.hom j ≫ j := by
    rw [← Over.w ι, ← Category.assoc, ha, pullback.condition]
  let inv : (Over.pullback j).obj X ⟶ (Over.pullback j).obj X' :=
    Over.homMk (pullback.lift a (pullback.snd _ _) hc) (pullback.lift_snd _ _ _)
  refine ⟨inv, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [← cancel_mono ι.left]
      simp only [inv, Over.comp_left, Over.pullback_map_left, Over.homMk_left, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, ha, Over.id_left, Category.id_comp]
    · simp only [inv, Over.comp_left, Over.pullback_map_left, Over.homMk_left, Category.assoc,
        pullback.lift_snd, Over.id_left, Category.id_comp]
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [inv, Over.comp_left, Over.pullback_map_left, Over.homMk_left, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, ha, Over.id_left, Category.id_comp]
    · simp only [inv, Over.comp_left, Over.pullback_map_left, Over.homMk_left, Category.assoc,
        pullback.lift_snd, Over.id_left, Category.id_comp]

theorem isIso_gf_map {X X' : Over (S L)} (ι : X' ⟶ X) [IsOpenImmersion ι.left] (U : (S L).Opens)
    (hU : (jL L) ⁻¹ᵁ U = ⊤) (hr : ∀ x : X.left, X.hom x ∈ U → x ∈ Set.range ι.left) :
    IsIso ((gf L).map ι) :=
  isIso_pb_map (jL L) ι U hU hr

end Setup

/-! ## Néron models over an open of `Spec 𝓞_L` -/

section NeronOn

variable (L : Type) [Field L] [NumberField L]

/-- **A Néron model of `B` over the open `U ⊆ Spec 𝓞_L`**, phrased over `Spec 𝓞_L`: a smooth,
separated, quasi-compact `𝓞_L`-scheme `X` lying over `U`, with `e : X_L ≅ B`, such that every
`L`-morphism `Y_L → B` from the generic fibre of a smooth `𝓞_L`-scheme `Y` lying over `U` extends to
`Y → X` (uniqueness is automatic: `neron_extension_injective`). At `U = ⊤` this is the conclusion of
`NeronSchemeExtensionExists`. -/
structure NeronOn (B : Over (Spec (CommRingCat.of L))) (U : (S L).Opens) where
  X : Over (S L)
  supp : Supp L U X
  smooth : Smooth X.hom
  sep : IsSeparated X.hom
  qc : QuasiCompact X.hom
  e : (gf L).obj X ≅ B
  ext : ∀ (Y : Over (S L)) [Smooth Y.hom], Supp L U Y →
    Function.Surjective fun f : Y ⟶ X => (gf L).map f ≫ e.hom

variable {L}

attribute [instance] NeronOn.smooth NeronOn.sep NeronOn.qc

theorem NeronOn.inj {B : Over (Spec (CommRingCat.of L))} {U : (S L).Opens} (n : NeronOn L B U)
    (Y : Over (S L)) [Smooth Y.hom] {f g : Y ⟶ n.X}
    (h : (gf L).map f ≫ n.e.hom = (gf L).map g ≫ n.e.hom) : f = g :=
  ZInQ.Contrib.NeronC.neron_extension_injective L n.X n.e Y h

/-- The part of `X` over the open `U`. -/
noncomputable def res (X : Over (S L)) (U : (S L).Opens) : Over (S L) :=
  Over.mk ((X.hom ⁻¹ᵁ U).ι ≫ X.hom)

/-- Its inclusion. -/
noncomputable def resι (X : Over (S L)) (U : (S L).Opens) : res X U ⟶ X :=
  Over.homMk (X.hom ⁻¹ᵁ U).ι rfl

instance (X : Over (S L)) (U : (S L).Opens) : IsOpenImmersion (resι X U).left := by
  show IsOpenImmersion (X.hom ⁻¹ᵁ U).ι; infer_instance

instance smooth_res (X : Over (S L)) (U : (S L).Opens) [Smooth X.hom] : Smooth (res X U).hom := by
  dsimp [res]; infer_instance

instance sep_res (X : Over (S L)) (U : (S L).Opens) [IsSeparated X.hom] :
    IsSeparated (res X U).hom := by
  dsimp [res]; infer_instance

instance qc_res (X : Over (S L)) (U : (S L).Opens) [QuasiCompact X.hom] :
    QuasiCompact (res X U).hom := by
  dsimp [res]
  haveI : QuasiCompact (X.hom ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict X.hom U)
      (inferInstance : QuasiCompact U.ι)
  infer_instance

theorem range_comp_iso {X Y Z : Scheme.{0}} (a : X ⟶ Y) [IsIso a] (b : Y ⟶ Z) :
    Set.range (a ≫ b) = Set.range b := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨a x, (Scheme.Hom.comp_apply a b x).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨inv a y, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]

theorem supp_res (X : Over (S L)) (U : (S L).Opens) : Supp L U (res X U) := by
  show ((X.hom ⁻¹ᵁ U).ι ≫ X.hom) ⁻¹ᵁ U = ⊤
  rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]

theorem supp_mono {U V : (S L).Opens} (hUV : U ≤ V) {X : Over (S L)} (h : Supp L U X) :
    Supp L V X := by
  unfold Supp at *
  exact top_le_iff.mp (h ▸ Scheme.Hom.preimage_mono _ hUV)

/-- A map into `X` from a scheme lying over `U` factors through `res X U`. -/
noncomputable def liftRes {X Y : Over (S L)} {U : (S L).Opens} (hY : Supp L U Y) (f : Y ⟶ X) :
    Y ⟶ res X U :=
  Over.homMk (IsOpenImmersion.lift (X.hom ⁻¹ᵁ U).ι f.left (by
    rintro _ ⟨y, rfl⟩
    show f.left y ∈ Set.range (X.hom ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]
    show X.hom (f.left y) ∈ U
    rw [← Scheme.Hom.comp_apply, Over.w f]
    exact mem_of_supp L hY y)) (by
    show _ ≫ (X.hom ⁻¹ᵁ U).ι ≫ X.hom = Y.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w f])

@[simp] theorem liftRes_ι {X Y : Over (S L)} {U : (S L).Opens} (hY : Supp L U Y) (f : Y ⟶ X) :
    liftRes hY f ≫ resι X U = f := by
  apply Over.OverMorphism.ext
  simp [liftRes, resι]

theorem isIso_gf_resι (X : Over (S L)) {U : (S L).Opens} (hU : (jL L) ⁻¹ᵁ U = ⊤) :
    IsIso ((gf L).map (resι X U)) :=
  isIso_gf_map L (resι X U) U hU (fun x hx => by
    show x ∈ Set.range (X.hom ⁻¹ᵁ U).ι
    rw [Scheme.Opens.range_ι]; exact hx)

/-- **Restriction.** A Néron model over `V` restricts to a Néron model over every open `U ⊆ V`
containing the generic point. -/
noncomputable def NeronOn.restrict {B : Over (Spec (CommRingCat.of L))} {U V : (S L).Opens}
    (n : NeronOn L B V) (hUV : U ≤ V) (hU : (jL L) ⁻¹ᵁ U = ⊤) : NeronOn L B U :=
  haveI := isIso_gf_resι n.X hU
  { X := res n.X U
    supp := supp_res n.X U
    smooth := inferInstance
    sep := inferInstance
    qc := inferInstance
    e := asIso ((gf L).map (resι n.X U)) ≪≫ n.e
    ext := fun Y _ hY φ => by
      obtain ⟨f, hf⟩ := n.ext Y (supp_mono hUV hY) φ
      refine ⟨liftRes hY f, ?_⟩
      simp only [Iso.trans_hom, asIso_hom, ← Category.assoc, ← CategoryTheory.Functor.map_comp, liftRes_ι]
      exact hf }

end NeronOn

/-! ## Gluing over a Zariski cover of `Spec 𝓞_L` -/

section Glue

variable {L : Type} [Field L] [NumberField L] (B : Over (Spec (CommRingCat.of L)))

theorem opensRange_lift {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] (H : Set.range g ⊆ Set.range f) :
    (IsOpenImmersion.lift f g H).opensRange = f ⁻¹ᵁ g.opensRange := by
  ext x
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range, Scheme.Hom.mem_preimage]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, f.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac, hy]

theorem opensRange_of_fac {X Y Z : Scheme.{0}} (a : X ⟶ Y) (f : Y ⟶ Z) (g : X ⟶ Z)
    [IsOpenImmersion a] [IsOpenImmersion f] [IsOpenImmersion g] (h : a ≫ f = g) :
    a.opensRange = f ⁻¹ᵁ g.opensRange := by
  subst h
  ext x
  simp only [Scheme.Hom.coe_opensRange, Set.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by rw [Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, f.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hy]

/-- The opens (containing the generic point) over which `B` has a Néron model. -/
def Good (U : (S L).Opens) : Prop := (jL L) ⁻¹ᵁ U = ⊤ ∧ Nonempty (NeronOn L B U)

/-- The index type of the gluing. -/
abbrev Idx : Type := {U : (S L).Opens // Good B U}

/-- A chosen Néron model over each good open. -/
noncomputable def nn (i : Idx B) : NeronOn L B i.1 := Classical.choice i.2.2

/-- The transition maps (unique extensions of the identity of `B`). -/
noncomputable def tr {i j : Idx B} (h : i ≤ j) : (nn B i).X ⟶ (nn B j).X :=
  ((nn B j).ext (nn B i).X (supp_mono h (nn B i).supp) (nn B i).e.hom).choose

theorem tr_spec {i j : Idx B} (h : i ≤ j) :
    (gf L).map (tr B h) ≫ (nn B j).e.hom = (nn B i).e.hom :=
  ((nn B j).ext (nn B i).X (supp_mono h (nn B i).supp) (nn B i).e.hom).choose_spec

theorem tr_id (i : Idx B) (h : i ≤ i) : tr B h = 𝟙 _ :=
  (nn B i).inj _ (by rw [tr_spec, CategoryTheory.Functor.map_id, Category.id_comp])

theorem tr_comp {i j k : Idx B} (hij : i ≤ j) (hjk : j ≤ k) (hik : i ≤ k) :
    tr B hik = tr B hij ≫ tr B hjk :=
  (nn B k).inj _ (by rw [tr_spec, CategoryTheory.Functor.map_comp, Category.assoc, tr_spec, tr_spec])

/-- `tr` factors through the part of `X_j` over `U_i` by an isomorphism. -/
theorem isIso_liftRes_tr {i j : Idx B} (h : i ≤ j) :
    IsIso (liftRes (nn B i).supp (tr B h)) := by
  haveI := isIso_gf_resι (nn B j).X (U := i.1) i.2.1
  let e' : (gf L).obj (res (nn B j).X i.1) ≅ B := asIso ((gf L).map (resι _ _)) ≪≫ (nn B j).e
  obtain ⟨s, hs⟩ := (nn B i).ext (res (nn B j).X i.1) (supp_res _ _) e'.hom
  have hs' : (gf L).map s ≫ (nn B i).e.hom = (gf L).map (resι _ _) ≫ (nn B j).e.hom := hs
  refine ⟨s, ?_, ?_⟩
  · apply (nn B i).inj
    rw [CategoryTheory.Functor.map_comp, Category.assoc, hs', CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, ← CategoryTheory.Functor.map_comp, liftRes_ι, tr_spec]
  · apply ZInQ.Contrib.NeronC.neron_extension_injective L (res (nn B j).X i.1) e'
    show _ ≫ (gf L).map (resι _ _) ≫ (nn B j).e.hom = _ ≫ (gf L).map (resι _ _) ≫ (nn B j).e.hom
    rw [CategoryTheory.Functor.map_comp, Category.assoc, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc ((gf L).map (liftRes _ _)), ← CategoryTheory.Functor.map_comp,
      liftRes_ι, tr_spec, hs']

instance isOpenImmersion_tr {i j : Idx B} (h : i ≤ j) : IsOpenImmersion (tr B h).left := by
  haveI := isIso_liftRes_tr B h
  have : (tr B h).left = (liftRes (nn B i).supp (tr B h)).left ≫ (resι (nn B j).X i.1).left := by
    rw [← Over.comp_left, liftRes_ι]
  rw [this]
  infer_instance

theorem opensRange_tr {i j : Idx B} (h : i ≤ j) :
    (tr B h).left.opensRange = (nn B j).X.hom ⁻¹ᵁ i.1 := by
  haveI := isIso_liftRes_tr B h
  have : (tr B h).left = (liftRes (nn B i).supp (tr B h)).left ≫ (resι (nn B j).X i.1).left := by
    rw [← Over.comp_left, liftRes_ι]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange, this, range_comp_iso]
  show Set.range ((nn B j).X.hom ⁻¹ᵁ i.1).ι = _
  rw [Scheme.Opens.range_ι]

variable (hcov : ∀ x : S L, ∃ U : (S L).Opens, x ∈ U ∧ Nonempty (NeronOn L B U))

/-- The open cover of `Spec 𝓞_L` by the good opens. -/
noncomputable def cov : (S L).OpenCover where
  I₀ := Idx B
  X i := i.1
  f i := i.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hx, hn⟩ := hcov x
    exact ⟨⟨U, jL_preimage_eq_top L ⟨x, hx⟩, hn⟩, by simpa using hx⟩

instance : Preorder (cov B hcov).I₀ := inferInstanceAs (Preorder (Idx B))

theorem isBasis_good :
    TopologicalSpace.Opens.IsBasis (Set.range fun i : (cov B hcov).I₀ ↦ ((cov B hcov).f i).opensRange) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U, hxU, ⟨n⟩⟩ := hcov x
  have hne : ((U ⊓ W : (S L).Opens) : Set (S L)).Nonempty := ⟨x, hxU, hx⟩
  have hg : Good B (U ⊓ W) := ⟨jL_preimage_eq_top L hne,
    ⟨n.restrict inf_le_left (jL_preimage_eq_top L hne)⟩⟩
  refine ⟨U ⊓ W, ⟨⟨U ⊓ W, hg⟩, Scheme.Opens.opensRange_ι _⟩, ⟨hxU, hx⟩, inf_le_right⟩

noncomputable instance locDir : (cov B hcov).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp [cov]) (isBasis_good B hcov)

theorem mem_range_ι (U : (S L).Opens) (x : S L) (hx : x ∈ U) : x ∈ Set.range U.ι := by
  rw [Scheme.Opens.range_ι]; exact hx

/-- The functor `i ↦ X_i`. -/
noncomputable def F : (cov B hcov).I₀ ⥤ Scheme.{0} where
  obj i := (nn B i).X.left
  map h := (tr B (leOfHom h)).left
  map_id i := by rw [tr_id]; rfl
  map_comp f g := by rw [tr_comp B (leOfHom f) (leOfHom g)]; rfl

/-- `X_i → U_i`. -/
noncomputable def toU (i : (cov B hcov).I₀) : (nn B i).X.left ⟶ (cov B hcov).X i :=
  IsOpenImmersion.lift i.1.ι (nn B i).X.hom (by
    rintro _ ⟨x, rfl⟩
    exact mem_range_ι _ _ (mem_of_supp L (nn B i).supp x))

@[reassoc (attr := simp)]
theorem toU_ι (i : (cov B hcov).I₀) : toU B hcov i ≫ (cov B hcov).f i = (nn B i).X.hom :=
  IsOpenImmersion.lift_fac _ _ _

/-- The natural transformation `X_i → U_i`. -/
noncomputable def nat : F B hcov ⟶ (cov B hcov).functorOfLocallyDirected where
  app i := toU B hcov i
  naturality {i j} h := by
    rw [← cancel_mono ((cov B hcov).f j)]
    simp only [Category.assoc, Scheme.Cover.functorOfLocallyDirected_map,
      Scheme.Cover.trans_map, toU_ι]
    exact Over.w (tr B (leOfHom h))

theorem equifibered : (nat B hcov).Equifibered := by
  intro i j h
  haveI : IsOpenImmersion ((F B hcov).map h) := isOpenImmersion_tr B (leOfHom h)
  refine (IsOpenImmersion.isPullback (toU B hcov i) ((F B hcov).map h)
    (((cov B hcov).functorOfLocallyDirected).map h) (toU B hcov j)
    ((nat B hcov).naturality h) ?_).flip
  show toU B hcov j ⁻¹ᵁ ((cov B hcov).trans h).opensRange = (tr B (leOfHom h)).left.opensRange
  rw [opensRange_tr, opensRange_of_fac _ _ _ (Scheme.Cover.trans_map (cov B hcov) h),
    ← Scheme.Hom.comp_preimage, toU_ι]
  congr 1
  exact Scheme.Opens.opensRange_ι _

/-- The relative gluing datum. -/
noncomputable def gd : (cov B hcov).RelativeGluingData where
  functor := F B hcov
  natTrans := nat B hcov
  equifibered := equifibered B hcov

instance isOpenImmersion_F_map {i j : (cov B hcov).I₀} (h : i ⟶ j) :
    IsOpenImmersion ((gd B hcov).functor.map h) :=
  isOpenImmersion_tr B (leOfHom h)

/-- The glued `𝓞_L`-scheme. -/
noncomputable def N : Over (S L) := Over.mk (gd B hcov).toBase

theorem toBase_isPullback (i : (cov B hcov).I₀) :
    IsPullback (colimit.ι (gd B hcov).functor i) (toU B hcov i) (gd B hcov).toBase
      ((cov B hcov).f i) :=
  ((gd B hcov).isPullback_natTrans_ι_toBase i).flip

theorem prop_N (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange] (hP : ∀ i : (cov B hcov).I₀, P (nn B i).X.hom) :
    P (gd B hcov).toBase := by
  apply IsZariskiLocalAtTarget.of_openCover (cov B hcov)
  intro i
  have h := toBase_isPullback B hcov i
  have e : pullback.snd (gd B hcov).toBase ((cov B hcov).f i) = h.isoPullback.inv ≫ toU B hcov i := by
    simp
  change P (pullback.snd (gd B hcov).toBase ((cov B hcov).f i))
  rw [e, MorphismProperty.cancel_left_of_respectsIso (P := P)]
  refine MorphismProperty.of_postcomp P (W' := @IsOpenImmersion) _ ((cov B hcov).f i)
    inferInstance ?_
  rw [toU_ι]
  exact hP i

/-- A base index (some good open). -/
noncomputable def i0 : (cov B hcov).I₀ :=
  let x0 : S L := jL L (Nonempty.some (PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance))
  ⟨(hcov x0).choose, jL_preimage_eq_top L ⟨x0, (hcov x0).choose_spec.1⟩,
    (hcov x0).choose_spec.2⟩

/-- The inclusion `X_{i₀} → N`. -/
noncomputable def ιN (i : (cov B hcov).I₀) : (nn B i).X ⟶ N B hcov :=
  Over.homMk (colimit.ι (gd B hcov).functor i) (by
    show colimit.ι (gd B hcov).functor i ≫ (gd B hcov).toBase = _
    rw [Scheme.Cover.RelativeGluingData.ι_toBase]
    exact toU_ι B hcov i)

instance (i : (cov B hcov).I₀) : IsOpenImmersion (ιN B hcov i).left := by
  show IsOpenImmersion (colimit.ι (gd B hcov).functor i); infer_instance

instance isIso_gf_ιN (i : (cov B hcov).I₀) : IsIso ((gf L).map (ιN B hcov i)) := by
  refine isIso_gf_map L (ιN B hcov i) i.1 i.2.1 (fun x hx => ?_)
  show x ∈ Set.range (colimit.ι (gd B hcov).functor i)
  rw [← Scheme.Cover.RelativeGluingData.preimage_toBase_eq_range_ι]
  exact mem_range_ι _ _ hx

/-- The generic-fibre identification of `N`. -/
noncomputable def eN : (gf L).obj (N B hcov) ≅ B :=
  (asIso ((gf L).map (ιN B hcov (i0 B hcov)))).symm ≪≫ (nn B (i0 B hcov)).e

section Ext

variable (Y : Over (S L)) [Smooth Y.hom]

/-- The pieces of `Y` over the good opens. -/
noncomputable def Yi (i : (cov B hcov).I₀) : Over (S L) :=
  Over.mk (pullback.fst Y.hom ((cov B hcov).f i) ≫ Y.hom)

instance (i : (cov B hcov).I₀) : Smooth (Yi B hcov Y i).hom := by
  dsimp [Yi]; infer_instance

theorem supp_Yi (i : (cov B hcov).I₀) : Supp L i.1 (Yi B hcov Y i) := by
  show (pullback.fst Y.hom ((cov B hcov).f i) ≫ Y.hom) ⁻¹ᵁ i.1 = ⊤
  rw [pullback.condition, Scheme.Hom.comp_preimage]
  show pullback.snd Y.hom ((cov B hcov).f i) ⁻¹ᵁ (i.1.ι ⁻¹ᵁ i.1) = ⊤
  rw [Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

/-- The inclusion of a piece. -/
noncomputable def inc (i : (cov B hcov).I₀) : Yi B hcov Y i ⟶ Y := Over.homMk (pullback.fst _ _) rfl

instance (i : (cov B hcov).I₀) : IsOpenImmersion (inc B hcov Y i).left := by
  show IsOpenImmersion (pullback.fst Y.hom ((cov B hcov).f i)); infer_instance

variable (φ : (gf L).obj Y ⟶ B)

/-- The local extensions. -/
noncomputable def ψ (i : (cov B hcov).I₀) : Yi B hcov Y i ⟶ (nn B i).X :=
  ((nn B i).ext (Yi B hcov Y i) (supp_Yi B hcov Y i) ((gf L).map (inc B hcov Y i) ≫ φ)).choose

theorem ψ_spec (i : (cov B hcov).I₀) :
    (gf L).map (ψ B hcov Y φ i) ≫ (nn B i).e.hom = (gf L).map (inc B hcov Y i) ≫ φ :=
  ((nn B i).ext (Yi B hcov Y i) (supp_Yi B hcov Y i) ((gf L).map (inc B hcov Y i) ≫ φ)).choose_spec

/-- The cover of `Y` by its pieces. -/
noncomputable abbrev 𝒱 : Y.left.OpenCover := (cov B hcov).pullback₁ Y.hom

theorem compat {i j : (cov B hcov).I₀} (hij : i ⟶ j) :
    (𝒱 B hcov Y).trans hij ≫ (ψ B hcov Y φ j).left ≫ colimit.ι (gd B hcov).functor j =
      (ψ B hcov Y φ i).left ≫ colimit.ι (gd B hcov).functor i := by
  have htm : (𝒱 B hcov Y).trans hij ≫ pullback.fst Y.hom ((cov B hcov).f j) =
      pullback.fst Y.hom ((cov B hcov).f i) := Scheme.Cover.trans_map (𝒱 B hcov Y) hij
  let t' : Yi B hcov Y i ⟶ Yi B hcov Y j := Over.homMk ((𝒱 B hcov Y).trans hij) (by
    show _ ≫ pullback.fst Y.hom ((cov B hcov).f j) ≫ Y.hom = pullback.fst Y.hom ((cov B hcov).f i) ≫ Y.hom
    rw [← Category.assoc, htm])
  have ht : t' ≫ inc B hcov Y j = inc B hcov Y i := Over.OverMorphism.ext htm
  have key : t' ≫ ψ B hcov Y φ j = ψ B hcov Y φ i ≫ tr B (leOfHom hij) := by
    apply (nn B j).inj
    rw [CategoryTheory.Functor.map_comp, Category.assoc, ψ_spec, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, ht, CategoryTheory.Functor.map_comp, Category.assoc,
      tr_spec, ψ_spec]
  have k2 := congrArg (fun t => t.left) key
  simp only [Over.comp_left] at k2
  rw [← Category.assoc]
  change t'.left ≫ _ ≫ _ = _
  rw [← Category.assoc, k2, Category.assoc]
  congr 1
  exact colimit.w (gd B hcov).functor hij

theorem fac (i : (cov B hcov).I₀) :
    ((ψ B hcov Y φ i).left ≫ colimit.ι (gd B hcov).functor i) ≫ (N B hcov).hom =
      (𝒱 B hcov Y).f i ≫ Y.hom := by
  show _ ≫ (gd B hcov).toBase = _
  rw [Category.assoc, Scheme.Cover.RelativeGluingData.ι_toBase]
  show _ ≫ toU B hcov i ≫ (cov B hcov).f i = _
  rw [toU_ι]
  exact Over.w (ψ B hcov Y φ i)

/-- The glued extension. -/
noncomputable def ext : Y ⟶ N B hcov :=
  Scheme.OpenCover.glueMorphismsOverOfLocallyDirected (𝒱 B hcov Y)
    (fun i => (ψ B hcov Y φ i).left ≫ colimit.ι (gd B hcov).functor i)
    (fun hij => compat B hcov Y φ hij) (fac B hcov Y φ)

theorem ext_spec : (gf L).map (ext B hcov Y φ) ≫ (eN B hcov).hom = φ := by
  haveI : IsIso ((gf L).map (inc B hcov Y (i0 B hcov))) :=
    isIso_gf_map L (inc B hcov Y (i0 B hcov)) (i0 B hcov).1 (i0 B hcov).2.1 (fun y hy => by
      show y ∈ Set.range (pullback.fst Y.hom ((cov B hcov).f (i0 B hcov)))
      rw [Scheme.Pullback.range_fst]
      exact mem_range_ι _ _ hy)
  have hf0 : inc B hcov Y (i0 B hcov) ≫ ext B hcov Y φ = ψ B hcov Y φ (i0 B hcov) ≫ ιN B hcov (i0 B hcov) := by
    apply Over.OverMorphism.ext
    show (𝒱 B hcov Y).f (i0 B hcov) ≫ (ext B hcov Y φ).left = _
    rw [ext, Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left]
    rfl
  rw [← cancel_epi ((gf L).map (inc B hcov Y (i0 B hcov))), ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, hf0, CategoryTheory.Functor.map_comp]
  simp only [eN, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  exact ψ_spec B hcov Y φ (i0 B hcov)

end Ext

/-- **Glue N1-g3 (proved).** If every point of `Spec 𝓞_L` has an open neighbourhood over which `B` has a
Néron model, then `B` has a Néron model over `Spec 𝓞_L`. -/
noncomputable def glued : NeronOn L B ⊤ where
  X := N B hcov
  supp := Scheme.Hom.preimage_top _
  smooth := prop_N B hcov @Smooth (fun i => (nn B i).smooth)
  sep := prop_N B hcov @IsSeparated (fun i => (nn B i).sep)
  qc := prop_N B hcov @QuasiCompact (fun i => (nn B i).qc)
  e := eN B hcov
  ext := fun Y _ _ φ => ⟨ext B hcov Y φ, ext_spec B hcov Y φ⟩

end Glue

end NeronExt
