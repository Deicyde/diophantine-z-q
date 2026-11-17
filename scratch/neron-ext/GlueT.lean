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

/-- An open immersion of `S`-schemes which is surjective over an open `U` containing the generic
point induces an isomorphism of generic fibres. -/
theorem isIso_gf_map {X X' : Over (S L)} (ι : X' ⟶ X) [IsOpenImmersion ι.left] (U : (S L).Opens)
    (hU : (jL L) ⁻¹ᵁ U = ⊤) (hr : ∀ x : X.left, X.hom x ∈ U → x ∈ Set.range ι.left) :
    IsIso ((gf L).map ι) := by
  have hrange : Set.range (pullback.fst X.hom (jL L)) ⊆ Set.range ι.left := by
    rintro _ ⟨z, rfl⟩
    apply hr
    have h1 : X.hom (pullback.fst X.hom (jL L) z) = jL L (pullback.snd X.hom (jL L) z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    have : pullback.snd X.hom (jL L) z ∈ (jL L) ⁻¹ᵁ U := by rw [hU]; trivial
    exact this
  let a : pullback X.hom (jL L) ⟶ X'.left := IsOpenImmersion.lift ι.left _ hrange
  have ha : a ≫ ι.left = pullback.fst X.hom (jL L) := IsOpenImmersion.lift_fac _ _ _
  have hc : a ≫ X'.hom = pullback.snd X.hom (jL L) ≫ jL L := by
    rw [← Over.w ι, ← Category.assoc, ha, pullback.condition]
  let inv : (gf L).obj X ⟶ (gf L).obj X' :=
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

end Glue
end NeronExt
