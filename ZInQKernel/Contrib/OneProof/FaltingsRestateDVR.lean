import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3
import ZInQKernel.Contrib.OneProof.SemistablePrintedReadings
import ZInQKernel.Contrib.OneProof.ChevalleyFree

/-! The DVR dictionary from semistable reduction to the hypotheses of Faltings' Lemma 1. -/

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue CToPrinted DictModels.RaynaudOr SGA3Nbhd
open ZInQ.SemiAbDescend ZInQ.HeightSplit ZInQ.HeightFix
open scoped NumberField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- Base change of a model to the residue field of the DVR itself. -/
noncomputable abbrev closedFibreMap {K : Type} [Field K] (O : ValuationSubring K) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))

/-- Faltings' semiabelian condition, specialized to a DVR and an abelian generic fibre.
The generic fibre is already an abelian variety by the definition of `GroupModelO`. -/
def IsSemiabelianModelO {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    (G : GroupModelO A O) : Prop :=
  letI : GrpObj ((Over.pullback (closedFibreMap O)).obj G.G) := Functor.grpObjObj
  ConnectedSpace ((Over.pullback (closedFibreMap O)).obj G.G).left ∧
    HasSemiAbelianIdCompTorus ((Over.pullback (closedFibreMap O)).obj G.G)

/-- **Published (LEAF).** Faltings, Invent. Math. 73 (1983), p. 350, Lemma 1 (page read by the
reading desk; paper cited in the manuscript). Specialize the normal base to the spectrum of
a DVR and the dense open to its generic point. A homomorphism of the generic fibres of two
semiabelian schemes extends uniquely to a homomorphism. This instance uses only models with
abelian generic fibres. -/
def FaltingsLemma1DVR : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A B : PkgI3.AbVar K) (G : GroupModelO A O) (H : GroupModelO B O),
    IsSemiabelianModelO G → IsSemiabelianModelO H →
    let F := Over.pullback (jO O)
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    letI : GrpObj (F.obj H.G) := Functor.grpObjObj
    ∀ f : F.obj G.G ⟶ F.obj H.G, IsMonHom f →
      ∃! g : G.G ⟶ H.G, IsMonHom g ∧ F.map g = f

private theorem range_pullback {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (i : X ⟶ Y) :
    Set.range ((Over.pullback s).map i).left = pullback.fst Y.hom s ⁻¹' Set.range i.left := by
  have hm : ((Over.pullback s).map i).left =
      pullback.map X.hom s Y.hom s i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [hm, Scheme.Pullback.range_map]
  have h : Set.range ((𝟙 T : T ⟶ T) : T → T) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h, Set.preimage_univ, Set.inter_univ]

/-- The open subgroup with the fibrewise identity component as image has the full generic fibre. -/
private theorem generic_iso_of_range {K : Type} [Field K] {A : PkgI3.AbVar K}
    {O : ValuationSubring K} [IsDiscreteValuationRing O] (G : GroupModelO A O)
    {U : Over (Spec (CommRingCat.of O))} (i : U ⟶ G.G) [IsOpenImmersion i.left]
    (hr : Set.range i.left = idCompSet G.G) : IsIso ((Over.pullback (jO O)).map i) := by
  suffices h : IsIso ((Over.pullback (jO O)).map i).left by
    haveI : IsIso ((Over.forget _).map ((Over.pullback (jO O)).map i)) := h
    exact isIso_of_reflects_iso _ (Over.forget _)
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨ZInQ.H5Glue.isOpenImmersion_pullback_map _ i, ⟨fun z => ?_⟩⟩
  show z ∈ Set.range ((Over.pullback (jO O)).map i).left
  rw [range_pullback, hr]
  apply mem_idCompSet_groupModelO_generic G
  have hw : G.G.hom (pullback.fst G.G.hom (jO O) z) = jO O (pullback.snd G.G.hom (jO O) z) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [hw]
  intro hn
  have hp := congrArg PrimeSpectrum.asIdeal hn
  change Ideal.comap (algebraMap O K) (pullback.snd G.G.hom (jO O) z).asIdeal =
    IsLocalRing.maximalIdeal O at hp
  have h0 : (pullback.snd G.G.hom (jO O) z).asIdeal = ⊥ :=
    (Ideal.eq_bot_or_top _).resolve_right (pullback.snd G.G.hom (jO O) z).isPrime.ne_top
  rw [h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O K)] at hp
  exact (IsDiscreteValuationRing.not_a_field O) hp.symm

/-- A smooth open identity subgroup of a semistable model over a DVR with perfect
residue field has connected semiabelian special fibre. -/
private theorem closed_fibre_of_range {K : Type} [Field K] {A : PkgI3.AbVar K}
    {O : ValuationSubring K} [IsDiscreteValuationRing O] [PerfectField (IsLocalRing.ResidueField O)]
    (G : GroupModelO A O) (hs : G.IsSemistable) (U : GroupModelO A O)
    (i : U.G ⟶ G.G) [IsOpenImmersion i.left] [IsMonHom i]
    (hr : Set.range i.left = idCompSet G.G) : IsSemiabelianModelO U := by
  let k := IsLocalRing.ResidueField O
  let d := closedFibreMap O
  let F := Over.pullback d
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (F.obj U.G) := Functor.grpObjObj
  haveI : LocallyOfFiniteType (F.obj G.G).hom := by
    change LocallyOfFiniteType (pullback.snd G.G.hom d); infer_instance
  haveI : QuasiCompact (F.obj G.G).hom := by
    change QuasiCompact (pullback.snd G.G.hom d); infer_instance
  have hcomp : sφ (φbar k) ≫ d = Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let E := pbCompIso _ _ _ hcomp (Grp.mk G.G)
  letI : GrpObj ((Over.pullback (sφ (φbar k))).obj (F.obj G.G)) := Functor.grpObjObj
  have hgeom : HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj (F.obj G.G)) :=
    @hasSemiAbelian_of_iso _ _ (geomSpecialFibre G)
      ((Over.pullback (sφ (φbar k))).obj (F.obj G.G)) _ _
      (isoX E).symm (inferInstanceAs (IsMonHom E.inv.hom.hom)) hs
  obtain ⟨V, _, j, hj, hjm, hjc, htorus⟩ :=
    ZInQ.ChevFree.semiAbelianDescendsPerfect_proof k (F.obj G.G) hgeom
  haveI := hj
  haveI := hjm
  haveI := hjc
  haveI : IsOpenImmersion (F.map i).left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
  have hEq : Set.range j.left = Set.range (F.map i).left := by
    rw [range_pullback, hr,
      idComp_baseChange' geomConnOfRationalPoint_proof d G.G (isOpen_idCompSet_groupModelO G),
      idCompSet_eq_cc (F.obj G.G) default]
    exact ZInQ.SemistabAssembly.range_eq_connectedComponent j
  let e₀ := IsOpenImmersion.isoOfRangeEq j.left (F.map i).left hEq
  have he₀ : e₀.hom ≫ (F.map i).left = j.left := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let e : V ≅ F.obj U.G := Over.isoMk e₀ (by
    rw [← Over.w (F.map i), ← Category.assoc, he₀, Over.w])
  have hfac : e.hom ≫ F.map i = j := Over.OverMorphism.ext he₀
  haveI : Mono (F.map i) :=
    ⟨fun f g h => Over.OverMorphism.ext ((cancel_mono (F.map i).left).mp
      (by simpa using congrArg CommaMorphism.left h))⟩
  haveI : IsMonHom (e.hom ≫ F.map i) := by rw [hfac]; infer_instance
  have hem : IsMonHom e.hom := isMonHom_of_comp_mono e.hom (F.map i)
  refine ⟨(Scheme.homeoOfIso e₀).connectedSpace_iff.mp hjc, ?_⟩
  exact ⟨V, inferInstance, e.hom, inferInstance, hem, hjc, htorus⟩

/-- The identity component of a semistable model over the DVR is a semiabelian
model with the same generic fibre. -/
private theorem exists_semiabelian_component {K : Type} [Field K] {A : PkgI3.AbVar K}
    {O : ValuationSubring K} [IsDiscreteValuationRing O] [PerfectField (IsLocalRing.ResidueField O)]
    (G : GroupModelO A O) (hs : G.IsSemistable) :
    ∃ (M : GroupModelO A O) (i : M.G ⟶ G.G), IsOpenImmersion i.left ∧ IsMonHom i ∧
      Set.range i.left = idCompSet G.G ∧ IsSemiabelianModelO M := by
  let W : G.G.left.Opens := ⟨idCompSet G.G, isOpen_idCompSet_groupModelO G⟩
  have gc := idCompSubgroup_proof geomConnOfRationalPoint_proof _ G.G
  have hW : OpenSub.IsSubgroupOpen G.G W :=
    { one := fun s => idCompSet_one G.G s
      mul := gc.1
      inv := gc.2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  let i := OpenSub.incl W
  haveI hi : IsMonHom i := OpenSub.isMonHom_incl hW
  haveI ho : IsOpenImmersion i.left := show IsOpenImmersion W.ι from inferInstance
  haveI : Smooth (OpenSub.G0 W).hom := show Smooth (W.ι ≫ G.G.hom) from inferInstance
  haveI : IsSeparated (OpenSub.G0 W).hom := show IsSeparated (W.ι ≫ G.G.hom) from inferInstance
  haveI : QuasiCompact (OpenSub.G0 W).hom := by
    haveI : IsLocallyNoetherian G.G.left := LocallyOfFiniteType.isLocallyNoetherian G.G.hom
    haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
    haveI : IsNoetherian G.G.left := {}
    show QuasiCompact (W.ι ≫ G.G.hom)
    infer_instance
  have hr : Set.range i.left = idCompSet G.G := Scheme.Opens.range_ι W
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj (OpenSub.G0 W)) := Functor.grpObjObj
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  haveI : IsIso (F.map i) := generic_iso_of_range G i hr
  haveI : IsMonHom G.gen.hom := G.gen_hom
  let M : GroupModelO A O :=
    { G := OpenSub.G0 W
      gen := asIso (F.map i) ≪≫ G.gen
      gen_hom := by
        show IsMonHom (F.map i ≫ G.gen.hom)
        infer_instance }
  exact ⟨M, i, ho, hi, hr, closed_fibre_of_range G hs M i hr⟩

/-- Faltings' Lemma 1 identifies the two open identity components. When the target
is Néron, this isomorphism agrees with the restriction of the given generic
isomorphism's Néron extension. The source can already be a base changed model. -/
theorem identityComponent_of_faltingsLemma1 (hF : FaltingsLemma1DVR)
    {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}
    [IsDiscreteValuationRing O] [PerfectField (IsLocalRing.ResidueField O)]
    (G N : GroupModelO A O) (hsG : G.IsSemistable) (hsN : N.IsSemistable)
    (hN : N.IsNeronModel) (c : G.G ⟶ N.G) [IsMonHom c]
    [IsIso ((Over.pullback (jO O)).map c)] (W : G.G.left.Opens)
    (hW : (W : Set G.G.left) = idCompSet G.G) :
    IsOpenImmersion (W.ι ≫ c.left) ∧ Set.range (W.ι ≫ c.left) = idCompSet N.G := by
  obtain ⟨U, i, hoi, hmi, hri, hsU⟩ := exists_semiabelian_component G hsG
  obtain ⟨V, j, hoj, hmj, hrj, hsV⟩ := exists_semiabelian_component N hsN
  haveI := hoi
  haveI := hmi
  haveI := hoj
  haveI := hmj
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj U.G) := Functor.grpObjObj
  letI : GrpObj (F.obj V.G) := Functor.grpObjObj
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (F.obj N.G) := Functor.grpObjObj
  haveI : IsIso (F.map i) := generic_iso_of_range G i hri
  haveI : IsIso (F.map j) := generic_iso_of_range N j hrj
  haveI : IsIso (F.map c) := ‹IsIso ((Over.pullback (jO O)).map c)›
  haveI : IsMonHom (inv (F.map j) ≫ F.map j) := by simp; infer_instance
  haveI : IsMonHom (inv (F.map j)) := isMonHom_of_comp_mono _ (F.map j)
  let f := F.map i ≫ F.map c ≫ inv (F.map j)
  haveI : IsMonHom f := by dsimp [f]; infer_instance
  haveI : IsIso f := by dsimp [f]; infer_instance
  haveI : IsMonHom (inv f ≫ f) := by simp; infer_instance
  haveI : IsMonHom (inv f) := isMonHom_of_comp_mono _ f
  obtain ⟨u, hu, huniqU⟩ := hF K O A A U V hsU hsV f inferInstance
  obtain ⟨v, hv, huniqV⟩ := hF K O A A V U hsV hsU (inv f) inferInstance
  haveI := hu.1
  haveI := hv.1
  have huvid : u ≫ v = 𝟙 _ := by
    obtain ⟨z, _, hz⟩ := hF K O A A U U hsU hsU (𝟙 _) inferInstance
    exact (hz _ ⟨inferInstance, by rw [Functor.map_comp, hu.2, hv.2]; simp⟩).trans
      (hz _ ⟨inferInstance, F.map_id _⟩).symm
  have hvuid : v ≫ u = 𝟙 _ := by
    obtain ⟨z, _, hz⟩ := hF K O A A V V hsV hsV (𝟙 _) inferInstance
    exact (hz _ ⟨inferInstance, by rw [Functor.map_comp, hv.2, hu.2]; simp⟩).trans
      (hz _ ⟨inferInstance, F.map_id _⟩).symm
  let e : U.G ≅ V.G := ⟨u, v, huvid, hvuid⟩
  have hfac : i ≫ c = u ≫ j := (hN U.G).1 (by
    change F.map (i ≫ c) ≫ N.gen.hom = F.map (u ≫ j) ≫ N.gen.hom
    rw [Functor.map_comp, Functor.map_comp, hu.2]
    simp [f])
  have hriW : Set.range W.ι = Set.range i.left := by rw [Scheme.Opens.range_ι, hW, hri]
  let eW := IsOpenImmersion.isoOfRangeEq W.ι i.left hriW
  have heW : eW.hom ≫ i.left = W.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hc : W.ι ≫ c.left = eW.hom ≫ e.hom.left ≫ j.left := by
    rw [← heW, Category.assoc]
    exact congrArg (eW.hom ≫ ·) (congrArg CommaMorphism.left hfac)
  rw [hc]
  haveI : IsIso e.hom := Iso.isIso_hom e
  haveI : IsIso e.hom.left := Functor.map_isIso (Over.forget _) e.hom
  refine ⟨inferInstance, ?_⟩
  have hs : Function.Surjective (eW.hom ≫ e.hom.left) :=
    (Scheme.homeoOfIso (asIso (eW.hom ≫ e.hom.left))).surjective
  rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hs, Set.image_univ, hrj]

/-- Apply the DVR comparison to a supplied open subgroup representing the original
identity component. This is the local input for the number field argument. -/
theorem identityComponentBaseChangeDVRRange_of_faltingsLemma1
    (hF : FaltingsLemma1DVR)
    {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    {O : ValuationSubring K} {O' : ValuationSubring K'}
    [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
    [PerfectField (IsLocalRing.ResidueField O')]
    (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K)
    (N : GroupModelO A O) (hN : N.IsNeronModel) (hs : HasSemistableReduction A O)
    (N' : GroupModelO (A.baseChange K') O') (hN' : N'.IsNeronModel)
    (hs' : N'.IsSemistable)
    (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ N.G)
    [IsOpenImmersion i.left] [IsMonHom i] (hri : Set.range i.left = idCompSet N.G) :
    let F := Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))
    letI : GrpObj (F.obj U) := Functor.grpObjObj
    ∃ m : F.obj U ⟶ N'.G, IsOpenImmersion m.left ∧ IsMonHom m := by
  let G := bcDVR hO N
  have hsG : G.IsSemistable := (isSemistable_bcDVR_iff hO (GapPersists.isAlgebraic_resMap hO) N).mp
    (semistableNeronModels_of_has hs N hN)
  let d := Spec.map (CommRingCat.ofHom (comapHom hO))
  let k := (Over.pullback d).map i
  letI : GrpObj ((Over.pullback d).obj U) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback d).obj N.G) := Functor.grpObjObj
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O')))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (G.G ⊗ G.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  obtain ⟨c, hc⟩ := (hN' G.G).2 G.gen.hom
  simp only at hc
  have hcm : IsMonHom c :=
    isMonHom_of_ext (Over.pullback (jO O')) G.gen.hom N'.gen.hom G.gen_hom N'.gen_hom
      (hN' _).1 (hN' _).1 c hc
  haveI : IsIso ((Over.pullback (jO O')).map c) := by
    have : IsIso ((Over.pullback (jO O')).map c ≫ N'.gen.hom) := by rw [hc]; infer_instance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom N'.gen) this
  let W : ((Over.pullback d).obj N.G).left.Opens :=
    ⟨idCompSet ((Over.pullback d).obj N.G), isOpen_idCompSet_groupModelO G⟩
  haveI := hcm
  have hWo := (identityComponent_of_faltingsLemma1 hF G N' hsG hs' hN' c W rfl).1
  haveI : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
  have hr : Set.range k.left = Set.range W.ι := by
    rw [Scheme.Opens.range_ι, range_pullback, hri]
    exact idComp_baseChange' geomConnOfRationalPoint_proof d N.G (isOpen_idCompSet_groupModelO N)
  have hk : IsMonHom k := inferInstance
  refine ⟨k ≫ c, ?_, @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hk hcm⟩
  haveI : IsOpenImmersion W.ι := inferInstance
  let eW := IsOpenImmersion.isoOfRangeEq k.left W.ι hr
  have hfac : eW.hom ≫ W.ι = k.left := IsOpenImmersion.isoOfRangeEq_hom_fac k.left W.ι hr
  let cS : ((Over.pullback d).obj N.G).left ⟶ N'.G.left := c.left
  have hw : k.left ≫ cS = eW.hom ≫ (W.ι ≫ cS) :=
    (congrArg (fun m => m ≫ cS) hfac.symm).trans (Category.assoc _ _ _)
  change IsOpenImmersion (k.left ≫ cS)
  rw [hw]
  haveI : IsOpenImmersion (W.ι ≫ cS) := hWo
  infer_instance

end ZInQ.FaltingsRestate
