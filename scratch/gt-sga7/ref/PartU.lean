import ShP

/-! # sh-printed2, Part U: the uses of the two fields, with the char-0 statements

c-to-printed uses `BLR_1_2_4` once (`neronLocalizesDVR_of_printed`, at a number field) and `SGA7_IX_3_3` once
(`identityComponentBaseChangeDVRRange_of`, whose result `IdentityComponentBaseChangeDVRRange` is used once,
in `semistableNeronBaseChange_of_printed_full`, at a number field `L` and a discrete valuation ring `O` of `L`).
The char-0 forms suffice: the two theorems are copied verbatim below (`…0`), the only changes being the
hypotheses `BLR_1_2_4_0`, `SGA7_IX_3_3_0`, the intro pattern of the restricted Prop, and one `haveI` giving
`PerfectField κ(O)` (the residue field of a DVR of a number field is finite). -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ReductSplit ReductGlue CToPrinted

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace SHPrinted2

/-- The residue field of a discrete valuation ring of a number field is finite (it is `𝓞_L/𝔭` for the
center `𝔭`). -/
theorem finite_residueField {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : Finite (IsLocalRing.ResidueField O) := by
  haveI := center_isMaximal O
  letI := algOL O
  haveI := isLocalization_center O
  let e : O ≃+* Localization.AtPrime (center O) :=
    (IsLocalization.algEquiv (center O).primeCompl O (Localization.AtPrime (center O))).toRingEquiv
  let e2 := IsLocalRing.ResidueField.mapEquiv e
  let e3 := RingEquiv.ofBijective _ (center O).bijective_algebraMap_quotient_residueField
  exact Finite.of_equiv _ (e3.trans e2.symm).toEquiv

/-- ... hence perfect. -/
theorem perfectField_residueField {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : PerfectField (IsLocalRing.ResidueField O) := by
  haveI := finite_residueField O
  infer_instance

open ReductSplit in
/-- reduct-split's local `IdentityComponentBaseChangeDVR` with the connectedness hypotheses on `U` replaced
by `Set.range i = 𝒩⁰` (the form in which it is used below). -/
def IdentityComponentBaseChangeDVRRange0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) (A : PkgI3.AbVar K),
    HasSemistableReduction A O →
    ∀ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel →
    ∀ 𝒩' : GroupModelO (A.baseChange K') O', 𝒩'.IsNeronModel →
    ∀ (U : Over (Spec (CommRingCat.of O))) [GrpObj U] (i : U ⟶ 𝒩.G), IsOpenImmersion i.left →
      IsMonHom i → Set.range i.left = idCompSet 𝒩.G →
      ∃ j : (Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U ⟶ 𝒩'.G,
        IsOpenImmersion j.left ∧
        (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (comapHom hO)))).obj U) :=
          Functor.grpObjObj
         IsMonHom j)

open ReductSplit in
/-- **`IdentityComponentBaseChangeDVRRange`, PROVED** from the printed SGA 3 VI_B 3.10, SGA 7 IX 3.3 and the
bundle leaf `AVGlue.GeomConnOfRationalPoint` (the argument of `identityComponentFromPrinted_of`). -/
theorem identityComponentBaseChangeDVRRange0_of (h3 : SGA3_VIB_3_10) (h7 : SGA7_IX_3_3_0)
    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRange0 := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hss 𝒩 h𝒩 𝒩' h𝒩' U _ i hoi hmi hri
  have gb := idCompBaseChangeDVR_of h3 hG
  let N := ReductGlue.bcDVR hO 𝒩
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of O')))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (N.G ⊗ N.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  obtain ⟨c, hc⟩ := (h𝒩' N.G).2 N.gen.hom
  simp only at hc
  have hcm : IsMonHom c :=
    ReductGlue.isMonHom_of_ext (Over.pullback (jO O')) N.gen.hom 𝒩'.gen.hom N.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 c hc
  have hciso : IsIso ((Over.pullback (jO O')).map c) := by
    have : IsIso ((Over.pullback (jO O')).map c ≫ 𝒩'.gen.hom) := by
      rw [hc]; exact Iso.isIso_hom N.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := h3 _ (bcO hO 𝒩.G)
  let W : (bcO hO 𝒩.G).left.Opens := ⟨idCompSet (bcO hO 𝒩.G), hW⟩
  obtain ⟨hWo, -⟩ := h7 K O K' O' hO A hss 𝒩 h𝒩 𝒩' h𝒩' c hcm hciso W rfl
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  let k := (Over.pullback g).map i
  haveI : IsOpenImmersion i.left := hoi
  haveI : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
  have hkmap : k.left = pullback.map U.hom g 𝒩.G.hom g i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = Set.range W.ι := by
    rw [Scheme.Opens.range_ι, hkmap, Scheme.Pullback.range_map]
    have hga := hri
    have hgb := gb K O K' O' hO 𝒩.G
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hga]
    exact hgb
  refine ⟨k ≫ c, ?_, ?_⟩
  · show IsOpenImmersion (k.left ≫ c.left)
    have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac k.left W.ι hrk
    generalize IsOpenImmersion.isoOfRangeEq k.left W.ι hrk = eW at hfac
    have e : k.left ≫ c.left = eW.hom ≫ (W.ι ≫ c.left) := by
      rw [← hfac]
      exact Category.assoc _ _ _
    rw [e]
    haveI := hWo
    infer_instance
  · letI : GrpObj ((Over.pullback g).obj U) := Functor.grpObjObj
    have hk : IsMonHom k := inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ hk hcm


open ReductSplit ReductGlue ZInQ.HeightSplit ZInQ.DefFaltings in
/-- **The field `semistableNeronBaseChange` (SS2) from published-form leaves alone** (compiled): BLR 1.2/4,
SGA 3 VI_B 3.10, SGA 7 IX 3.3, EGA IV 8.10.5 (open immersions) and the bundle leaf
`AVGlue.GeomConnOfRationalPoint` (Stacks 04KV). No glue Prop is left. -/
theorem semistableNeronBaseChange_of_printed_full0 (hB : BLR_1_2_4_0) (h3 : SGA3_VIB_3_10)
    (h7 : SGA7_IX_3_3_0) (hE : EGAIV_8_10_5_openImm) (hG : AVGlue.GeomConnOfRationalPoint) :
    ZInQ.HeightSplit.SemistableNeronBaseChange := by
  have hIC := identityComponentOLRange_of h3 hG
  have h33 := identityComponentBaseChangeDVRRange0_of h3 h7 hG
  have hOI := openImmersionLocalization hE
  have hL := neronLocalizesDVR_of_printed0 hB
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  obtain ⟨𝒢₀, i, hoi, hmi, hri⟩ := hIC K A L 𝒩
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  let gLL : Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  let 𝒱 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒩
  let 𝒰 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒢₀
  let jL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of (𝓞 L')) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L'))
  letI : GrpObj ((Over.pullback jL').obj 𝒰.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback jL').obj 𝒩'.G) := Functor.grpObjObj
  obtain ⟨j, hj⟩ := (h𝒩' 𝒰.G).2 𝒰.gen.hom
  simp only at hj
  haveI : Smooth (𝟙_ (Over (Spec (CommRingCat.of (𝓞 L'))))).hom :=
    ZInQ.Contrib.NeronC.smooth_tensorUnit _
  haveI : Smooth (𝒰.G ⊗ 𝒰.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  have hjm : IsMonHom j :=
    isMonHom_of_ext (Over.pullback jL') 𝒰.gen.hom 𝒩'.gen.hom 𝒰.gen_hom 𝒩'.gen_hom
      (h𝒩' _).1 (h𝒩' _).1 j hj
  haveI := hmi
  letI : GrpObj ((Over.pullback gLL).obj 𝒢₀.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback gLL).obj 𝒩.G) := Functor.grpObjObj
  refine ⟨𝒰, 𝒱, ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 𝒱.G))⟩, ⟨j, ?_, hjm⟩,
    ⟨(Over.pullback gLL).map i, ZInQ.H5Glue.isOpenImmersion_pullback_map _ i,
      (inferInstance : IsMonHom ((Over.pullback gLL).map i))⟩⟩
  -- `j` is an open immersion: check at every DVR `O'` of `L'`
  refine hOI L' 𝒰.G 𝒩'.G j (fun O' _ => ?_)
  let O : ValuationSubring L := O'.comap (algebraMap L L')
  haveI : IsDiscreteValuationRing O := dvrComapFinite L L' O' inferInstance
  haveI := center_isMaximal O
  have hO : O'.comap (algebraMap L L') = O := rfl
  have hssO : HasSemistableReduction (A.baseChange L) O :=
    (semistableLocalGlobal_leaf hL K A L 𝒩 h𝒩).mp hss O inferInstance
  let N := toO 𝒩' O'
  have hN : N.IsNeronModel := hL K A L' 𝒩' h𝒩' O'
  let N' := N.transport (bcbcIso A L L') (bcbcIso_isMonHom A L L')
  have hN' : N'.IsNeronModel := N.transport_isNeronModel _ _ hN
  let U := (Over.pullback (gO O)).obj 𝒢₀.G
  letI : GrpObj U := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒩.G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gO O)).obj 𝒢₀.G) := Functor.grpObjObj
  have hmiO : IsMonHom ((Over.pullback (gO O)).map i) := inferInstance
  -- the image of `U` is the identity component of `𝒩 ×_{𝓞_L} O`
  have hrange : Set.range ((Over.pullback (gO O)).map i).left =
      CToPrinted.idCompSet ((Over.pullback (gO O)).obj 𝒩.G) := by
    haveI : IsOpenImmersion i.left := hoi
    have hkmap : ((Over.pullback (gO O)).map i).left = pullback.map 𝒢₀.G.hom (gO O) 𝒩.G.hom (gO O)
        i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext <;> simp [Over.pullback_map_left]
    rw [hkmap, Scheme.Pullback.range_map]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O)) : Spec (CommRingCat.of O) ⟶ _) :
        Spec (CommRingCat.of O) → Spec (CommRingCat.of O)) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hri]
    exact CToPrinted.idComp_baseChange h3 hG (gO O) 𝒩.G
  haveI : PerfectField (IsLocalRing.ResidueField O) := perfectField_residueField O
  obtain ⟨j', hj'o, hj'm⟩ := h33 L O L' O' hO (A.baseChange L) hssO (toO 𝒩 O)
    (hL K A L 𝒩 h𝒩 O) N' hN' U ((Over.pullback (gO O)).map i)
    (ZInQ.H5Glue.isOpenImmersion_pullback_map _ i) hmiO hrange
  -- compare `T = 𝒰 ×_{𝓞_{L'}} O'` with `U ×_O O'`
  have hsq : gO O' ≫ gLL = Spec.map (CommRingCat.ofHom (comapHom hO)) ≫ gO O := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  let c := isoX (pbCompIso (gO O') gLL _ hsq (Grp.mk 𝒢₀.G)) ≪≫
    (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (comapHom hO))) (gO O) _ rfl (Grp.mk 𝒢₀.G))).symm
  let T := (Over.pullback (gO O')).obj 𝒰.G
  haveI : Smooth T.hom := by change Smooth (pullback.snd 𝒰.G.hom (gO O')); infer_instance
  let j₂ : T ⟶ N.G := c.hom ≫ j'
  haveI : IsOpenImmersion j₂.left := by
    have h1 : IsOpenImmersion c.hom.left := by
      haveI : IsIso c.hom.left := Functor.map_isIso (Over.forget _) c.hom
      infer_instance
    have h2 : IsOpenImmersion j'.left := hj'o
    show IsOpenImmersion (c.hom.left ≫ j'.left)
    exact @IsOpenImmersion.comp _ _ _ _ _ h1 h2
  -- generic identification of `T`
  let eT : (Over.pullback (jO O')).obj T ≅ (A.baseChange L').X :=
    isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒰.G)) ≪≫ 𝒰.gen
  have h₂ : IsIso ((Over.pullback (jO O')).map j₂) := by
    haveI : IsOpenImmersion ((Over.pullback (jO O')).map j₂).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ j₂
    exact isIso_of_openImmersion_of_iso (A.baseChange L') eT N.gen _
  have hcomp := pbCompIso_natural' (jO O') (gO O') _ (jO_gO O') j
  have hjL : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j) := by
    have : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map j ≫
        𝒩'.gen.hom) := by
      rw [hj]; exact Iso.isIso_hom 𝒰.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  have h₁ : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j)) := by
    have : IsIso ((Over.pullback (jO O')).map ((Over.pullback (gO O')).map j) ≫
        (isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒩'.G))).hom) := by
      rw [hcomp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hjL
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this
  exact isOpenImmersion_of_neron N hN T ((Over.pullback (gO O')).map j) j₂ h₁ h₂


/-- The restricted Prop is a specialization of c-to-printed's. -/
theorem identityComponentBaseChangeDVRRange0_of_general (h : IdentityComponentBaseChangeDVRRange) :
    IdentityComponentBaseChangeDVRRange0 :=
  fun K _ _ O _ _ K' _ _ _ O' _ hO A => h K O K' O' hO A

end SHPrinted2

#print axioms SHPrinted2.identityComponentBaseChangeDVRRange0_of
#print axioms SHPrinted2.semistableNeronBaseChange_of_printed_full0
