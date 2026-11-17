import ZInQKernel.Contrib.OneProof.SGA7IX33SHPre
import ZInQKernel.Contrib.OneProof.PersistsDVR
import ZInQKernel.Contrib.OneProof.SGA3IdComp

/-!
# sga3-nbhd: `G⁰` over discrete valuation rings, and the DVR readers of SGA 3 VI_B 3.10 without it

`SGA3IdComp.SGA3_VIB_3_10_Nbhd` (the research field `sga3_VIB_3_10_Nbhd`) reaches the chain only through
`CToPrinted.SGA3_VIB_3_10`. Over a DVR that statement is elementary for the chain's group models; this file proves
* `SGA3Nbhd.isClosed_fibre_diff`, `SGA3Nbhd.isOpen_idCompSet_of_finite`: for a smooth group scheme `G → S`, `G⁰` is
  open if the fibres are preconnected outside finitely many closed points (the special fibre is closed and its
  identity component is open in it);
* `SGA3Nbhd.isOpen_idCompSet_groupModelO`: `G⁰` is open for every `ReductSplit.GroupModelO` over a DVR;
* `SGA3Nbhd.idComp_baseChange'`, `SGA3Nbhd.idCompSubgroup_proof`,
  `SGA3Nbhd.identityComponentBaseChangeDVRRange_proof`: the chain's glue with `IsOpen (idCompSet G)` for the one
  `G` used, or with no SGA 3 hypothesis;
* leaf-free versions of the chain's DVR readers: `SGA3Nbhd.NF.sga7_IX_3_3_of_SH'`,
  `SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH'`, `SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'` (same statements as the
  originals, without the `SGA3_VIB_3_10` argument).
The remaining reader, over `𝓞_L`, is `SemistableNeronBaseChangeNoSGA3.lean`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits Topology TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj CToPrinted
open NumberField

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



/-- **`CToPrinted.idComp_baseChange` with `IsOpen (idCompSet G)` for the one `G` used** (SGA 3 VI_B 3.3; the
proof of `idComp_baseChange` with `h3 S G` replaced by `hW3`; original doc: from the printed
SGA 3 VI_B 3.10 and the bundle leaf `AVGlue.GeomConnOfRationalPoint`, Stacks 04KV), for a smooth quasi-compact
group scheme over a noetherian scheme and any base change `g : S' → S`. For `s' ∈ S'`, the set
`P = {w : fst w ∈ G⁰, w over s'}` is the image of `G⁰ ×_S Spec κ(s')`, which is connected
(`connectedSpace_pullback_idComp`), so `P ⊆ (G ×_S S')⁰`; conversely the image under `fst` of the component of
`e'(s')` is a connected subset of `G_{g(s')}` containing `e(g(s'))`. -/
theorem idComp_baseChange' (hG : AVGlue.GeomConnOfRationalPoint)
    {S S' : Scheme.{0}} [IsNoetherian S] (g : S' ⟶ S) (G : Over S) [GrpObj G] [Smooth G.hom]
    [QuasiCompact G.hom] (hW3 : IsOpen (idCompSet G)) :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    pullback.fst G.hom g ⁻¹' idCompSet G = idCompSet ((Over.pullback g).obj G) := by
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  let W : G.left.Opens := ⟨idCompSet G, hW3⟩
  have hW : (W : Set G.left) = idCompSet G := rfl
  haveI : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  haveI : IsNoetherian G.left := {}
  let e' := (η[(Over.pullback g).obj G] : 𝟙_ (Over S') ⟶ _).left
  let e := (η[G] : 𝟙_ (Over (S)) ⟶ G).left
  have hu1 : ∀ s', pullback.fst G.hom g (e' s') = e (g s') := by
    intro s'
    rw [← Scheme.Hom.comp_apply, unit_bc_fst g G, Scheme.Hom.comp_apply]
  have hu2 : ∀ s', pullback.snd G.hom g (e' s') = s' := by
    intro s'
    show ((Over.pullback g).obj G).hom (e' s') = s'
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  have hfib : ∀ w : ((Over.pullback g).obj G).left, G.hom (pullback.fst G.hom g w) = g (pullback.snd G.hom g w) := by
    intro w
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  -- the sets `P s'` are preconnected
  have hP : ∀ s' : S', _root_.IsPreconnected
      {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
    intro s'
    let f0 := W.ι ≫ G.hom
    let m2 := pullback.map f0 g G.hom g W.ι (𝟙 _) (𝟙 _) (by simp [f0]) (by simp)
    let r := (S').fromSpecResidueField s'
    let m1 := pullback.fst (pullback.snd f0 g) r
    haveI hc : ConnectedSpace ↥(pullback f0 (r ≫ g)) :=
      connectedSpace_pullback_idComp hG G W hW
        (↑((S').residueField s')) (r ≫ g)
    haveI : ConnectedSpace ↥(pullback (pullback.snd f0 g) r) :=
      (Scheme.homeoOfIso (pullbackLeftPullbackSndIso f0 g r)).connectedSpace_iff.mpr hc
    have hrange : Set.range (m1 ≫ m2) =
        {w : ((Over.pullback g).obj G).left | pullback.fst G.hom g w ∈ W ∧ pullback.snd G.hom g w = s'} := by
      ext w
      constructor
      · rintro ⟨u, rfl⟩
        constructor
        · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_fst, ← Category.assoc,
            Scheme.Hom.comp_apply]
          have : W.ι ((m1 ≫ pullback.fst f0 g) u) ∈ Set.range W.ι := ⟨_, rfl⟩
          rwa [Scheme.Opens.range_ι] at this
        · rw [← Scheme.Hom.comp_apply, Category.assoc, pullback.lift_snd, Category.comp_id,
            pullback.condition, Scheme.Hom.comp_apply]
          have : r (pullback.snd (pullback.snd f0 g) r u) ∈ Set.range r := ⟨_, rfl⟩
          rwa [Scheme.range_fromSpecResidueField] at this
      · rintro ⟨h1, h2⟩
        have hw : w ∈ Set.range m2 := by
          rw [Scheme.Pullback.range_map]
          refine ⟨?_, ⟨pullback.snd G.hom g w, rfl⟩⟩
          show pullback.fst G.hom g w ∈ Set.range W.ι
          rw [Scheme.Opens.range_ι]
          exact h1
        obtain ⟨v, rfl⟩ := hw
        have hv : pullback.snd f0 g v ∈ Set.range r := by
          rw [Scheme.range_fromSpecResidueField]
          have : (m2 ≫ pullback.snd G.hom g) v = s' := h2
          rw [pullback.lift_snd, Category.comp_id] at this
          exact this
        have hv' : v ∈ Set.range m1 := by
          rw [Scheme.Pullback.range_fst]
          exact hv
        obtain ⟨u, rfl⟩ := hv'
        exact ⟨u, rfl⟩
    rw [← hrange]
    exact (isConnected_range (m1 ≫ m2).continuous).isPreconnected
  ext z
  constructor
  · intro hz
    let s' := pullback.snd G.hom g z
    show z ∈ connectedComponentIn (((Over.pullback g).obj G).hom ⁻¹' {((Over.pullback g).obj G).hom z}) (e' (((Over.pullback g).obj G).hom z))
    refine (hP s').subset_connectedComponentIn ⟨?_, hu2 s'⟩ ?_ ⟨hz, rfl⟩
    · rw [hu1]
      exact idCompSet_one G (g s')
    · rintro w ⟨-, hw⟩
      exact hw
  · intro hz
    let s' := pullback.snd G.hom g z
    have hz' : z ∈ connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s') := hz
    set C := connectedComponentIn (pullback.snd G.hom g ⁻¹' {s'}) (e' s')
    have hC : _root_.IsPreconnected (pullback.fst G.hom g '' C) :=
      isPreconnected_connectedComponentIn.image _ (pullback.fst G.hom g).continuous.continuousOn
    have hsub : pullback.fst G.hom g '' C ⊆ G.hom ⁻¹' {g s'} := by
      rintro _ ⟨w, hw, rfl⟩
      show G.hom (pullback.fst G.hom g w) = g s'
      rw [hfib]
      exact congrArg g (connectedComponentIn_subset (pullback.snd G.hom g ⁻¹' {s'}) _ hw)
    have hmem : e (g s') ∈ pullback.fst G.hom g '' C :=
      ⟨e' s', mem_connectedComponentIn (hu2 s'), hu1 s'⟩
    have := hC.subset_connectedComponentIn hmem hsub ⟨z, hz', rfl⟩
    show pullback.fst G.hom g z ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (pullback.fst G.hom g z)})
      (e (G.hom (pullback.fst G.hom g z)))
    rw [hfib]
    exact this

/-- **The glue `IdCompSubgroup` with no SGA 3 hypothesis**: multiplication by `SGA3IdComp.mul_mem` (any base,
from Stacks 04KV), inversion by the argument of `CToPrinted.idCompSubgroup_of` (which never used openness). -/
theorem idCompSubgroup_proof (hG : AVGlue.GeomConnOfRationalPoint) : IdCompSubgroup := by
  intro S _ G _ _ _
  let e := (η[G] : 𝟙_ (Over S) ⟶ G).left
  have he : ∀ s, G.hom (e s) = s := by
    intro s
    rw [← Scheme.Hom.comp_apply, Over.w]
    rfl
  constructor
  · intro z hz1 hz2
    exact SGA3IdComp.mul_mem G hG z hz1 hz2
  · intro x hx
    let ιl := (GrpObj.inv : G ⟶ G).left
    have hι : ∀ y, G.hom (ιl y) = G.hom y := by
      intro y
      rw [← Scheme.Hom.comp_apply, Over.w]
    let C := connectedComponentIn (G.hom ⁻¹' {G.hom x}) (e (G.hom x))
    have hC : _root_.IsPreconnected (ιl '' C) :=
      isPreconnected_connectedComponentIn.image _ ιl.continuous.continuousOn
    have hsub : ιl '' C ⊆ G.hom ⁻¹' {G.hom x} := by
      rintro _ ⟨y, hy, rfl⟩
      show G.hom (ιl y) = G.hom x
      rw [hι]
      exact connectedComponentIn_subset (G.hom ⁻¹' {G.hom x}) _ hy
    have hes : e (G.hom x) ∈ ιl '' C := by
      refine ⟨e (G.hom x), mem_connectedComponentIn (he _), ?_⟩
      show ιl (e (G.hom x)) = e (G.hom x)
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, GrpObj.one_inv]
    have := hC.subset_connectedComponentIn hes hsub ⟨x, hx, rfl⟩
    show ιl x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom (ιl x)}) (e (G.hom (ιl x)))
    rw [hι]
    exact this

open ReductSplit in
/-- **`IdentityComponentBaseChangeDVRRange` with no SGA 3 hypothesis** (`G⁰` open over a DVR is proved here), from SGA 7 IX 3.3 and the
bundle leaf `AVGlue.GeomConnOfRationalPoint` (the argument of `identityComponentFromPrinted_of`). -/
theorem identityComponentBaseChangeDVRRange_proof (h7 : SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : IdentityComponentBaseChangeDVRRange := by
  intro K _ O _ K' _ _ _ O' _ hO A hss 𝒩 h𝒩 𝒩' h𝒩' U _ i hoi hmi hri
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
  have hW : IsOpen (idCompSet (bcO hO 𝒩.G)) := isOpen_idCompSet_groupModelO (ReductGlue.bcDVR hO 𝒩)
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
    have hgb := idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G
      (isOpen_idCompSet_groupModelO 𝒩)
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



end SGA3Nbhd


namespace SGA3Nbhd.NF

open ReductSplit ReductGlue SGA7PersistsNF

/-- `SGA7PersistsNF.body_of_SH` without `SGA3_VIB_3_10` (all bases are DVRs; `G⁰` open there is proved). -/
theorem body_of_SH' {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
    {O' : ValuationSubring K'} [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']
    (hO : O'.comap (algebraMap K K') = O) {E E' : Type} [Field E] [Field E'] [Algebra K E]
    [Algebra K' E'] [Algebra E E'] [Algebra K E'] [IsScalarTower K E E'] [IsScalarTower K K' E']
    {P : ValuationSubring E} {P' : ValuationSubring E'} [IsDiscreteValuationRing P]
    [IsDiscreteValuationRing P'] (hP : P.comap (algebraMap K E) = O)
    (hP' : P'.comap (algebraMap K' E') = O') (hSHP : IsSHNeronExt O P hP)
    (hSHP' : IsSHNeronExt O' P' hP') (hPP' : P'.comap (algebraMap E E') = P)
    (hG : AVGlue.GeomConnOfRationalPoint) (h7 : Body P P' hPP') : Body O O' hO := by
  intro A hss 𝒩 h𝒩 𝒩' h𝒩' c hc hciso U hU
  -- the Néron models over `P` and `P'`
  let 𝒩₁ := bcDVR hP 𝒩
  have h𝒩₁ : 𝒩₁.IsNeronModel := hSHP.2.2 A 𝒩 h𝒩
  have hss₁ : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩₀, h𝒩₀, hs⟩ := hss
    exact ⟨bcDVR hP 𝒩₀, hSHP.2.2 A 𝒩₀ h𝒩₀, (isSemistable_bcDVR_iff hP hSHP.2.1 𝒩₀).mp hs⟩
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  let 𝒩'₁ : GroupModelO ((A.baseChange E).baseChange E') P' :=
    (bcDVR hP' 𝒩').transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he
  have h𝒩'₁ : 𝒩'₁.IsNeronModel :=
    GroupModelO.transport_isNeronModel _ he _ (hSHP'.2.2 (A.baseChange K') 𝒩' h𝒩')
  -- the square of bases `O → O' → P'`, `O → P → P'`
  have sq : gD hP' ≫ gD hO = gD hPP' ≫ gD hP := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    show algebraMap K' E' (algebraMap K K' (x : K)) = algebraMap E E' (algebraMap K E (x : K))
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  -- the comparison map over `P'`
  let Y := bcO hO 𝒩.G
  letI : GrpObj Y := Functor.grpObjObj
  let Y₁ := bcO hPP' 𝒩₁.G
  letI : GrpObj Y₁ := Functor.grpObjObj
  haveI : Smooth Y₁.hom := by change Smooth (pullback.snd _ _); infer_instance
  let eIG := pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G) ≪≫
    (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G)).symm
  let eI : Y₁ ≅ (Over.pullback (gD hP')).obj Y := isoX eIG
  let c₁ : Y₁ ⟶ 𝒩'₁.G := eI.hom ≫ (Over.pullback (gD hP')).map c
  haveI := hc
  haveI := hciso
  letI : GrpObj ((Over.pullback (gD hP')).obj Y) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (gD hP')).obj 𝒩'.G) := Functor.grpObjObj
  have hc₁ : IsMonHom c₁ := by
    have h1 : IsMonHom eI.hom := inferInstanceAs (IsMonHom (isoX eIG).hom)
    have h2 : IsMonHom ((Over.pullback (gD hP')).map c) := inferInstance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ h1 h2
  have hiso₁ : IsIso ((Over.pullback (jO P')).map c₁) := by
    have n1 := pbCompIso_natural' (jO P') (gD hP') _ (jO_gD hP') c
    have n2 := pbCompIso_natural' (sKK (K := K') (K' := E')) (jO O') _ rfl c
    haveI hA : IsIso ((Over.pullback (sKK (K := K') (K' := E') ≫ jO O')).map c) := by
      have : IsIso ((Over.pullback (sKK (K := K') (K' := E'))).map ((Over.pullback (jO O')).map c) ≫
          (isoX (pbCompIso (sKK (K := K') (K' := E')) (jO O') _ rfl (Grp.mk 𝒩'.G))).hom) := by
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) (Iso.isIso_hom _)
      rw [n2] at this
      exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (Iso.isIso_hom _) this
    haveI : IsIso ((Over.pullback (jO P')).map ((Over.pullback (gD hP')).map c)) := by
      have : IsIso ((isoX (pbCompIso (jO P') (gD hP') _ (jO_gD hP') (Grp.mk Y))).hom ≫
          (Over.pullback (sKK (K := K') (K' := E') ≫ jO O')).map c) :=
        @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hA
      rw [← n1] at this
      exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom _) this
    show IsIso ((Over.pullback (jO P')).map (eI.hom ≫ (Over.pullback (gD hP')).map c))
    rw [Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ eI.hom) inferInstance
  let U₁ : Y₁.left.Opens := ⟨idCompSet Y₁, SGA3Nbhd.isOpen_idCompSet_groupModelO (bcDVR hPP' 𝒩₁)⟩
  obtain ⟨ho₁, hr₁⟩ := h7 (A.baseChange E) hss₁ 𝒩₁ h𝒩₁ 𝒩'₁ h𝒩'₁ c₁ hc₁ hiso₁ U₁ rfl
  -- descent along `Spec P' → Spec O'`
  haveI := (flat_surjective_gD hP').1
  haveI := (flat_surjective_gD hP').2
  haveI : IsIso eI.hom.left := Functor.map_isIso (Over.forget _) eI.hom
  let q : Y₁.left ⟶ Y.left := eI.hom.left ≫ pullback.fst Y.hom (gD hP')
  let p : 𝒩'₁.G.left ⟶ 𝒩'.G.left := pullback.fst 𝒩'.G.hom (gD hP')
  haveI : Surjective p := by show Surjective (pullback.fst _ _); infer_instance
  haveI : Flat p := by show Flat (pullback.fst _ _); infer_instance
  haveI : QuasiCompact p := by show QuasiCompact (pullback.fst _ _); infer_instance
  have hsq : IsPullback c₁.left q p c.left := isPullback_bc_iso (gD hP') c eI.hom.left
  have hq : q ≫ pullback.fst 𝒩.G.hom (gD hO) =
      pullback.fst 𝒩₁.G.hom (gD hPP') ≫ pullback.fst 𝒩.G.hom (gD hP) := by
    have e1 := pbCompIso_fst (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G)
    have e2 := pbCompIso_inv_fst (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G)
    have hE : eI.hom.left = (isoX (pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G))).hom.left ≫
        (isoX (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G))).inv.left := rfl
    have e2' : (isoX (pbCompIso (gD hP') (gD hO) _ sq (Grp.mk 𝒩.G))).inv.left ≫
        pullback.fst Y.hom (gD hP') ≫ pullback.fst 𝒩.G.hom (gD hO) =
        pullback.fst 𝒩.G.hom (gD hPP' ≫ gD hP) := e2
    show (eI.hom.left ≫ pullback.fst Y.hom (gD hP')) ≫ pullback.fst 𝒩.G.hom (gD hO) = _
    rw [hE]
    refine Eq.trans ?_ (Eq.trans (congrArg
      ((isoX (pbCompIso (gD hPP') (gD hP) _ rfl (Grp.mk 𝒩.G))).hom.left ≫ ·) e2') e1)
    exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)
  have hU₁ : (U₁ : Set Y₁.left) = q.base ⁻¹' U := by
    have i1 : pullback.fst 𝒩.G.hom (gD hO) ⁻¹' idCompSet 𝒩.G = idCompSet Y :=
      SGA3Nbhd.idComp_baseChange' hG (gD hO) 𝒩.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)
    have i2 : pullback.fst 𝒩.G.hom (gD hP) ⁻¹' idCompSet 𝒩.G = idCompSet 𝒩₁.G :=
      SGA3Nbhd.idComp_baseChange' hG (gD hP) 𝒩.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)
    have i3 : pullback.fst 𝒩₁.G.hom (gD hPP') ⁻¹' idCompSet 𝒩₁.G = idCompSet Y₁ :=
      SGA3Nbhd.idComp_baseChange' hG (gD hPP') 𝒩₁.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩₁)
    show idCompSet Y₁ = q.base ⁻¹' (U : Set Y.left)
    rw [hU, ← i1, ← i3, ← i2]
    ext x
    show (pullback.fst 𝒩.G.hom (gD hP)) ((pullback.fst 𝒩₁.G.hom (gD hPP')) x) ∈ idCompSet 𝒩.G ↔
      (pullback.fst 𝒩.G.hom (gD hO)) (q x) ∈ idCompSet 𝒩.G
    exact (Iff.of_eq (congrArg (fun f : Y₁.left ⟶ 𝒩.G.left => f x ∈ idCompSet 𝒩.G) hq)).symm
  have hT : p.base ⁻¹' idCompSet 𝒩'.G = idCompSet 𝒩'₁.G := SGA3Nbhd.idComp_baseChange' hG (gD hP') 𝒩'.G (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩')
  exact descend_openImm U c.left c₁.left q p hsq U₁ hU₁ ho₁ _ _ hT hr₁

/-! ## The field and its restricted form -/

/-- **The field `sga7_IX_3_3`, exactly** (`CToPrinted.SGA7_IX_3_3`), from its strictly henselian form

`GapSHPair.NeronBaseChangeStrictHenselization` (BLR 1.2/2), SGA 3 VI_B 3.10 and Stacks 04KV. -/
theorem sga7_IX_3_3_of_SH' (h7 : SGA7_IX_3_3_SH) (hN : GapSHPair.NeronBaseChangeStrictHenselization)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7_IX_3_3 := by
  intro K _ O _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, hSHP', hPP'⟩ :=
    GapSHPair.strictHenselizationPair_of_neron hN K O K' O' hO
  haveI : IsDiscreteValuationRing P := hSHP.1.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1.1
  exact body_of_SH' hO hP hP' hSHP hSHP' hPP' hG (h7 E P hSHP.1 E' P' hSHP'.1 hPP')


end SGA3Nbhd.NF


namespace SGA3Nbhd.Persists

open ZInQ.HeightSplit GapPersists

open ReductSplit ReductGlue CToPrinted in
/-- **SGA 7 IX 3.3, first assertion (`ReductSplit.SemistablePersistsDVR`), from the second assertion.** -/
theorem semistablePersistsDVR_of_printed' (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductSplit.SemistablePersistsDVR := by
  intro K _ O _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨𝒩, h𝒩, hs⟩ := hA
  have hsN : (bcDVR hO 𝒩).IsSemistable := (isSemistable_bcDVR_iff hO (isAlgebraic_resMap hO) 𝒩).mp hs
  -- the identity component `W ⊆ 𝒩`
  have gc := SGA3Nbhd.idCompSubgroup_proof hG
  let W : 𝒩.G.left.Opens := ⟨idCompSet 𝒩.G, SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩⟩
  have hW : OpenSub.IsSubgroupOpen 𝒩.G W :=
    { one := fun s => idCompSet_one 𝒩.G s
      mul := (gc _ 𝒩.G).1
      inv := (gc _ 𝒩.G).2 }
  letI : GrpObj (OpenSub.G0 W) := OpenSub.grpG0 hW
  have hmon : IsMonHom (OpenSub.incl W) := OpenSub.isMonHom_incl hW
  have hoi : IsOpenImmersion (OpenSub.incl W).left := show IsOpenImmersion W.ι from inferInstance
  have hri : Set.range (OpenSub.incl W).left = idCompSet 𝒩.G := Scheme.Opens.range_ι W
  obtain ⟨j, hj, hjm⟩ := SGA3Nbhd.identityComponentBaseChangeDVRRange_proof h7 hG K O K' O' hO A ⟨𝒩, h𝒩, hs⟩
    𝒩 h𝒩 𝒩' h𝒩' (OpenSub.G0 W) (OpenSub.incl W) hoi hmon hri
  -- its base change `W ×_O O' → 𝒩 ×_O O'`, with image `(𝒩 ×_O O')⁰`
  let g := Spec.map (CommRingCat.ofHom (comapHom hO))
  letI : GrpObj ((Over.pullback g).obj (OpenSub.G0 W)) := Functor.grpObjObj
  letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
  let k := (Over.pullback g).map (OpenSub.incl W)
  haveI : IsOpenImmersion (OpenSub.incl W).left := hoi
  have hk : IsOpenImmersion k.left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
  have hkm : IsMonHom k := inferInstance
  have hkmap : k.left = pullback.map (OpenSub.G0 W).hom g 𝒩.G.hom g (OpenSub.incl W).left (𝟙 _) (𝟙 _)
      (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [k, Over.pullback_map_left]
  have hrk : Set.range k.left = idCompSet (bcO hO 𝒩.G) := by
    rw [hkmap, Scheme.Pullback.range_map]
    have hid : Set.range ((𝟙 (Spec (CommRingCat.of O')) : Spec (CommRingCat.of O') ⟶ _) :
        Spec (CommRingCat.of O') → Spec (CommRingCat.of O')) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    rw [hid, Set.preimage_univ, Set.inter_univ, hri]
    exact SGA3Nbhd.idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G
      (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)
  exact hasSemiAbelian_transfer (Spec.map (CommRingCat.ofHom (algebraMap O' (ResBarO O'))))
    (bcO hO 𝒩.G) 𝒩'.G ((Over.pullback g).obj (OpenSub.G0 W)) k j hk hkm hrk hj hjm hsN

/-- **The field `semistablePersistsSHcp` (`ReductB.SemistablePersistsSHcp`) discharged**: it is a specialization
of `SemistablePersistsDVR` (the proof of `ReductB.cp_of_general`, second half). -/
theorem semistablePersistsSHcp_of_printed' (h7 : CToPrinted.SGA7_IX_3_3)
    (hG : AVGlue.GeomConnOfRationalPoint) : ReductB.SemistablePersistsSHcp :=
  fun K _ _ O _ _ _ K' _ _ _ O' _ hO A hA => semistablePersistsDVR_of_printed' h7 hG K O K' O' hO A hA

/-- The field from the bundle fields as they stand at the base (`OpenResearchLeaves21` holds `sga7_IX_3_3_SH` and
`neronBaseChangeStrictHenselization`, from which `SGA7PersistsNF.sga7_IX_3_3_of_SH` gives `SGA7_IX_3_3`). -/
theorem semistablePersistsSHcp_of_SH' (h7 : SGA7PersistsNF.SGA7_IX_3_3_SH)
    (hN : GapSHPair.NeronBaseChangeStrictHenselization) (hG : AVGlue.GeomConnOfRationalPoint) :
    ReductB.SemistablePersistsSHcp :=
  semistablePersistsSHcp_of_printed' (SGA3Nbhd.NF.sga7_IX_3_3_of_SH' h7 hN hG) hG


end SGA3Nbhd.Persists


namespace SGA3Nbhd.Pre

open ReductSplit ReductGlue DictModels.SGA7Pre

/-- The two opens agree: `pullback.fst ⁻¹' N⁰ = (N ×_O O')⁰` (SGA 3 VI_B 3.3, the chain's `idComp_baseChange`). -/
theorem preimage_eq' {K K' : Type} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
    [IsDiscreteValuationRing O] {O' : ValuationSubring K'} (hO : O'.comap (algebraMap K K') = O)
    {A : PkgI3.AbVar K} (𝒩 : GroupModelO A O) (hG : AVGlue.GeomConnOfRationalPoint) :
    letI : GrpObj (bcO hO 𝒩.G) := Functor.grpObjObj
    pullback.fst 𝒩.G.hom (Spec.map (CommRingCat.ofHom (comapHom hO))) ⁻¹' idCompSet 𝒩.G =
      idCompSet (bcO hO 𝒩.G) :=
  SGA3Nbhd.idComp_baseChange' hG (Spec.map (CommRingCat.ofHom (comapHom hO))) 𝒩.G
    (SGA3Nbhd.isOpen_idCompSet_groupModelO 𝒩)

/-- **The field `sga7_IX_3_3_SH`, exactly**, from the print's form `SGA7_IX_3_3_SHpre` and `GeomConnOfRationalPoint`
(no SGA 3 VI_B 3.10: `G⁰` open over a DVR is proved). -/
theorem sga7_IX_3_3_SH_of_pre' (h : SGA7_IX_3_3_SHpre)
    (hG : AVGlue.GeomConnOfRationalPoint) : SGA7PersistsNF.SGA7_IX_3_3_SH := by
  intro K _ O _ hS K' _ _ _ O' _ hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U hU
  exact h K O hS K' O' hS' hO A hA 𝒩 h𝒩 𝒩' h𝒩' c hc hci U (hU.trans (preimage_eq' hO 𝒩 hG).symm)


end SGA3Nbhd.Pre

end

