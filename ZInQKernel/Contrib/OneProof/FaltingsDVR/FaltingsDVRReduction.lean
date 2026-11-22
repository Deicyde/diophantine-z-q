import ZInQKernel.Contrib.OneProof.FaltingsDict2
import ZInQKernel.Contrib.OneProof.SGA7IX33Cor
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing

/-! Néron existence and the open-immersion clause of SGA 7 I, IX,
Proposition 3.2 imply Faltings' extension lemma over a DVR. -/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit CToPrinted SGA3Nbhd ZInQ.SemiAbDescend

namespace ZInQ.FaltingsRestate

private theorem pullback_comparison_fst
    {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (i : X ⟶ Y) :
    ((Over.pullback s).map i).left ≫ pullback.fst Y.hom s =
      pullback.fst X.hom s ≫ i.left := by
  exact pullback.lift_fst _ _ _

private theorem range_pullback_comparison
    {S T : Scheme.{0}} (s : T ⟶ S) {X Y : Over S} (i : X ⟶ Y) :
    Set.range ((Over.pullback s).map i).left =
      pullback.fst Y.hom s ⁻¹' Set.range i.left := by
  have hm : ((Over.pullback s).map i).left =
      pullback.map X.hom s Y.hom s i.left (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext <;> simp [Over.pullback_map_left]
  rw [hm, Scheme.Pullback.range_map]
  have h : Set.range ((𝟙 T : T ⟶ T) : T → T) = Set.univ :=
    Set.range_eq_univ.mpr fun x => ⟨x, rfl⟩
  rw [h, Set.preimage_univ, Set.inter_univ]

private theorem idComp_eq_univ_of_semiabelian
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G : GroupModelO A O) (hG : IsSemiabelianModelO G) :
    idCompSet G.G = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases specDVR_points O (G.G.hom x) with hg | hs
  · have hne : G.G.hom x ≠ IsLocalRing.closedPoint O := by
      rw [(jO_genericOpen O).2.2, Set.mem_singleton_iff] at hg
      intro h
      have h' := congrArg PrimeSpectrum.asIdeal (hg.symm.trans h)
      rw [genericPoint_eq_bot_of_affine] at h'
      exact IsDiscreteValuationRing.not_a_field O h'.symm
    exact mem_idCompSet_groupModelO_generic G x hne
  · let j := closedFibreMap O
    let F := Over.pullback j
    letI : GrpObj (F.obj G.G) := Functor.grpObjObj
    have hx : x ∈ Set.range (pullback.fst G.G.hom j) := by
      rw [Scheme.Pullback.range_fst]
      exact hs
    obtain ⟨y, rfl⟩ := hx
    change y ∈ pullback.fst G.G.hom j ⁻¹' idCompSet G.G
    rw [idComp_baseChange' geomConnOfRationalPoint_proof j G.G
      (isOpen_idCompSet_groupModelO G), idCompSet_eq_cc _ default]
    letI : ConnectedSpace (F.obj G.G).left := hG.1
    rw [PreconnectedSpace.connectedComponent_eq_univ]
    exact Set.mem_univ _

/-- A semiabelian model's open immersion into a group model with the same
generic fibre has image the fibrewise identity component. -/
theorem range_eq_idComp_of_comparison
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O)
    (hG : IsSemiabelianModelO G) (i : G.G ⟶ N.G)
    [IsOpenImmersion i.left] [IsMonHom i]
    [IsIso ((Over.pullback (jO O)).map i)] :
    Set.range i.left = idCompSet N.G := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [← Set.image_univ, ← idComp_eq_univ_of_semiabelian G hG]
    exact SGA33Steps.image_idCompSet_subset G.G N.G i (IsMonHom.one_hom i)
  · intro x hx
    rcases specDVR_points O (N.G.hom x) with hg | hs
    · have hxp : x ∈ Set.range (pullback.fst N.G.hom (jO O)) := by
        rw [Scheme.Pullback.range_fst]
        exact hg
      obtain ⟨y, rfl⟩ := hxp
      change y ∈ pullback.fst N.G.hom (jO O) ⁻¹' Set.range i.left
      rw [← range_pullback_comparison]
      exact ⟨(inv ((Over.pullback (jO O)).map i)).left y, by
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, IsIso.inv_hom_id]
        rfl⟩
    · let j := closedFibreMap O
      let F := Over.pullback j
      letI : GrpObj (F.obj G.G) := Functor.grpObjObj
      letI : GrpObj (F.obj N.G) := Functor.grpObjObj
      haveI : IsOpenImmersion (F.map i).left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
      haveI : ConnectedSpace (F.obj G.G).left := hG.1
      haveI : LocallyOfFiniteType (F.obj N.G).hom :=
        show LocallyOfFiniteType (pullback.snd N.G.hom j) by infer_instance
      have hxp : x ∈ Set.range (pullback.fst N.G.hom j) := by
        rw [Scheme.Pullback.range_fst]
        exact hs
      obtain ⟨y, rfl⟩ := hxp
      change y ∈ pullback.fst N.G.hom j ⁻¹' idCompSet N.G at hx
      rw [idComp_baseChange' geomConnOfRationalPoint_proof j N.G
        (isOpen_idCompSet_groupModelO N), idCompSet_eq_cc _ default] at hx
      change y ∈ pullback.fst N.G.hom j ⁻¹' Set.range i.left
      rw [← range_pullback_comparison,
        ZInQ.SemistabAssembly.range_eq_connectedComponent (F.map i)]
      exact hx

/-- The open-immersion clause of SGA 7 I, IX, Prop. 3.2, restricted to a
semiabelian model with connected closed fibre. -/
def SemiabelianNeronComparison : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (G N : GroupModelO A O), IsSemiabelianModelO G →
    N.IsNeronModel → ∀ i : G.G ⟶ N.G,
    (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom → IsOpenImmersion i.left

set_option backward.isDefEq.respectTransparency false in
/-- Néron existence and the open-immersion clause of SGA 7 I, IX,
Prop. 3.2 imply the exact print-form statement of Faltings' Lemma 1
over a DVR. -/
theorem faltingsLemma1DVRPrint_of_comparison
    (hN : NeronSchemeModelExistsDVR) (hC : SemiabelianNeronComparison) :
    FaltingsLemma1DVRPrint := by
  intro K _ O _ A B G H hG hH
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj G.G) := Functor.grpObjObj
  letI : GrpObj (F.obj H.G) := Functor.grpObjObj
  dsimp only
  intro f hf
  obtain ⟨N, h𝒩⟩ := exists_neron_groupModel hN O B
  letI : GrpObj (F.obj N.G) := Functor.grpObjObj
  haveI : IsMonHom H.gen.hom := H.gen_hom
  haveI : IsMonHom N.gen.hom := N.gen_hom
  obtain ⟨i, hi⟩ := (h𝒩 H.G).2 H.gen.hom
  change F.map i ≫ N.gen.hom = H.gen.hom at hi
  haveI : IsOpenImmersion i.left := hC K O B H N hH h𝒩 i hi
  haveI : IsMonHom (F.map i ≫ N.gen.hom) := hi ▸ H.gen_hom
  haveI : IsMonHom (F.map i) := isMonHom_of_comp_mono _ N.gen.hom
  haveI : IsMonHom i := isMonHom_of_generic H N i (F.map i) inferInstance rfl
  haveI : IsIso (F.map i ≫ N.gen.hom) := hi ▸ inferInstance
  haveI : IsIso (F.map i) := IsIso.of_isIso_comp_right _ N.gen.hom
  have hr := range_eq_idComp_of_comparison H N hH i
  obtain ⟨u, hu⟩ := (h𝒩 G.G).2 (f ≫ H.gen.hom)
  change F.map u ≫ N.gen.hom = f ≫ H.gen.hom at hu
  have hu' : F.map u = f ≫ F.map i := by
    apply (cancel_mono N.gen.hom).mp
    rw [hu, Category.assoc, hi]
  haveI : IsMonHom (F.map u) := hu' ▸ inferInstance
  haveI : IsMonHom u := isMonHom_of_generic G N u (F.map u) inferInstance rfl
  have huRange : Set.range u.left ⊆ Set.range i.left := by
    rw [hr, ← Set.image_univ, ← idComp_eq_univ_of_semiabelian G hG]
    exact SGA33Steps.image_idCompSet_subset G.G N.G u (IsMonHom.one_hom u)
  let v₀ := IsOpenImmersion.lift i.left u.left huRange
  have hv₀ : v₀ ≫ i.left = u.left := IsOpenImmersion.lift_fac _ _ _
  let v : G.G ⟶ H.G := Over.homMk v₀ (by rw [← Over.w i, ← Category.assoc, hv₀, Over.w u])
  have hv : v ≫ i = u := Over.OverMorphism.ext hv₀
  refine ⟨v, ?_, ?_⟩
  · change F.map v = f
    have e : F.map v ≫ F.map i = f ≫ F.map i := by
      rw [← F.map_comp v i, hv, hu']
    have e' := congrArg (fun g => g ≫ inv (F.map i)) e
    simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using e'
  · intro w hw
    have hwi : w ≫ i = v ≫ i := by
      apply (h𝒩 G.G).1
      change F.map (w ≫ i) ≫ N.gen.hom = F.map (v ≫ i) ≫ N.gen.hom
      change F.map w = f at hw
      rw [Functor.map_comp, hw, Category.assoc, hi, hv, hu]
    apply Over.OverMorphism.ext
    apply (cancel_mono i.left).mp
    exact congrArg CommaMorphism.left hwi


open ZInQ.Contrib.GroupLawNeron in
/-- The Dedekind existence theorem gives the scheme-level Néron model in the
valuation-subring conventions of the reduction and Tate-module files. -/
theorem neronSchemeModelExistsDVR_of_dedekind (hN : NeronSchemeExtensionDedekind) :
    NeronSchemeModelExistsDVR := by
  intro K _ O _ A
  obtain ⟨N, hSmooth, hSep, hQC, e, hSurj⟩ :=
    hN O K A (IsDiscreteValuationRing.not_isField O)
  refine ⟨N, hSmooth, hSep, hQC, e, fun Y _ => ⟨?_, hSurj Y⟩⟩
  haveI : IsSchemeTheoreticallyDominant (jO O) :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (FaithfulSMul.algebraMap_injective O K)
  intro f g h
  exact ZInQ.Contrib.NeronC.pullback_map_injective (jO O) Y N ((cancel_mono e.hom).mp h)

set_option backward.isDefEq.respectTransparency false in
/-- A locally quasi-finite comparison of smooth DVR models that is an
isomorphism on the generic fibre is an open immersion. -/
theorem isOpenImmersion_of_comparison
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G H : GroupModelO A O) (i : G.G ⟶ H.G)
    [LocallyQuasiFinite i.left] [IsIso ((Over.pullback (jO O)).map i)] :
    IsOpenImmersion i.left := by
  let j := jO O
  let F := Over.pullback j
  haveI : IsOpenImmersion j := (jO_genericOpen O).1
  haveI : IsSchemeTheoreticallyDominant j :=
    ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map _
      (FaithfulSMul.algebraMap_injective O K)
  haveI : QuasiCompact j := show QuasiCompact (Spec.map _) by infer_instance
  let a := pullback.fst G.G.hom j
  let b := pullback.fst H.G.hom j
  haveI : IsOpenImmersion a := show IsOpenImmersion (pullback.fst G.G.hom j) by infer_instance
  haveI : IsOpenImmersion b := show IsOpenImmersion (pullback.fst H.G.hom j) by infer_instance
  haveI : IsSchemeTheoreticallyDominant a :=
    show IsSchemeTheoreticallyDominant (pullback.fst G.G.hom j) by infer_instance
  haveI : IsSchemeTheoreticallyDominant b :=
    show IsSchemeTheoreticallyDominant (pullback.fst H.G.hom j) by infer_instance
  let V := b.opensRange
  let e := IsOpenImmersion.isoOfRangeEq V.ι b (Scheme.Opens.range_ι V)
  have he : e.hom ≫ b = V.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let d : (F.obj G.G).left ≅ (F.obj H.G).left :=
    (Over.forget _).mapIso (asIso (F.map i))
  let s : (V : Scheme) ⟶ G.G.left := e.hom ≫ d.inv ≫ a
  have hs : s ≫ i.left = V.ι := by
    have hi : d.hom ≫ b = a ≫ i.left := by
      exact pullback_comparison_fst j i
    rw [show s = e.hom ≫ d.inv ≫ a from rfl, Category.assoc, Category.assoc,
      ← hi, Iso.inv_hom_id_assoc, he]
  have hsd : DenseRange s.base := by
    have hd : Function.Surjective (e.hom ≫ d.inv) :=
      ((e.hom ≫ d.inv).surjective)
    change DenseRange (fun x => a ((e.hom ≫ d.inv) x))
    exact a.denseRange.comp hd.denseRange a.continuous
  have hV : Dense (V : Set H.G.left) := b.denseRange
  haveI : IsLocallyNoetherian H.G.left := LocallyOfFiniteType.isLocallyNoetherian H.G.hom
  haveI : IsLocallyNoetherian G.G.left := LocallyOfFiniteType.isLocallyNoetherian G.G.hom
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  haveI : IsNoetherian G.G.left := {}
  haveI : IsReduced G.G.left := by
    have hY : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
    haveI : IsIso G.gen.inv.left :=
      inferInstanceAs (IsIso ((Over.forget _).mapIso G.gen).inv)
    haveI : IsReduced (F.obj G.G).left :=
      IsSchemeTheoreticallyDominant.isReduced G.gen.inv.left
    exact IsSchemeTheoreticallyDominant.isReduced a
  haveI : IsSeparated (i.left ≫ H.G.hom) := by rw [Over.w]; infer_instance
  haveI : IsSeparated i.left := IsSeparated.of_comp i.left H.G.hom
  haveI : LocallyOfFiniteType (i.left ≫ H.G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left H.G.hom
  have hY : ∀ z : H.G.left,
      IsDomain (H.G.left.presheaf.stalk z) ∧ IsIntegrallyClosed (H.G.left.presheaf.stalk z) :=
    fun z =>
      ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
        O H.G.hom z
  exact ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.isOpenImmersion_of_locallyQuasiFinite_of_isIntegrallyClosed_stalk_of_denseRange
    i.left hY V hV s hs hsd

private theorem isDiscrete_preimage_of_baseChange
    {S T : Scheme.{0}} (s : T ⟶ S) [IsPreimmersion s] {X Y : Over S} (i : X ⟶ Y)
    [LocallyQuasiFinite ((Over.pullback s).map i).left]
    (y : Y.left) (hy : Y.hom y ∈ Set.range s) :
    _root_.IsDiscrete (i.left ⁻¹' {y}) := by
  let a := pullback.fst X.hom s
  let b := pullback.fst Y.hom s
  let c := ((Over.pullback s).map i).left
  haveI : IsPreimmersion a := show IsPreimmersion (pullback.fst X.hom s) by infer_instance
  haveI : IsPreimmersion b := show IsPreimmersion (pullback.fst Y.hom s) by infer_instance
  have hby : y ∈ Set.range b := by
    change y ∈ Set.range (pullback.fst Y.hom s)
    rwa [Scheme.Pullback.range_fst]
  obtain ⟨y', rfl⟩ := hby
  have hcomm (x : (Over.pullback s |>.obj X).left) : b (c x) = i.left (a x) :=
    congrArg (fun g : (Over.pullback s |>.obj X).left ⟶ Y.left => g x)
      (pullback_comparison_fst s i)
  have he : a '' (c ⁻¹' {y'}) = i.left ⁻¹' {b y'} := by
    ext x
    constructor
    · rintro ⟨x', hx', rfl⟩
      change c x' = y' at hx'
      change i.left (a x') = b y'
      rw [← hcomm, hx']
    · intro hx
      change i.left x = b y' at hx
      have hw : X.hom x ∈ Set.range s := by
        change Y.hom (b y') ∈ Set.range s at hy
        have hxw : X.hom x = Y.hom (i.left x) := by
          rw [← Scheme.Hom.comp_apply, Over.w]
        rwa [hxw, hx]
      have hxr : x ∈ Set.range a := by
        change x ∈ Set.range (pullback.fst X.hom s)
        rwa [Scheme.Pullback.range_fst]
      obtain ⟨x', rfl⟩ := hxr
      exact ⟨x', b.isEmbedding.injective ((hcomm x').trans hx), rfl⟩
  rw [← he]
  exact (c.isDiscrete_preimage_singleton y').image a.isEmbedding.toIsInducing

/-- For a comparison that is an isomorphism on the generic fibre, it suffices
to show local quasi-finiteness on the closed fibre. -/
theorem locallyQuasiFinite_of_comparison_closedFibre
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G H : GroupModelO A O) (i : G.G ⟶ H.G)
    [LocallyQuasiFinite ((Over.pullback (closedFibreMap O)).map i).left]
    [IsIso ((Over.pullback (jO O)).map i)] :
    LocallyQuasiFinite i.left := by
  haveI : LocallyOfFiniteType (i.left ≫ H.G.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType i.left := locallyOfFiniteType_of_comp i.left H.G.hom
  apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
  intro y
  rcases specDVR_points O (H.G.hom y) with hy | hy
  · haveI : IsOpenImmersion (jO O) := (jO_genericOpen O).1
    haveI : IsIso ((Over.pullback (jO O)).map i).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((Over.pullback (jO O)).map i)))
    exact isDiscrete_preimage_of_baseChange (jO O) i y hy
  · haveI : IsClosedImmersion (closedFibreMap O) :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    exact isDiscrete_preimage_of_baseChange (closedFibreMap O) i y hy

/-- Local quasi-finiteness of the comparison between a semiabelian model
and its Néron model. -/
def SemiabelianNeronComparisonQuasiFinite : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (G N : GroupModelO A O), IsSemiabelianModelO G →
    N.IsNeronModel → ∀ i : G.G ⟶ N.G,
    (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom → LocallyQuasiFinite i.left

/-- The exact Faltings input follows from Dedekind Néron existence and the
quasi-finiteness clause of SGA 7 I, IX, Prop. 3.1(d), for the comparison map. -/
theorem faltingsLemma1DVRPrint_of_quasiFinite_comparison
    (hN : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
    (hQ : SemiabelianNeronComparisonQuasiFinite) : FaltingsLemma1DVRPrint :=
  faltingsLemma1DVRPrint_of_comparison (neronSchemeModelExistsDVR_of_dedekind hN) <| by
    intro K _ O _ A G N hG hN' i hi
    haveI : LocallyQuasiFinite i.left := hQ K O A G N hG hN' i hi
    haveI : IsIso ((Over.pullback (jO O)).map i ≫ N.gen.hom) := hi ▸ inferInstance
    haveI : IsIso ((Over.pullback (jO O)).map i) := IsIso.of_isIso_comp_right _ N.gen.hom
    exact isOpenImmersion_of_comparison G N i

private theorem locallyQuasiFinite_of_surjective_baseChange
    {S T : Scheme.{0}} (s : T ⟶ S) [Surjective s]
    {X Y : Over S} (i : X ⟶ Y) [LocallyOfFiniteType i.left]
    [LocallyQuasiFinite ((Over.pullback s).map i).left]
    [QuasiCompact ((Over.pullback s).map i).left] :
    LocallyQuasiFinite i.left := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro y
  let a := pullback.fst X.hom s
  let b := pullback.fst Y.hom s
  let c := ((Over.pullback s).map i).left
  haveI : Surjective b := show Surjective (pullback.fst Y.hom s) by infer_instance
  obtain ⟨y', rfl⟩ := b.surjective y
  have hi : a '' (c ⁻¹' {y'}) = i.left ⁻¹' {b y'} := by
    have hp := Scheme.image_preimage_eq_of_isPullback
      (NeronSH.isPullback_pullback_map_left s i) ({y'} : Set ((Over.pullback s).obj Y).left)
    change a '' (c ⁻¹' {y'}) = i.left ⁻¹' b '' {y'} at hp
    simpa only [Set.image_singleton] using hp
  rw [← hi]
  exact (c.finite_preimage_singleton y').image a

/-- The closed-fibre comparison may be tested after any field extension. -/
theorem locallyQuasiFinite_closedFibre_of_fieldExtension
    {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {A : PkgI3.AbVar K} (G N : GroupModelO A O) (i : G.G ⟶ N.G)
    (k' : Type) [Field k'] [Algebra (IsLocalRing.ResidueField O) k']
    (h : LocallyQuasiFinite ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField O) k')))).map
      ((Over.pullback (closedFibreMap O)).map i)).left) :
    LocallyQuasiFinite ((Over.pullback (closedFibreMap O)).map i).left := by
  let k := IsLocalRing.ResidueField O
  let s := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let j := closedFibreMap O
  let F := Over.pullback j
  let f := F.map i
  let X := (Over.pullback s).obj (F.obj G.G)
  haveI : Surjective s := ⟨fun _ => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : LocallyOfFiniteType (F.obj G.G).hom :=
    show LocallyOfFiniteType (pullback.snd G.G.hom j) by infer_instance
  haveI : LocallyOfFiniteType (f.left ≫ (F.obj N.G).hom) := by
    rw [Over.w]
    infer_instance
  haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left (F.obj N.G).hom
  haveI : LocallyOfFiniteType X.hom :=
    show LocallyOfFiniteType (pullback.snd (F.obj G.G).hom s) by infer_instance
  haveI : QuasiCompact (F.obj G.G).hom :=
    show QuasiCompact (pullback.snd G.G.hom j) by infer_instance
  haveI : QuasiCompact X.hom :=
    show QuasiCompact (pullback.snd (F.obj G.G).hom s) by infer_instance
  haveI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  haveI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  haveI : IsNoetherian X.left := {}
  haveI : LocallyQuasiFinite ((Over.pullback s).map f).left := h
  exact locallyQuasiFinite_of_surjective_baseChange s f

/-- The special-fibre assertion of local quasi-finiteness for the comparison. -/
def SemiabelianNeronComparisonClosedQuasiFinite : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (G N : GroupModelO A O), IsSemiabelianModelO G →
    N.IsNeronModel → ∀ i : G.G ⟶ N.G,
    (Over.pullback (jO O)).map i ≫ N.gen.hom = G.gen.hom →
    LocallyQuasiFinite ((Over.pullback (closedFibreMap O)).map i).left

/-- The closed fibre suffices for the canonical comparison in Faltings'
extension lemma. -/
theorem faltingsLemma1DVRPrint_of_closed_quasiFinite_comparison
    (hN : ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind)
    (hQ : SemiabelianNeronComparisonClosedQuasiFinite) : FaltingsLemma1DVRPrint :=
  faltingsLemma1DVRPrint_of_quasiFinite_comparison hN <| by
    intro K _ O _ A G N hG hN' i hi
    haveI : LocallyQuasiFinite ((Over.pullback (closedFibreMap O)).map i).left :=
      hQ K O A G N hG hN' i hi
    haveI : IsIso ((Over.pullback (jO O)).map i ≫ N.gen.hom) := hi ▸ inferInstance
    haveI : IsIso ((Over.pullback (jO O)).map i) := IsIso.of_isIso_comp_right _ N.gen.hom
    exact locallyQuasiFinite_of_comparison_closedFibre G N i

end ZInQ.FaltingsRestate
