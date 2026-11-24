import ZInQKernel.Contrib.OneProof.SSFaltings
import ZInQKernel.Contrib.OneProof.PrintedStableHeight
import ZInQKernel.Contrib.OneProof.GaRigiditySGA7
import ZInQKernel.Contrib.OneProof.FaltingsRestateDVR
import ZInQKernel.Contrib.OneProof.BLRLocalizes
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization
import ZInQKernel.Contrib.OneProof.GeomConnOfRationalPoint
import ZInQKernel.Contrib.OneProof.SZRaynaud
import ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron

/-! Faltings' height invariance for a semiabelian scheme and the separate comparison
with Néron models. -/

set_option linter.style.haveILetI false

namespace ZInQ.FaltingsRestate

open CategoryTheory AlgebraicGeometry NumberField
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.H5Neron ZInQ.SSFaltings
open ZInQ.HeightFix DictModels.RaynaudOr

/-- The special fibres of Faltings' semiabelian model (Invent. Math. 73 (1983), p. 350)
are connected extensions of abelian varieties by tori over the residue fields.
Smoothness and an abelian generic fibre are already part of `GroupModel`.
For a connected group over a field the open connected subgroup in
`HasSemiAbelianIdCompTorus) is the whole group. -/
def IsSemiabelianModel {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
    {A : PkgI3.AbVar K} (G : GroupModel A L) : Prop :=
  ∀ (p : Ideal (𝓞 L)) [p.IsMaximal],
    ConnectedSpace (resFibre G p).left ∧ HasSemiAbelianIdCompTorus (resFibre G p)

/-- Faltings 1983, §3 p. 354 (asserted there without proof), with p. 351 Bem. b):
the normalized height of a semiabelian model with proper generic fibre agrees
with the height of its base change. Both pages read by the reading desk. -/
def FaltingsHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type)
    [Field L] [NumberField L] [Algebra K L] (G : GroupModel A L), IsSemiabelianModel G →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
      [IsScalarTower K L L'] (G' : GroupModel A L'), IsBaseChangeOf G' G → G'.height = G.height

/-- The existing height base change theorem applies even without the semiabelian hypothesis. -/
theorem faltingsHeightBaseChange : FaltingsHeightBaseChange := by
  intro K _ _ A L _ _ _ G _ L' _ _ _ _ _ G' hG'
  exact Contrib.HeightBC.modelHeightBaseChange K A L L' G G' hG'

/-- **Consequence (GLUE).** The Néron comparison needed for height: two semistable
Néron models over an extension admit a common open subgroup model after base change.
This is SS2 restricted to cases where both models are semistable. It follows from
SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (page read; uncited in the manuscript), or
from Faltings 1983, Lemma 1, p. 350 (page read), with the semiabelian dictionary.
The common open subgroup need only contain an open neighbourhood of the identity;
this statement does not require a global identity-component construction. -/
def SemistableNeronIdentification : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L : Type)
    [Field L] [NumberField L] [Algebra K L] (N : GroupModel A L), N.IsNeronModel → IsSemistable N →
    ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
      [IsScalarTower K L L'] (N' : GroupModel A L'), N'.IsNeronModel → IsSemistable N' →
      ∃ U V : GroupModel A L', IsBaseChangeOf V N ∧ IsOpenSubgroupModel U N' ∧ IsOpenSubgroupModel U V

/-- SS2 supplies the comparison without needing target semistability. -/
theorem semistableNeronIdentification_of_ss2 (h : SemistableNeronBaseChange) :
    SemistableNeronIdentification := by
  intro K _ _ A L _ _ _ N hN hs L' _ _ _ _ _ N' hN' _
  exact h K A L N hN hs L' N' hN'

/-- Corollary 3.3 supplies SS2 by the existing localization argument. -/
theorem semistableNeronIdentification_of_cor33 (h : GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34) :
    SemistableNeronIdentification :=
  semistableNeronIdentification_of_ss2
    (SGA3Nbhd.semistableNeronBaseChange_noSGA3 GapBLR.blr_1_2_4
      (SGA3Nbhd.NF.sga7_IX_3_3_of_SH'
        (SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre'
          (SGA33Steps.shpre_of_cor33 (GaRigidity.SGA7.sga7_IX_Cor3_3_of_def34 h))
          geomConnOfRationalPoint_proof)
        NeronSH.neronBaseChangeStrictHenselization_proof geomConnOfRationalPoint_proof)
      geomConnOfRationalPoint_proof)

private theorem height_eq_of_two_semistable (h : SemistableNeronIdentification)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (L L' : Type)
    [Field L] [NumberField L] [Algebra K L] [Field L'] [NumberField L'] [Algebra K L']
    [Algebra L L'] [IsScalarTower K L L'] (N : GroupModel A L) (N' : GroupModel A L')
    (hN : N.IsNeronModel) (hs : IsSemistable N) (hN' : N'.IsNeronModel)
    (hs' : IsSemistable N') : N'.height = N.height := by
  obtain ⟨U, V, hV, hUN', hUV⟩ := h K A L N hN hs L' N' hN' hs'
  calc
    N'.height = U.height := (Contrib.HeightBC.openSubgroupHeight K A L' U N' hUN').symm
    _ = V.height := Contrib.HeightBC.openSubgroupHeight K A L' U V hUV
    _ = N.height := Contrib.HeightBC.modelHeightBaseChange K A L L' N V hV

/-- Compare the heights over a common larger semistable field, using minimality for
the intermediate Néron model. No persistence of semistability is required. -/
theorem faltingsSemistableHeightBC_of_identification (h : SemistableNeronIdentification)
    (hSS : SemistableReductionThmIF) (hN1 : NeronModelExists) : FaltingsSemistableHeightBC := by
  intro K _ _ A L _ _ _ N hN hs L' _ _ _ _ _ N' hN'
  obtain ⟨K₀, hfin, hK₀⟩ := hSS K A
  haveI : FiniteDimensional K K₀ := hfin
  haveI : Module.Finite K L' := Module.Finite.of_restrictScalars_finite ℚ K L'
  let e : L' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let E : IntermediateField K (AlgebraicClosure K) := e.fieldRange ⊔ K₀
  haveI : FiniteDimensional K e.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField e).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : NumberField E := NumberField.of_module_finite K E
  let f : L' →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField e).toAlgHom
  letI : Algebra L' E := f.toRingHom.toAlgebra
  letI : IsScalarTower K L' E := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  letI : Algebra L E := ((algebraMap L' E).comp (algebraMap L L')).toAlgebra
  letI : IsScalarTower L L' E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K L E := IsScalarTower.to₁₂₄ K L L' E
  obtain ⟨N'', hN''⟩ := hN1 K A E
  have hs'' : IsSemistable N'' := hK₀ E le_sup_right N'' hN''
  have hei : N''.height = N.height := height_eq_of_two_semistable h K A L E N N'' hN hs hN'' hs''
  obtain ⟨V, hV⟩ := groupModelBaseChangeExists K A L L' N
  obtain ⟨V', hV'⟩ := groupModelBaseChangeExists K A L' E N'
  apply le_antisymm
  · calc
      N'.height ≤ V.height := Contrib.HeightBC.neronModelMinimal K A L' N' V hN'
      _ = N.height := Contrib.HeightBC.modelHeightBaseChange K A L L' N V hV
  · calc
      N.height = N''.height := hei.symm
      _ ≤ V'.height := Contrib.HeightBC.neronModelMinimal K A E N'' V' hN''
      _ = N'.height := Contrib.HeightBC.modelHeightBaseChange K A L' E N' V' hV'

/-- The old field from the separate Néron comparison and the two existing fields
for Raynaud's criterion and existence of Néron models. -/
theorem faltingsSemistableHeightBC_of_leaves (h : SemistableNeronIdentification)
    (hR : SZRaynaud.SilverbergZarhinThm35) (hD : Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    FaltingsSemistableHeightBC :=
  let hE := Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind hD
  faltingsSemistableHeightBC_of_identification h
    (semistableReductionThmIF_of_raynaud (SZRaynaud.raynaudSemistable_of_sz35 hR)
      Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
      Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
      (GapNeron.neronSchemeModelExistsNF hE)
      (ReductGlue.semistableLocalGlobal_leaf GapBLR.neronLocalizesDVR_proved))
    (Contrib.NeronC.neronModelExists_of_extension hE)

open Limits Topology MonoidalCategory CartesianMonoidalCategory MonObj
  ReductSplit ReductGlue CToPrinted SGA3Nbhd ZInQ.Contrib.SpreadOut.NF in
/-- Localize both Néron models and apply Faltings' Lemma 1 at the finitely many
primes where the generic comparison has not already spread to an open immersion.
As in `semistableNeronBaseChange_noSGA3`, only the identity components at
those primes are needed to build the global common open subgroup. -/
theorem semistableNeronIdentification_of_faltingsLemma1 (hF : FaltingsLemma1DVR) :
    SemistableNeronIdentification := by
  have hG := geomConnOfRationalPoint_proof
  have hOI := openImmersionLocalization ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof
  have hL := GapBLR.neronLocalizesDVR_proved
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩' hss'
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  let gLL : Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))
  let 𝒱 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒩
  let jL' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of (𝓞 L')) :=
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L'))
  -- the Néron extension `c₀ : 𝒱 → 𝒩'`, an open immersion over `𝓞_{L'}[1/n!]`
  obtain ⟨c₀, hc₀⟩ := (h𝒩' 𝒱.G).2 𝒱.gen.hom
  simp only at hc₀
  have hc₀L : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map c₀) := by
    have : IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')))).map c₀ ≫
        𝒩'.gen.hom) := by
      rw [hc₀]; exact Iso.isIso_hom 𝒱.gen
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (Iso.isIso_hom 𝒩'.gen) this
  obtain ⟨n, hn⟩ := spread_openImm 𝒱.G 𝒩'.G c₀ hc₀L
  -- the finite set `T` of primes of `𝓞_L` containing `n!`
  let Tset : Set (Spec (CommRingCat.of (𝓞 L))) := {t | sf L n ∈ t.asIdeal}
  have hTne : ∀ t ∈ Tset, t.asIdeal ≠ ⊥ := fun t ht h => sf_ne_zero L n (by
    have : sf L n ∈ t.asIdeal := ht
    rw [h] at this
    exact this)
  have hTc : ∀ t ∈ Tset, IsClosed ({t} : Set (Spec (CommRingCat.of (𝓞 L)))) := fun t ht =>
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mpr
      (Ring.DimensionLEOne.maximalOfPrime (hTne t ht) t.isPrime)
  have hTfin : Tset.Finite := by
    refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing (𝓞 L) (Ideal.span {sf L n})).preimage
      (fun a _ b _ h => PrimeSpectrum.ext h)).subset ?_
    intro t ht
    have htm : t.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime (hTne t ht) t.isPrime
    refine ⟨⟨t.isPrime, (Ideal.span_singleton_le_iff_mem _).mpr ht⟩, fun q hq hqt => ?_⟩
    have hq0 : q ≠ ⊥ := fun h => sf_ne_zero L n (by
      have := hq.2 (Ideal.mem_span_singleton_self (sf L n))
      rw [h] at this
      exact this)
    have hqm : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq0 hq.1
    exact (hqm.eq_of_le htm.ne_top hqt).ge
  -- the open subgroup `W₀`
  let W0s : Set 𝒩.G.left := {x | 𝒩.G.hom x ∈ Tset → x ∈ idCompSet 𝒩.G}
  have hW0c : W0s = (⋃ t ∈ Tset, (𝒩.G.hom ⁻¹' {t} \
      connectedComponentIn (𝒩.G.hom ⁻¹' {t}) ((η[𝒩.G] : 𝟙_ (Over _) ⟶ 𝒩.G).left t)))ᶜ := by
    ext x
    simp only [W0s, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_sdiff,
      Set.mem_preimage, Set.mem_singleton_iff, exists_prop, not_exists, not_and, not_not]
    constructor
    · intro h t ht hxt
      subst hxt
      exact h ht
    · intro h ht
      exact h _ ht rfl
  have hW0o : IsOpen W0s := by
    rw [hW0c, isOpen_compl_iff]
    exact hTfin.isClosed_biUnion fun t ht => isClosed_fibre_diff 𝒩.G t (hTc t ht)
  let W0 : 𝒩.G.left.Opens := ⟨W0s, hW0o⟩
  have gc := idCompSubgroup_proof hG _ 𝒩.G
  have hW0 : OpenSub.IsSubgroupOpen 𝒩.G W0 :=
    { one := fun s _ => idCompSet_one 𝒩.G s
      mul := fun z h1 h2 ht => by
        have e1 : 𝒩.G.hom ((μ[𝒩.G] : 𝒩.G ⊗ 𝒩.G ⟶ 𝒩.G).left z) =
            𝒩.G.hom ((fst 𝒩.G 𝒩.G).left z) := SGA3IdComp.hom_mu 𝒩.G z
        have e2 : 𝒩.G.hom ((snd 𝒩.G 𝒩.G).left z) = 𝒩.G.hom ((fst 𝒩.G 𝒩.G).left z) := by
          show 𝒩.G.hom (pullback.snd 𝒩.G.hom 𝒩.G.hom z) = 𝒩.G.hom (pullback.fst 𝒩.G.hom 𝒩.G.hom z)
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
        have ht' : 𝒩.G.hom ((fst 𝒩.G 𝒩.G).left z) ∈ Tset := e1 ▸ ht
        exact gc.1 z (h1 ht') (h2 (e2 ▸ ht'))
      inv := fun x hx ht => by
        have e1 : 𝒩.G.hom ((GrpObj.inv : 𝒩.G ⟶ 𝒩.G).left x) = 𝒩.G.hom x := by
          rw [← Scheme.Hom.comp_apply, Over.w]
        exact gc.2 x (hx (e1 ▸ ht)) }
  have hgen : ∀ x : 𝒩.G.left, (𝒩.G.hom x).asIdeal = ⊥ → x ∈ (W0 : Set 𝒩.G.left) :=
    fun x hx ht => absurd hx (hTne _ ht)
  obtain ⟨𝒢₀, i, hoi, hmi, hri⟩ := openSubgroupModel_at 𝒩 W0 hW0 hgen
  let 𝒰 : GroupModel A L' := ZInQ.H5Glue.GroupModel.baseChange L L' 𝒢₀
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
  have hsN : N.IsSemistable := semistableNeronModels_of_has
    ((semistableLocalGlobal_leaf hL K A L' 𝒩' h𝒩').mp hss' O' inferInstance) N hN
  let N' := N.transport (bcbcIso A L L') (bcbcIso_isMonHom A L L')
  have hN' : N'.IsNeronModel := N.transport_isNeronModel _ _ hN
  let T := (Over.pullback (gO O')).obj 𝒰.G
  haveI : Smooth T.hom := by change Smooth (pullback.snd 𝒰.G.hom (gO O')); infer_instance
  let eT : (Over.pullback (jO O')).obj T ≅ (A.baseChange L').X :=
    isoX (pbCompIso (jO O') (gO O') _ (jO_gO O') (Grp.mk 𝒰.G)) ≪≫ 𝒰.gen
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
  suffices hj2 : ∃ j₂ : T ⟶ N.G, IsOpenImmersion j₂.left by
    obtain ⟨j₂, hj₂⟩ := hj2
    haveI := hj₂
    have h₂ : IsIso ((Over.pullback (jO O')).map j₂) := by
      haveI : IsOpenImmersion ((Over.pullback (jO O')).map j₂).left :=
        ZInQ.H5Glue.isOpenImmersion_pullback_map _ j₂
      exact isIso_of_openImmersion_of_iso (A.baseChange L') eT N.gen _
    exact isOpenImmersion_of_neron N hN T ((Over.pullback (gO O')).map j) j₂ h₁ h₂
  by_cases hu : IsUnit (toOL O' (sf L' n))
  · -- `n!` is a unit in `O'`: the base change of `𝒰 → 𝒱 → 𝒩'`
    refine ⟨(Over.pullback (gO O')).map ((Over.pullback gLL).map i) ≫ (Over.pullback (gO O')).map c₀, ?_⟩
    haveI : IsOpenImmersion i.left := hoi
    haveI : IsOpenImmersion ((Over.pullback gLL).map i).left := ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
    have h1 : IsOpenImmersion ((Over.pullback (gO O')).map ((Over.pullback gLL).map i)).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ _
    have h2 : IsOpenImmersion ((Over.pullback (gO O')).map c₀).left := hn O' hu
    show IsOpenImmersion (((Over.pullback (gO O')).map ((Over.pullback gLL).map i)).left ≫
      ((Over.pullback (gO O')).map c₀).left)
    exact @IsOpenImmersion.comp _ _ _ _ _ h1 h2
  · -- `n!` is not a unit in `O'`: the center of `O` lies in `T`
    have hcl : sf L n ∈ (gO O (IsLocalRing.closedPoint O)).asIdeal := by
      show toOL O (sf L n) ∈ IsLocalRing.maximalIdeal O
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu'
      apply hu
      have := hu'.map (comapHom hO)
      convert this using 1
      apply Subtype.ext
      simp [comapHom, toOL, sf]
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
      ext z
      by_cases hz : pullback.snd 𝒩.G.hom (gO O) z = IsLocalRing.closedPoint O
      · have hfz : 𝒩.G.hom (pullback.fst 𝒩.G.hom (gO O) z) = gO O (IsLocalRing.closedPoint O) := by
          rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz]
        have hT : 𝒩.G.hom (pullback.fst 𝒩.G.hom (gO O) z) ∈ Tset := by rw [hfz]; exact hcl
        constructor
        · intro hzW
          refine mem_idCompSet_bc hG (gO O) 𝒩.G z ?_ (hzW hT)
          rw [hz]
          exact hTc _ hcl
        · intro hz' _
          exact mem_idCompSet_of_bc (gO O) 𝒩.G z hz'
      · constructor
        · intro _
          exact mem_idCompSet_groupModelO_generic (toO 𝒩 O) z hz
        · intro _ hT
          exfalso
          have hfz : 𝒩.G.hom (pullback.fst 𝒩.G.hom (gO O) z) = gO O (pullback.snd 𝒩.G.hom (gO O) z) := by
            rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
          have h0 : (pullback.snd 𝒩.G.hom (gO O) z).asIdeal = ⊥ := by
            by_contra h
            have hm : (pullback.snd 𝒩.G.hom (gO O) z).asIdeal.IsMaximal :=
              Ring.DimensionLEOne.maximalOfPrime h (pullback.snd 𝒩.G.hom (gO O) z).isPrime
            exact hz (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm))
          apply hTne _ hT
          rw [hfz]
          show Ideal.comap (toOL O) (pullback.snd 𝒩.G.hom (gO O) z).asIdeal = ⊥
          rw [h0]
          exact Ideal.comap_bot_of_injective _ (fun a b h => by
            have := congrArg Subtype.val h
            simpa using this)
    haveI := center_isMaximal O'
    haveI : PerfectField (center O').ResidueField := perfectField_residueField (center O')
    haveI : PerfectField (IsLocalRing.ResidueField O') := PerfectField.of_ringEquiv (resIso O')
    have hIO : IsOpenImmersion ((Over.pullback (gO O)).map i).left :=
      ZInQ.H5Glue.isOpenImmersion_pullback_map _ i
    obtain ⟨j', hj'o, _⟩ :=
      @identityComponentBaseChangeDVRRange_of_faltingsLemma1 hF L L' _ _ _ _ O O' _ _ _ hO
        (A.baseChange L) (toO 𝒩 O) (hL K A L 𝒩 h𝒩 O) hssO N' hN' hsN U
        _ ((Over.pullback (gO O)).map i) hIO hmiO hrange
    -- compare `T = 𝒰 ×_{𝓞_{L'}} O'` with `U ×_O O'`
    have hsq : gO O' ≫ gLL = Spec.map (CommRingCat.ofHom (comapHom hO)) ≫ gO O := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    let c := isoX (pbCompIso (gO O') gLL _ hsq (Grp.mk 𝒢₀.G)) ≪≫
      (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (comapHom hO))) (gO O) _ rfl (Grp.mk 𝒢₀.G))).symm
    -- compare `T = 𝒰 ×_{𝓞_{L'}} O'` with `U ×_O O'`
    have hsq : gO O' ≫ gLL = Spec.map (CommRingCat.ofHom (comapHom hO)) ≫ gO O := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    let c := isoX (pbCompIso (gO O') gLL _ hsq (Grp.mk 𝒢₀.G)) ≪≫
      (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (comapHom hO))) (gO O) _ rfl (Grp.mk 𝒢₀.G))).symm
    refine ⟨c.hom ≫ j', ?_⟩
    have h1 : IsOpenImmersion c.hom.left := by
      haveI : IsIso c.hom.left := Functor.map_isIso (Over.forget _) c.hom
      infer_instance
    have h2 : IsOpenImmersion j'.left := hj'o
    show IsOpenImmersion (c.hom.left ≫ j'.left)
    exact @IsOpenImmersion.comp _ _ _ _ _ h1 h2

/-- The old open field follows from the printed DVR instance of Lemma 1
and the two existing Raynaud and Néron existence fields. -/
theorem faltingsSemistableHeightBC_of_faltingsLemma1 (hF : FaltingsLemma1DVR)
    (hR : SZRaynaud.SilverbergZarhinThm35) (hD : Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    FaltingsSemistableHeightBC :=
  faltingsSemistableHeightBC_of_leaves (semistableNeronIdentification_of_faltingsLemma1 hF) hR hD

end ZInQ.FaltingsRestate
