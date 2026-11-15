import ZInQKernel.Contrib.OneProof.SGA7PersistsNF
/-! triage2 probe A: `semistablePersistsSHcp` removal. The target statement (general K, so no NF needed)
and the declarations the plan needs. -/
open CategoryTheory AlgebraicGeometry

-- target: SGA 7 IX 3.3 first assertion over any DVR, from fields already on the chain
example : Prop :=
  CToPrinted.SGA3_VIB_3_10 → CToPrinted.SGA7_IX_3_3 → AVGlue.GeomConnOfRationalPoint →
    ReductSplit.SemistablePersistsDVR

#check @CToPrinted.identityComponentBaseChangeDVRRange_of
#check @CToPrinted.IdentityComponentBaseChangeDVRRange
#check @CToPrinted.idCompBaseChangeDVR_of
#check @CToPrinted.idCompSet
#check @SGA7PersistsNF.sga7_IX_3_3_of_SH
#check @ReductSplit.GroupModelO.IsSemistable
#check @ReductSplit.geomSpecialFibre
#check @ZInQ.HeightSplit.HasSemiAbelianIdentityComponent
#check @ReductSplit.SemistablePersistsDVR
#check @ReductB.persistsNF_of_general
#check @ReductB.semistableReductionThm_of_leaves_nf
#check @ReductB.semistablePersists_final_nf
#check @ReductB.ss1_ss3_of_cp
#check @HDec.HSyn.ss1_ss3_of14
#check @ReductSplit.hasSemistableReduction_of
#check @AVGlue.GeomConnOfRationalPoint
#check @PkgI3.AbVar.baseChange
#check @AlgebraicGeometry.IsOpenImmersion.lift
#check @IsAlgClosed.lift

-- fold check: with the target theorem as a hypothesis, SS1 ∧ SS3 come from fields that stay on the chain
-- (sga3_VIB_3_10, sga7_IX_3_3 = derived from sga7_IX_3_3_SH + pair, geomConnOfRationalPoint), no semistablePersistsSHcp.
theorem ss1_ss3_of_persistsT2 (hP : ReductSplit.SemistablePersistsDVR) (h36 : ReductSplit.SemistableReductionDVR)
    (hN : ReductSplit.NeronSchemeModelExistsDVR) (hLG : ReductSplit.SemistableLocalGlobal)
    (hAA : ReductSplit.SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨ReductB.semistableReductionThm_final_nf (ReductB.reductionNF_of_general h36) (ReductB.persistsNF_of_general hP)
      hN hLG hAA,
    ReductB.semistablePersists_final_nf (ReductB.persistsNF_of_general hP) hN hLG⟩

open HDec.HSyn in
example (target : CToPrinted.SGA3_VIB_3_10 → CToPrinted.SGA7_IX_3_3 → AVGlue.GeomConnOfRationalPoint →
      ReductSplit.SemistablePersistsDVR)
    (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ss1_ss3_of_persistsT2 (target r.sga3_VIB_3_10 r.sga7_IX_3_3 t.geomConnOfRationalPoint)
    (semistableReductionDVR_of14 r t) r.neronSchemeModelExistsDVR
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open14 r t l))

-- task 2, step 5: the one new transport lemma (template: `hasSemiAbelian_pullback`, TailZ14:1006, for field isos)
def SemiAbelianBaseChangeAlgClosedT2 : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] [IsAlgClosed k] [IsAlgClosed k'] (σ : k →+* k')
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G], LocallyOfFiniteType G.hom → QuasiCompact G.hom →
    ZInQ.HeightSplit.HasSemiAbelianIdentityComponent G →
      (letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom σ))).obj G) := Functor.grpObjObj
       ZInQ.HeightSplit.HasSemiAbelianIdentityComponent ((Over.pullback (Spec.map (CommRingCat.ofHom σ))).obj G))

#check @ReductGlue.hasSemiAbelian_pullback
#check @ReductGlue.semiAbelianFieldIsoInvariant
#check @ReductGlue.hasSemiAbelian_of_iso
#check @CToPrinted.idComp_baseChange
