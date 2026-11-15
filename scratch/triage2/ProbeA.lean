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
