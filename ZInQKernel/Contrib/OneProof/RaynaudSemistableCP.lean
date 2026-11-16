import ZInQKernel.OneProof.H.TailZ42

/-! # raynaud-proof: the live chain needs Raynaud's criterion only over `char 0` with algebraically closed residue field

Task raynaud-proof (docs/research/raynaud-proof.md). The research field `raynaudSemistableSH`
(`ReductGlue.RaynaudSemistableSH`, TailZ14; SGA 7 I Exp. IX Prop. 4.7 over a strictly henselian DVR, every `K`, every
residue field) is **not** proved here: no field of the bundles carries the monodromy input that 4.7 needs (report §2).

What is proved: every use of the field in the live proof goes through the restricted printed form
`ReductB.RaynaudSemistableSHcp` (TailZ23: strictly henselian, `[CharZero K]`, `[PerfectField κ(O)]`, hence `κ(O)`
algebraically closed), which is a specialization of the field (`raynaudSemistableSHcp_of_SH`). The field is read
only by `raynaudSemistable_of14` (TailZ23 L722), whose two readers are

* `raynaudCriterionNF_of14` (TailZ26 L171): r6 at number fields, via `GapNeron.raynaudCriterion_leavesNF`, which
  applies 4.7 at a number field; here `raynaudCriterion_leavesNF_cp`;
* `semistableReductionDVR_of14` (TailZ23 L727, K1), read only by `ss1_ss3_of14NF` (TailZ26 L179) through
  `GapNeron.ss1_ss3_of_cpNF`, which applies it at number fields only (`reductionNF_of_general`); here neron-dvr's
  `GapNeron.ss1_ss3_of_cp_fullNF` (already a theorem from `RaynaudSemistableSHcp`).

`consumers_of_cp` gives both conclusions (`RaynaudCriterionNF`, SS1 and SS3) from `RaynaudSemistableSHcp` and the
other fields of the current top bundles (`OpenResearchLeaves26`, `OpenTextbookLeaves12`, `OpenAddedLeaves17`), with
no use of `r.raynaudSemistableSH`. No `sorry`, no `axiom`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety Pts torsion galAct IsInertia UnipSq HasGoodReduction)

namespace RaynaudCP

open ReductSplit ReductGlue ReductB GapNeron

/-- The restricted printed leaf is a specialization of the field (so it is not stronger). -/
theorem raynaudSemistableSHcp_of_SH (h : ReductGlue.RaynaudSemistableSH) : ReductB.RaynaudSemistableSHcp :=
  fun K _ _ O _ _ hSH A m hm hmu ht => h K O hSH A m hm hmu ht

/-- **SGA 7 IX 4.7 at the discrete valuation rings of a number field** (`ReductSplit.RaynaudSemistable`, TailZ7,
verbatim with `[NumberField K]` added): the generality of every use in the live proof. -/
def RaynaudSemistableNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

theorem raynaudSemistableNF_of_general (h : ReductSplit.RaynaudSemistable) : RaynaudSemistableNF :=
  fun K _ _ O _ A m hm hmu ht => h K O A m hm hmu ht

/-- `RaynaudSemistableCP` gives the number-field form: the residue field of a DVR of a number field is finite,
hence perfect (`ReductB.perfectField_residue_nf`). -/
theorem raynaudSemistableNF_of_CP (h : ReductB.RaynaudSemistableCP) : RaynaudSemistableNF := by
  intro K _ _ O _ A m hm hmu ht
  haveI := perfectField_residue_nf O
  exact h K O A m hm hmu ht

/-- **4.7 at number fields from the restricted printed leaf**, the pair and `[m]` étale (reduct-b's
`raynaudSemistableCP_of_SH`). -/
theorem raynaudSemistableNF_of_SHcp (hR : ReductB.RaynaudSemistableSHcp)
    (hPair : ReductGlue.StrictHenselizationPair) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    RaynaudSemistableNF :=
  raynaudSemistableNF_of_CP (raynaudSemistableCP_of_SH hR hPair hE)

/-- `GapNeron.raynaudCriterion_of_leavesNF` (NeronDVR.lean) with `hR` at number fields (proof unchanged: it applies
`hR` only at the number field `K`). -/
theorem raynaudCriterion_of_leavesNF_cp (hR : RaynaudSemistableNF) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : RaynaudCriterionNF := by
  intro K _ _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (hasSemistableReduction_ofNF hN O B hss) ℓ hℓO σ hσ t)

/-- **r6 at number fields from the restricted printed 4.7** (the consumer `GapNeron.raynaudCriterion_leavesNF`
with `RaynaudSemistableSHcp` and the pair in place of `RaynaudSemistable`). -/
theorem raynaudCriterion_leavesNF_cp (hR : ReductB.RaynaudSemistableSHcp)
    (hPair : ReductGlue.StrictHenselizationPair) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNF :=
  raynaudCriterion_of_leavesNF_cp (raynaudSemistableNF_of_SHcp hR hPair hE) hU hN
    (AvSplit.torsionStructure_of_mumford hM) (ReductGlue.fixedTorsionRational_of_mulEtale hE)

/-- **The two live consumers of `raynaudSemistableSH` from `RaynaudSemistableSHcp` and the other fields of the
current top bundles**: r6 at number fields and SS1, SS3 (the two arguments that `sixContactMin_of_open20`, TailZ26,
computes from leaf-fold14's bundles with `raynaudCriterionNF_of14` and `ss1_ss3_of14NF`). The field
`r.raynaudSemistableSH` is not read. Each other input is computed by the same term the chain uses (TailZ28 L113,
TailZ33 L101, TailZ41 L88, TailZ26 L114, TailZ15 L87, TailZ26 L171-185). -/
theorem consumers_of_cp (hR : ReductB.RaynaudSemistableSHcp) (r : HDec.HSyn.OpenResearchLeaves26)
    (t : HDec.HSyn.OpenTextbookLeaves12) (l : HDec.HSyn.OpenAddedLeaves17) :
    RaynaudCriterionNF ∧
      (ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists) := by
  have hE : AvSplit.T4.MulEtaleAbelianScheme :=
    ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof
  have hPair : ReductGlue.StrictHenselizationPair :=
    GapSHPair.strictHenselizationPair_of_neron r.neronBaseChangeStrictHenselization
  have hU : SemistableUnipotent :=
    UnipotentForward.semistableUnipotent_of_forwardGeom r.sga7_IX_3_5_ForwardGeom hE
      r.neronBaseChangeStrictHenselization
  have hN : NeronSchemeModelExistsDVRNF := neronSchemeModelExistsNF t.neronSchemeExtensionExists
  have hSH : ReductB.SemistablePersistsSHcp :=
    GapPersists.semistablePersistsSHcp_of_SH r.sga3_VIB_3_10 r.sga7_IX_3_3_SH
      r.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint
  have hLG : SemistableLocalGlobal :=
    ReductGlue.semistableLocalGlobal_leaf (CToPrinted.neronLocalizesDVR_of_printed GapBLR.blr_1_2_4)
  have hAA : SemistableAlmostAll :=
    ReductGlue.semistableAlmostAll_of
      (HDec.HSyn.abVarSpreadsOut_of_ega4 ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof l.egaIV_8_10_5_xii
        ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof)
      (HDec.HSyn.properSmoothGenConnected_of_zariski4 ZariskiConn.ZariskiConnectedness_proof.{0})
  exact ⟨raynaudCriterion_leavesNF_cp hR hPair hU hN t.mumfordTorsionAlgClosed hE,
    ss1_ss3_of_cp_fullNF hR hSH hPair t.mumfordTorsionAlgClosed hE hN hLG hAA⟩

end RaynaudCP
