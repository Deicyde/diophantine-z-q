import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal
import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent
import ZInQKernel.Contrib.OneProof.SilvermanRankOne
import ZInQKernel.Contrib.OneProof.VpDualMerge.Chain
import ZInQKernel.Contrib.OneProof.TatePrints.Glue

/-! # Headline check for tate-module-prints

* `TatePrints.OpenAddedLeaves30`: the added bundle of the planned fold, with the two single-print
  rows `colmez1992DeRhamAbVar` and `fontaine1982HTAbVar`.
* `openAddedLeaves29VP_of_tatePrints`: the bundle gives the vpdual-merge bundle
  `OpenAddedLeaves29VP` (`vpDual`) through `vpDual_of_colmezFontaine`.
* `frozenTarget_with_tatePrints`: `ZInQ.OneProof.frozenTarget`'s body (`OneProof/Main.lean`)
  verbatim, with the added bundle replaced by the two rows, fed through `vpDual_of_colmezFontaine`
  into `OpenAddedLeaves29VP` and `HDec.HSyn.sixContactMin_of_open98_vp`.
  `frozenTarget_with_addedLeaves30` is the same over the bundle.
-/

namespace TatePrints

/-- The added bundle of the planned fold: the two single-print rows on the Tate module, in place
of `scholzeH1AbVar` and `t10TateDuality`. -/
structure OpenAddedLeaves30 : Prop where
  /-- Colmez, Math. Ann. 292 (1992), Théorème 5.2 (i)-(ii), p. 639 (period pairing). -/
  colmez1992DeRhamAbVar : DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar
  /-- Fontaine, Invent. Math. 65 (1982), Théorème 2, p. 388, with the count in its proof. -/
  fontaine1982HTAbVar : DeRhamScholze.TatePrints.Fontaine1982HTAbVar

/-- The bundle from the two rows. -/
theorem openAddedLeaves30_mk (hC : DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar)
    (hF : DeRhamScholze.TatePrints.Fontaine1982HTAbVar) : OpenAddedLeaves30 :=
  ⟨hC, hF⟩

/-- The two rows give the vpdual-merge bundle: `vpDual` from `vpDual_of_colmezFontaine`. -/
theorem openAddedLeaves29VP_of_tatePrints (n : OpenAddedLeaves30) :
    HDec.HSyn.OpenAddedLeaves29VP where
  vpDual := DeRhamScholze.TatePrints.vpDual_of_colmezFontaine n.colmez1992DeRhamAbVar
    n.fontaine1982HTAbVar

/-- **Theorem 1.1 with the two single-print rows** in place of the added bundle:
`frozenTarget`'s body, with `sixContactMin_of_open98_vp` fed `vpDual_of_colmezFontaine`. -/
theorem frozenTarget_with_tatePrints
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (hC : DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar)
    (hF : DeRhamScholze.TatePrints.Fontaine1982HTAbVar)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open98_vp r t
      ⟨DeRhamScholze.TatePrints.vpDual_of_colmezFontaine hC hF⟩)
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

/-- The same over the bundle `OpenAddedLeaves30` (the shape of the planned `frozenTarget`). -/
theorem frozenTarget_with_addedLeaves30
    (r : HDec.HSyn.OpenResearchLeaves78) (t : HDec.HSyn.OpenTextbookLeaves18)
    (l : OpenAddedLeaves30)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves)
    (hRank : ZInQ.Manuscript.PoleS12.SilvermanRank.SilvermanAEC_C_16_5_5_RankOne) :
    _root_.ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open98_vp r t (openAddedLeaves29VP_of_tatePrints l))
    (ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne hRC hCT
      (ZInQ.Manuscript.PoleS12.SilvermanRank.rankOne_of_aec hRank))

end TatePrints

#print axioms TatePrints.openAddedLeaves30_mk
#print axioms TatePrints.openAddedLeaves29VP_of_tatePrints
#print axioms TatePrints.frozenTarget_with_tatePrints
#print axioms TatePrints.frozenTarget_with_addedLeaves30
#print axioms DeRhamScholze.TatePrints.Gen.span_eq_top_of_nondeg
#print axioms DeRhamScholze.TatePrints.Gen.finrank_hom
#print axioms DeRhamScholze.TatePrints.Gen.exists_basis_of_span
#print axioms DeRhamScholze.TatePrints.Gen.precomp_injective
#print axioms DeRhamScholze.TatePrints.Gen.repr_fixed
#print axioms DeRhamScholze.TatePrints.Gen.finrank_of_basis
#print axioms DeRhamScholze.TatePrints.Gen.finrank_of_nondeg
#print axioms DeRhamScholze.TatePrints.Gen.forall_prop_of_nondeg
#print axioms DeRhamScholze.TatePrints.rep_surjective
#print axioms DeRhamScholze.TatePrints.bdrFix_le_filB_zero
#print axioms DeRhamScholze.TatePrints.filB_zero_mul
#print axioms DeRhamScholze.TatePrints.nondeg_range
#print axioms DeRhamScholze.TatePrints.equivariant_range
#print axioms DeRhamScholze.TatePrints.finrank_ddr_of_nondeg
#print axioms DeRhamScholze.TatePrints.ddr_le_filH_zero_of_nondeg
#print axioms DeRhamScholze.TatePrints.dual_deRham_fil0_of_colmez
#print axioms DeRhamScholze.TatePrints.htSpaceOver_eq_bot_of_card
#print axioms DeRhamScholze.TatePrints.cycPow_natCast
#print axioms DeRhamScholze.TatePrints.eq_zero_of_forall_mem_filB
#print axioms DeRhamScholze.TatePrints.iota_preJ
#print axioms DeRhamScholze.TatePrints.preJ_eq
#print axioms DeRhamScholze.TatePrints.thetaJ_spec
#print axioms DeRhamScholze.TatePrints.grJ_apply
#print axioms DeRhamScholze.TatePrints.grJ_mem
#print axioms DeRhamScholze.TatePrints.mem_filH_succ_of_grJ
#print axioms DeRhamScholze.TatePrints.ddr_inf_filH_two_eq_bot
#print axioms DeRhamScholze.TatePrints.vpDual_clauses_of_colmezFontaine
#print axioms DeRhamScholze.TatePrints.vpDual_of_colmezFontaine
