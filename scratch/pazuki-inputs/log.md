# pazuki-inputs results log

- 11-16 22:55 Merged fee21695 (pazuki-alg) cleanly into wip/pazuki-inputs (no conflicts). VERIFIED.
- Statements read (VERIFIED, ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean): `PazukiDict.SymmPrincipalDescends`,
  `ThetaDivisorAlgebraicC`, `AnalyticPPAlgebraic`, `IsSymmPrincipal`, `OnZeroLocus`, `liftPt`; PazukiAlg.lean: `RiemannPPAV`.
- Existing fields relevant to descent (VERIFIED, kinds.tsv + TailZ24/TailQ/PicZeroAbVar): picRepresentableAbVar (LEAF),
  kleimanPicZeroProper (LEAF), mumfordTorsionAlgClosed (LEAF); PicZeroAbVar statement in TailZ24.
- No copy of Mumford, *Abelian varieties* on this host (no network): the reading of RiemannPPAV cannot be done here.
- Glue.lean part 1 (bcMap, liftPt_ptE, bcMap_isPullback, surjective_bcMap) compiles, 0 errors. VERIFIED.
- Glue.lean: symmPrincipalDescends_of_definedOver (SymmPrincipalDescends from SymmPrincipalDefinedOver) compiles, 0 errors. VERIFIED.
- ZInQKernel/Contrib/OneProof/PazukiInputs.lean (lake env lean) compiles, 0 errors/warnings. VERIFIED.
- Build: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.PazukiInputs`
  -> `Build completed successfully (14230 jobs)`. VERIFIED (scratch/pazuki-inputs/build.txt).
- #discharges (scratch/pazuki-inputs/Discharges.lean; output discharges-output.txt): DISCHARGES
  [OpenResearchLeaves31.pazukiCor13Upper] by PazukiInputs.pazukiCor13Upper_of_definedOver, still assumes
  [GAGAMorphism, PazukiCor13UpperPP, RiemannPPAV, SymmPrincipalDefinedOver], axioms [propext, Classical.choice,
  Quot.sound]; "35 open hypotheses, 9866 theorems checked, 36 discharge one". VERIFIED.
- autofold dry run: refused without --allow-rise ("strict count: 11/18 on 29 -> 12/19 on 31; strictest 11/18 -> 12/19");
  with --allow-rise the module (line 1 stripped) is FoldCheck.lean; compiles; sixContactMin_of_open49 depends on
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- Verdict: target -1 GLUE not met (+1 with this fine spec, as pazuki-alg; coarse pazuki-dict spec neutral).
  RiemannPPAV reading impossible on host (no book, no network). SymmPrincipalDefinedOver composite, not proved.
