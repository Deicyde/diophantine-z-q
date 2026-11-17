# pazuki-inputs results log

- 11-16 22:55 Merged fee21695 (pazuki-alg) cleanly into wip/pazuki-inputs (no conflicts). VERIFIED.
- Statements read (VERIFIED, ZInQKernel/Contrib/OneProof/PazukiCor13Upper.lean): `PazukiDict.SymmPrincipalDescends`,
  `ThetaDivisorAlgebraicC`, `AnalyticPPAlgebraic`, `IsSymmPrincipal`, `OnZeroLocus`, `liftPt`; PazukiAlg.lean: `RiemannPPAV`.
- Existing fields relevant to descent (VERIFIED, kinds.tsv + TailZ24/TailQ/PicZeroAbVar): picRepresentableAbVar (LEAF),
  kleimanPicZeroProper (LEAF), mumfordTorsionAlgClosed (LEAF); PicZeroAbVar statement in TailZ24.
- No copy of Mumford, *Abelian varieties* on this host (no network): the reading of RiemannPPAV cannot be done here.
- Glue.lean part 1 (bcMap, liftPt_ptE, bcMap_isPullback, surjective_bcMap) compiles, 0 errors. VERIFIED.
- Glue.lean: symmPrincipalDescends_of_definedOver (SymmPrincipalDescends from SymmPrincipalDefinedOver) compiles, 0 errors. VERIFIED.
