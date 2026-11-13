# hdec-adopt4 results log

## 22:55 PST: duplicate scan (scratch/hdec-adopt3/dups.py on the three drafts; output dups_lp2.txt)
- LeafPush2.lean Part I (to `end ModelsSec`): 115 declarations, all SAME as the adopted
  `ZInQ.DefFaltings` (Faltings.{HodgeData,IdealLines,Models,Height}) after the namespace rename;
  `partI.py`: of 1398 non-blank lines, all but 6 occur in order in the Faltings modules (2 lines
  wrapped by wrap.py, `open PkgI3` vs `open PkgI3 (AbVar)`, 3 lines of a comment). VERIFIED.
- Part II: IsCurve, IsJacobian, JacobianExists, IsBelyiFunction SAME as LeafModCurves'.
- R3: B, ofInt, InO, mulCoord, ofInt_{mul,add,neg,zero,one}, O SAME as LeafQM's; QMStr differs
  only in binder placement from LeafQM.AV.QMStr; T: IsComplexConj = PkgI4.IsComplexConj up to
  the abbrev PkgI4.GQ and the bound-variable name.
- Torus.lean §10: AbVar (+instances), AbVar.ptObj, AbVar.Pt SAME as PkgI3's (Objects).
  QM.B (one-line abbrev) = LeafQM.B: kept (importing QM.Structures for it is a large dependency).
- QMPolar.lean: B … O SAME as LeafQM's (trd SAME text as GlueRepo.A1.trd but over a different
  `B`: kept).
- hdec-elementary's IC2…OnQMLocus (copied in R3) are not in the build: kept.
