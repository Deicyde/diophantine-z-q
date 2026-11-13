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

## 22:58 PST: generator `adopt4.py` (9 modules); first `lake build` of the four leaf modules
(QM.Polar, Analytic.Uniformization, Analytic.QMLattice, LeafPush2.T) and dependencies: exit 0
(9068 jobs), no errors; warnings only (deprecations, linters). VERIFIED.

## 22:59 PST: statement check `same.py` (VERIFIED)
LeafPush2 (after Part I) 47/63, Torus 143/146, QMPolar 101/111 identical (whitespace-normalized
statement and proof). Missing are exactly the copies replaced by imports: LeafPush2 IsCurve,
IsJacobian, JacobianExists, IsBelyiFunction, B, ofInt, InO, mulCoord, ofInt_{mul,add,neg,zero,one},
O, QMStr, IsComplexConj; Torus AbVar, AbVar.ptObj, AbVar.Pt; QMPolar B … O. grep: no
sorry/admit/axiom; awk: no line > 100 characters.

## 23:00 PST: QM docstring repairs `docfix.py` (rv-qm-polar.md §4 item 2): QML3 (Structures),
R1fp, R5fp, R5fpCount, QMLeaves (Leaves). Docstrings only; wrap.py rewrapped two long lines.

## 23:07 PST: `lake build ZInQKernel` exit 0 (9989 jobs), after every Lean change. VERIFIED.
## 23:09 PST: `lake env lean scripts/print_axioms.lean` exit 0: 390 entries (332 + 58 new), all
exactly [propext, Classical.choice, Quot.sound]; list in axioms.txt. VERIFIED.
