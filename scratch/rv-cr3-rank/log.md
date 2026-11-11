# rv-cr3-rank log

## 2026-11-11 run 1
- Started fresh (no log). HEAD aa494aae.
- Started `lake build ZInQKernel` (output scratch/rv-cr3-rank/build.log).
- Read Rank/Statements.lean, RankVariants.lean, RK9.lean, RankMW.lean, key statements of Image/Counting/Delta,
  Selmer/Covering.lean (Sel2, Loc, CertifiedRankSel), Rank5b/Sec3/TYZ.lean, RedeiStatement.lean, Row5b.lean.
- No shadowing definitions of Sel2/Loc/T5b/shortCurve/kummer in ZInQKernel (grep).
- Findings so far (non-blocking): CertifiedRankRk's TYZ bullet omits Rédei's formula and Cor 4.4 / Thm 3.6
  (both needed to get from #Sel2=8, |a|≡7 to TYZ's class-number hypothesis); CertifiedRankTYZRk → CertifiedRankRk
  is Lean-derivable (det_M5b_eq_one, det_M5b_eq_T5b) but not stated.
