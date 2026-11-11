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
- `lake build ZInQKernel`: success (9906 jobs), tail in build-tail.txt.
- `lake env lean scripts/print_axioms.lean`: 38/38 entries [propext, Classical.choice, Quot.sound] (axioms.txt).
- Scratch Stmts.lean (deleted): elaborated statements (stmts.txt), Point group = Mathlib instAddCommGroup,
  and `CertifiedRankTYZRk → CertifiedRankRk` elaborates via det_M5b_eq_one + det_M5b_eq_T5b.
- Wrote docs/research/rv-cr3-rank.md. Verdict: no blocker; remarks R1–R4 (docstrings / KERNEL_PLAN wording).
- Wrote .fleet/rv-cr3-rank.md; done.
