# cr3-adopt log

Base: 81bb5d8f (wip/cr3-adopt from origin/wip/integrate-w19).

- Step 0: read rv-cr3-trust.md, cr3-trust.md, rv-prop-n.md. rv-cr3-rank (aec3b570) is an ancestor of
  HEAD (merged at 609e6eb2). Line numbers of §0 checked against HEAD.
- Step 1: docs/research/cr3-trust.md: all repairs of rv-cr3-trust §6 applied (Summary, §0.1-0.3,
  A1, A2, A5, A6, B5, B8, C1-C3, D1-D3, E3, §2.1, §2.2, §2.4, §2.6, §3 drafts, §4), changelog
  added at the end. docs/research/nt-tyz.md: dated note at the end with rv-prop-n's corrections
  (text above unchanged).
- Step 2: docstrings/comments only. CertifiedRank.lean (docstring = cr3-trust §3 draft);
  Rank/Statements.lean (CertifiedRankRk, CertifiedRankTYZClRk trust paragraphs = drafts;
  CertifiedRankTYZRk: auxiliary field); Row5b.lean (CertifiedRank5b: GZ with auxiliary field,
  rank ≥ 1, Lean derivation); Selmer/Covering.lean (CertifiedRankSel: TYZ route first, Kriz as
  alternative not needed); Sec3/TYZ.lean, Sec3/RedeiStatement.lean (Murty–Murty dropped, rv-prop-n,
  Lean derivation); RankVariants.lean module doc; Rank5b.lean variant doc; Main.lean (two
  passages); RankInf.lean, RankDL.lean (same literature). Pole.lean left alone (it describes the
  manuscript's own RC proof). Build pending (step 4).
- Step 3: KERNEL_PLAN.md CR₃ passages: PC row of the table and the CR₃ paragraph lead with
  TYZ + Proposition N + Gross–Zagier with an auxiliary field (Kriz an alternative, not needed),
  pointer to cr3-trust.md / rv-cr3-trust.md; the 5b and DLAdmRk SixContactMin variants added;
  sentence that TYZClRk implies all 14 forms. Rest unchanged.
- Step 4: `lake build ZInQKernel`: success (9919 jobs; output scratch/cr3-adopt/build.txt).
  `lake env lean scripts/print_axioms.lean`: 61 entries, all exactly [propext, Classical.choice,
  Quot.sound] (scratch/cr3-adopt/axioms.txt). Comment-only check
  (scratch/cr3-adopt/strip_check.py 81bb5d8f HEAD): all 11 changed .lean files IDENTICAL after
  stripping comments and docstrings (strip_check_out.txt); the stripper was mutation-tested (a
  changed `T5bCl d = 1` is detected, a changed docstring word is not).
