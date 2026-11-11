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
