# hdec-adopt2 results log

## Plan and generator (16:50 PST)
- Generator: `scratch/hdec-adopt2/adopt2.py` (run `python3 -I scratch/hdec-adopt2/adopt2.py` from
  the worktree root; wraps long lines with `scratch/hdec-adopt/wrap.py`).
- Duplicate check: `scratch/hdec-adopt2/decls.py` lists declaration names declared in several
  files (simple parser of namespace/end). Run over the existing HDecomp modules and the drafts,
  it found (VERIFIED, run 16:49): the pkg-I3 copies in glue-ssbc/C2.lean (§1-§4), glue-rho-cont
  (§1-§2 and `TateModuleFree`), glue-I3-linalg/TateBC.lean (§1); the PkgI6 cochain leaves in
  glue-wp3/WP3.lean (= `Conductor/I6Base`); `PkgI6.LocalKroneckerWeber` and SqrtLocal's lines
  84-242 in glue-sqrt-disj/Disj.lean. No other collision.
- Superseded drafts (their content is inside an adopted superset file, VERIFIED from the drafts'
  logs and the duplicate check): glue-I3-linalg/{I3,Commutant,C2}.lean and glue-ssbc/SSBC.lean
  (inside glue-ssbc/C2.lean); glue-conj/{T1,T2,T3,Conj,UnramConj}.lean (inside glue-b3b/B3b.lean,
  namespace GlueB3Unram); glue-wp3's copies of glue-descent (byte-identical, per glue-wp3 log);
  glue-sqrt-local/{CycloPadic,SqrtFinite,Frob,Local,Unramified}.lean (inside SqrtLocal.lean and
  glue-sqrt-disj/Disj.lean); glue-sqrt-disj/{Level,Plumb,Ram}.lean (inside Disj.lean).
- QMDichotomy: the only uses in the adopted drafts are inside the dropped pkg-I3 copy of
  glue-ssbc/C2.lean (the leaf and `I3Leaves`); after the move all I3 uses refer to Objects'
  `PkgI3.QMDichotomyYu`. VERIFIED (grep).
