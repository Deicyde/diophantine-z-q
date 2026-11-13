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

## Compile outcomes
- 16:51 `lake build` of the 15 new modules: 14 built; `Vigneras.Global` failed (wrap.py had
  broken a `first | … | (exfalso; revert h3; decide)` line inside a parenthesized tactic
  sequence: parse error). VERIFIED.
- Fix (in adopt2.py): that line becomes `first` followed by two lines of `| …` alternatives at
  one column (a first attempt with the `|` at a smaller column than the first `|` did not parse).
  16:58 `lake env lean ZInQKernel/HDecomp/Vigneras/Global.lean`: no errors. VERIFIED.
- 16:59 `lake build ZInQKernel`: exit 0 (incremental, 25 s; the full build before it took
  5 min 20 s and failed only at `Vigneras.Global` and its importers). VERIFIED.
- 16:59 `lake env lean scripts/print_axioms.lean`: 272 `#print axioms` lines, 272 outputs, each
  exactly `[propext, Classical.choice, Quot.sound]` (python check of the joined output). 93 of
  them are the new section (`scratch/hdec-adopt2/axioms_section.lean`). Output saved as
  `scratch/hdec-adopt2/axioms.txt` (it contains no file paths). VERIFIED.
- Checks on the new modules, `HDecomp.lean` and the new print_axioms lines: no line over 100
  characters (python, counting characters); no `sorry`/`admit`/`axiom` declaration (grep).
  VERIFIED.
- Verbatim-copy checks: C2's §1-§4 = pkg-I3 `I3.lean` lines 25-694 (difflib, one block of 670
  lines); TateBC §1 = I3.lean lines 26-123 (98 lines); WP3's PkgI6 blocks each occur in
  `Conductor/I6Base.lean` (whitespace-normalized substring); Disj's GlueSqrtLocal block =
  SqrtLocal lines 84-243 (160 lines); Disj's `LocalKroneckerWeber` body = I6Base's (docstring
  differs). VERIFIED.

## Second pass: copies found by body comparison (17:00-17:05 PST)
- Module headers revealed more copies with other names: `B3b.lean` copies glue-descent's
  `B2Glue` (`GQ`, its `IsTopologicalGroup` instance, `act`, `toRingAut`, `cyc`, `galChar`,
  `isLocallyConstant_of_openSubgroup`, `cyc_eq_of_agree`, `cyc_isLocallyConstant`,
  `galChar_isLocallyConstant`, `UnramifiedAt`) in namespace `GlueB3Unram`. The code is identical
  after normalizing whitespace and docstrings (`blocks.py`); `UnramifiedAt` differs only by
  `Qbar` (= `AlgebraicClosure ℚ`, abbrev). VERIFIED. They are replaced by
  `open GlueDescent.B2Q (…)` in both `namespace GlueB3Unram` blocks, plus an import of
  `Descent.B2Glue`.
- `Vigneras/Global.lean` copies `GlueRepo.A1.{B,comb,combMul}` (same code, VERIFIED): replaced by
  `open GlueRepo.A1 (B comb combMul)`; `comb_mul` (now the same statement as
  `GlueRepo.A1.comb_mul`) is proved by it.
- Body-level duplicate scan of all HDecomp modules (normalized declaration bodies over 60
  characters): the only remaining duplicates involving new modules are two lemmas proved twice
  inside `Sqrt/Disj.lean` (glue-sqrt-local's Frob, not an HDecomp module). VERIFIED.
- 17:02 `lake build ZInQKernel`: exit 0; `lake env lean scripts/print_axioms.lean`: 272 outputs,
  all `[propext, Classical.choice, Quot.sound]`. VERIFIED.
