# hdec-adopt5a results log

- 01:16 start. Base 883c4ddf. No ZInQKernel oleans in the worktree: base build started (one lake).
- h5-neron is NOT merged in the base (origin/wip/h5-neron = b7c1dc21, merge-base 01267822).
  Sources read with `git show origin/wip/h5-neron:scratch/h5-neron/<f>.lean` into
  scratch/hdec-adopt5a/src/ (no merge, so no file outside this task's paths changes).
- Duplicate scan (scratch/hdec-adopt3/dups.py on the five drafts): no draft declaration is a
  verbatim copy of an HDecomp declaration (11 same-last-name hits, all different code in other
  namespaces). No full name is declared in two drafts. C9's copies (FrobeniusDense, PkgI4 leaves
  R14/T24/T25/AttachedUpToTwist) come from scratch/h-decomposition/Leaves.lean, not in the build:
  kept.
- Docstring repairs applied: VSurjOfSurjective (ModCurves/Glue.lean), Ej (ModCurves/Defs.lean),
  R03_LinYang (LeafPush2/R3.lean).
- 01:50 generator scratch/hdec-adopt5a/adopt5a.py writes the five modules ModCurves/{C9,E1Sub,
  X1Belyi}.lean and Faltings/{HodgeLattice,H5Neron}.lean (one module per draft, same imports;
  import/#print lines moved; 17 long lines hand-wrapped, whitespace only). same.py: ALL SAME
  (whitespace-normalized text equal to the drafts). HDecomp.lean: 5 imports appended after the
  last import line (imports cannot follow the docstring). print_axioms.lean: 65 entries appended
  (axsec.py): the drafts' 62 targets + rhoF_semisimple_of_surj, modCurveLeaves_of,
  tangentDimAtOrigin_of. Not built yet (base build still running).
- 01:26 base build (before the new modules were picked up): exit 0, 9991 jobs.
- 01:32 VERIFIED `lake build ZInQKernel`: exit 0, 9996 jobs (5 new modules: H5Neron 62s,
  HodgeLattice 63s, X1Belyi 179s, C9 187s, E1Sub 190s; only linter/deprecation warnings).
- 01:35 VERIFIED `lake env lean scripts/print_axioms.lean`: exit 0, 464 axiom lists (399 + 65
  new), every one exactly [propext, Classical.choice, Quot.sound]; no other output. The 65 new
  entries: scratch/hdec-adopt5a/axioms.txt. No line over 100 characters in the changed Lean files;
  `sorry`/`axiom` occur only in comments ("no `sorry`, no `axiom`").
