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
- 01:22 generator scratch/hdec-adopt5a/adopt5a.py writes the five modules ModCurves/{C9,E1Sub,
  X1Belyi}.lean and Faltings/{HodgeLattice,H5Neron}.lean (one module per draft, same imports;
  import/#print lines moved; 17 long lines hand-wrapped, whitespace only). same.py: ALL SAME
  (whitespace-normalized text equal to the drafts). HDecomp.lean: 5 imports appended after the
  last import line (imports cannot follow the docstring). print_axioms.lean: 65 entries appended
  (axsec.py): the drafts' 62 targets + rhoF_semisimple_of_surj, modCurveLeaves_of,
  tangentDimAtOrigin_of. Not built yet (base build still running).
- 01:26 base build (before the new modules were picked up): exit 0, 9991 jobs.
- 01:32 VERIFIED `lake build ZInQKernel`: exit 0, 9996 jobs (5 new modules: H5Neron 62s,
  HodgeLattice 63s, X1Belyi 179s, C9 187s, E1Sub 190s; only linter/deprecation warnings).
- 01:33 VERIFIED `lake env lean scripts/print_axioms.lean`: exit 0, 464 axiom lists (399 + 65
  new), every one exactly [propext, Classical.choice, Quot.sound]; no other output. The 65 new
  entries: scratch/hdec-adopt5a/axioms.txt. No line over 100 characters in the changed Lean files;
  `sorry`/`axiom` occur only in comments ("no `sorry`, no `axiom`").
- 01:34 report docs/research/hdec-adopt5a.md written; adopt5a.py rerun: git status clean (byte-identical).
- (clock note: times above are by `date`; the base build took 10 min, 01:16-01:26.)
- 01:35-01:58 h5-neron part F, glue H4b. Diagnosis (Exp1-Exp3, scratch only): the kernel timeout
  is NOT in the IsMonHom instance comparison but in the equation `(bcGen 𝒢).hom = composite`
  (closed by `rfl`, and also by `rw`/`simp` with a final defeq step): `bcGen`'s declared source
  and target (`genericFibre L' _`, `(A.baseChange L').X`) and `𝒢.gen`'s type are not
  syntactically the composite's objects. Fix: `genIso` (𝒢.gen at unfolded type), `bcGen'` (the
  iso at the composite's type), `bcGen'_hom` by an explicit `Iso.trans_hom`/`congrArg₂` chain
  (each single-step lemma passes the kernel; `simp only` over the same lemmas still times out),
  then `bcGen'_isMonHom` by `rw [bcGen'_hom]; infer_instance`, and `groupModelBaseChangeExists`
  using `bcGen'` directly as the GroupModel's `gen`. Exp4.lean: 0 errors, all three
  `[propext, Classical.choice, Quot.sound]`.
- 02:00 module Faltings/H5BaseChange.lean (generator h4b.py: draft part F minus its unfinished
  comment and minus its two copied defs, which are verbatim in Faltings/H5Neron.lean (asserted),
  plus H4bAssembly.part). VERIFIED `lake build ZInQKernel` exit 0 (9997 jobs) and
  print_axioms exit 0: 471 entries (399 + 72), all [propext, Classical.choice, Quot.sound].
