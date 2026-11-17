# fold34-eichler log

Base wip/leaf-fold33b c0f3d085 (= origin/main, not moved; top `sixContactMin_of_open48`, TailZ55; render_open: 29 H
hypotheses, strictest 11/18, 6 others; 35 open). Build: reflink copy of `.lake/build` and `lean/.lake/build` from
the lcal-one worktree (byte-identical Main.lean; finished task); lake replayed Main.

## Step 0: merge origin/wip/eichler-bound (09896d1f)
- merged cleanly (c4866a12); brings wip/gr56-prove and wip/gr-dict: Contrib/OneProof/{GR56Lattice, GRDict,
  R5fpCountLe, EichlerBound/*}.lean, docs/research/{eichler-bound, gr56-prove, gr-dict}.md, scratch.
- hygiene: scratch files redeclaring HDec.HSyn bundles renamed .lean.txt: scratch/eichler-bound/BypassFold.lean,
  scratch/gr-dict/{BypassFold, BypassReach, FoldCheck}.lean, scratch/gr56-prove/FoldCheck.lean. Probe1.lean only
  `#check`s, kept. Host paths: none (grep for home-directory paths and the user name). No vendored code, no LICENSE.

## Step 1: Contrib helper (VERIFIED, compiled)
- `ZInQKernel/Contrib/OneProof/R5fpCountLeHF.lean`: `HDec.FS5NoCM.fibreComTrivialFull_of_leaves_hf'_le`,
  `fibreComTrivialFull_of_leaves_hf''_le` (the homfree forms of gr56-prove's `_le` lemmas; the live reader of the
  count on this base is `gluePieces_of_open4_hf_pz` -> `fibreComTrivialFull_of_leaves_hf''`, not the TailK one
  eichler-bound's generator patched) and `EichlerBound.r5fpCountLe_of_two (hG : GAGAMorphism)
  (hM : MumfordTorsionAlgClosed) : GR56.R5fpCountLe := r5fpCountLe_proof uniformizationLeafAll_proof hG hM`.
- `lake build ZInQKernel.Contrib.OneProof.R5fpCountLeHF`: ok (13390 jobs; R5fpCountLe and its EichlerBound modules
  built here for the first time on this base); both theorems [propext, Classical.choice, Quot.sound].

## Step 2: taint (VERIFIED, scratch/fold34-eichler/taint_out.txt)
- `Taint.lean` = fold33-pic's Taint2 with seeds the count projections `r5count`, `gonzalezRotgerCountX6`,
  `gonzalezRotgerCountX6Ab`, `gonzalezRotgerProp56X6`, and carriers extended to every structure in the closure with
  a count field, used or not (first run without the extension missed `ResearchLeaves3`, whose `r5count` is never
  read but which `gluePieces_of_open4_hf_pz` must build).
- closure 271552; 23 carriers (OpenResearchLeaves2, 5, 7, 8, 9, ResearchLeaves3, OpenResearchLeaves14GM..29GM, 31);
  81 tainted; the only non-forwarding reads: `researchLeaves8_of_open9_hf` (`r5fpCount_of_points`),
  `openResearchLeaves16_of_OpenResearchLeaves17_gm` (`gonzalezRotgerCountX6Ab_of_printed`),
  `researchLeaves9_of_open14_hf_gm_pz` (`gonzalezRotgerCountX6_iff_ab_gl`), and the reader in
  `gluePieces_of_open4_hf_pz`.

## Step 3: fold (commit 'fold gonzalezRotgerProp56X6')
- `gen/gen.py` (after fold33-pic's gen.py, with its copylib.py): `ZInQKernel/OneProof/H/EichlerBoundCopy.lean`,
  104 blocks (23 structures, X -> XEB / x_eb; `ResearchLeaves3.h5` copied as `ResearchLeaves3EB.h5` for `r.h5`),
  3312 lines; count fields typed `_root_.GR56.R5fpCountLe`, the three conversions replaced by forwarding, the reader
  by `fibreComTrivialFull_of_leaves_hf''_le`; the generator aborts on any other read of a count field.
  First build: error `ResearchLeaves3EB.h5` unknown (namespaced lemma filtered as a projection) -> fixed in gen.py;
  second build ok.
- `gen/top.py`: `ZInQKernel/OneProof/H/TailZ56.lean`: `OpenResearchLeaves32` (= OpenResearchLeaves31 without
  `gonzalezRotgerProp56X6`, 23 fields), `openResearchLeaves31EB_of_OpenResearchLeaves32 (n) (t : OpenTextbookLeaves16)`
  (`gonzalezRotgerProp56X6 := EichlerBound.r5fpCountLe_of_two t.gagaMorphism t.mumfordTorsionAlgClosed`: the two
  textbook inputs from the bundle, not from proofs), `sixContactMin_of_open49 r t l :=
  sixContactMin_of_open48_eb (...) t l`. Main patched (import TailZ56, `r : OpenResearchLeaves32`, open49, one
  docstring paragraph). First top.py run: struct-body regex swallowed the next docstring (unterminated comment) ->
  fixed; rerun.
- kinds.tsv: row `gonzalezRotgerProp56X6` (research, consequence, strict GLUE) dropped. claims.tsv: row
  `gonzalezRotgerProp56X6` (gr56-prove, held) dropped. No row added.
- reproducibility: from base Main + taint_out.txt, gen.py + top.py reproduce Main.lean, TailZ56.lean and
  EichlerBoundCopy.lean byte for byte (cmp). `replay.sh` runs the whole fold on a later head.

## Step 3 checks (all VERIFIED; outputs in scratch/fold34-eichler/)
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.EichlerBoundCopy
  ZInQKernel.OneProof.H.TailZ56 ZInQKernel.Contrib.OneProof.R5fpCountLeHF`: Build completed successfully (14243 jobs)
  (build_1.txt); sixContactMin_of_open49, frozenTarget: [propext, Classical.choice, Quot.sound].
- Discharges.lean (discharges_1.txt): `#discharges: 34 open hypotheses, 10264 theorems checked, 32 discharge one`;
  axioms standard for r5fpCountLe_proof, r5fpCountLe_of_two, eichlerOptEmbBound6,
  fibreComTrivialFull_of_leaves_hf''_le, sixContactMin_of_open48_eb, sixContactMin_of_open49, frozenTarget. No
  theorem has the type `GonzalezRotgerProp56X6` (the proved statement is weaker, so the field is removed by the
  bypass, not discharged).
- closure (closure_1_eichler.txt, 271942 constants): GRCountX6.GonzalezRotgerProp56X6, ShimuraSplit.GonzalezRotgerCountX6Ab,
  ShimuraSplit.GonzalezRotgerCountX6, LeafQM.AV.R5fpCount, GRCountX6.EichlerOptEmbCount6, sorryAx: false;
  GR56.R5fpCountLe, r5fpCountLe_proof, r5fpCountLe_of_two, fibreComTrivialFull_of_leaves_hf''_le,
  OpenResearchLeaves31EB, sixContactMin_of_open48_eb: true; OpenResearchLeaves31, sixContactMin_of_open48,
  sixContactMin_of_open45_pz, gluePieces_of_open4_hf_pz, fibreComTrivialFull_of_leaves_hf'': false; earlier folds'
  names still false. Bundles: OpenResearchLeaves32 23, OpenTextbookLeaves16 3, OpenAddedLeaves25 2 fields.
- hash guard (hashdiff_1_eichler.txt): before 15751, after 16589, only before 0, only after 838 (807
  EichlerBoundCopy + 31 TailZ56), changed 1: ZInQ.OneProof.frozenTarget.
- OpenStatements.lean: open-statements.json 34 open hypotheses (base 35).
- render_open.py, --check: **28 H hypotheses, strictest 11/17, 6 others**; "ok: 34 open hypotheses, all
  classified; 4 generated files up to date". STATUS.md strict count: 11 published / 17 glue (base 11/18): strict
  GLUE -1, no new leaf.
- frontier_crosswalk.py, --check: 232 IDs, 25 matched; up to date.
- DischargesTest rerun: `#discharges: 34 open hypotheses, 10267 theorems checked, 32 discharge one`.
- autoform check blueprint: OK: 781 articles, 2343 dependencies, 705 fully proved, 2531 declaration name(s) resolved.
