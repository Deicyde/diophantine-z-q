# fold-b115: ss-faltings, the Tau Ceti pin lines, pb-dimform with htmult-model

Task fold-b115, 2026-11-17. Base: wip/leaf-fold33b 1496913c (fork main 67950e82 plus inbox 71's fix). The branch
wip/fold-b115 is that base plus this task's commits, so wip/leaf-fold33b can fast-forward to it. The results log is
scratch/fold-b115/log.md, and replay instructions are in scratch/fold-b115/REPLAY.md. This is model work and no person
has reviewed it.

Marks: **VERIFIED** means compiled, or read in a named file. **UNVERIFIED** means not checked here.

## 1. Result

**All three items are in, built and checked. The count is unchanged at 5/24 on 29 strict, 30 open.** No manuscript
step was found to be an error.

| | top | open | H strict / strictest |
| --- | --- | --- | --- |
| base | `sixContactMin_of_open76` (TailZ83, `OpenResearchLeaves57`) | 30 | 5/24 on 29 |
| 1. ss-faltings: `sga7_IX_Cor3_3_Def34` → `faltingsSemistableHeightBC` (bypass) | TailZ84, `sixContactMin_of_open77` (`OpenResearchLeaves58`) | 30 | 5/24 on 29 |
| 2. Tau Ceti pin lines (Map, Polynomial, Sylow) | unchanged | 30 | 5/24 on 29 |
| 3. pb-dimform + htmult-model: queue29 rows, field docstrings | unchanged | 30 | 5/24 on 29 |

**Checks after each item** (VERIFIED):
- The build of Main + Discharges + the touched modules succeeds, and `frozenTarget` uses only
  `[propext, Classical.choice, Quot.sound]`.
- DumpCompact hash guard against the previous step:
  - item 1: only `ZInQ.OneProof.frozenTarget` changed; 985 new constants (TailZ84 35, SSFChain 950);
  - items 2 and 3: no constant changed.
- Closure: no `sorryAx`, and none of the removed Props.
- OpenStatements gives 30.
- render_open, frontier_crosswalk and both `--check` runs pass. DischargesTest was rerun, and the autoform check exits 0.
- `scratch/lane74/gate.sh` gives GATE=ok.

## 2. For the lead

1. **Bypass names.** ss-faltings' default names `OpenResearchLeaves58SF` / `sixContactMin_of_open77sf` make gate.sh
   fail with "autofold: cannot parse Main.lean": autofold's regex is `sixContactMin_of_open(\d+) `. The fold therefore
   passes `OpenResearchLeaves58` / `sixContactMin_of_open77` to ss-faltings' own generator. The Lean text is otherwise
   identical.
2. **SSFChain moved to `ZInQKernel/OneProof/H/SSFChain.lean`.** This is the generated chain copy, unchanged by `git mv`.
   - In `Contrib/OneProof`, `#discharges` reports every projection of its 28 copied bundles as a self-match. That
     gives 246 DISCHARGES lines instead of 16, and render_open would paste them into CONTRIBUTING.md's worked
     example (+725 lines).
   - Under `OneProof/H` it sits with the earlier copy reroutes (NoSGA3Copy, GoodModelIsoCopy, EichlerBoundCopy).
   - The proof files `SSFaltings.lean` and `SSFaltingsGR9.lean` stay in Contrib.
   - d2a6b's chain will have the same problem if it is generated into Contrib.
3. **d2a6b.** Its chain and bypass must be regenerated on this branch's top: `sixContactMin_of_open77`,
   `OpenResearchLeaves58`, TailZ84. The next free number is TailZ85. This task did not fold d2a6b.
4. **Tau Ceti diff count against the pin: not computable here.** The pin's source (Deicyde/TauCeti 86b92544) is not on
   this host, and the network is blocked.
   - Measured against the integrator's list (72.1-72.4), 0 code differences remain.
   - Both pin lines compile, so nothing goes in lead-outbox.md.
   - Two layout points are UNVERIFIED:
     - the Sylow line break: I chose Mathlib layout, a break after `(P : Sylow p G) :` with a 4-space continuation;
     - "the pin's comment wrapping" in Map.lean: the header comments are untouched; they carry the Apache-2.0 §4(b)
       notice "imports rewritten", which is still true.
5. **HTModel is not in AllContrib.** Appending `import ZInQKernel.Contrib.OneProof.HTModel` makes AllContrib fail:
   `import ZInQKernel.HDecomp.Textbook.Different failed, environment already contains
   'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local`.
   - HTModel's closure (PstModel → PanBergerFontaine → the OneProof chain) reaches `HDecomp/Textbook/Different.lean`.
   - That file defines the same def as `Contrib/Different/Local.lean`, which AllContrib imports.
   - This clash already existed. wip/contrib-clashes fixes it, but that branch is not in this base or in main.
   - Add the line once contrib-clashes is folded: `field_docs_q29.py --allcontrib`.
6. **htmult-model was cherry-picked, not merged.** Its branch also merges fork main 06660f4a: PRs #87 and #88, 81
   files of blueprint/ and top-level docs. This task may neither merge main nor edit blueprint/, so only its five own
   commits came over, with `-x`.
7. **Field docstrings.** Edited in TailZ83 and in TailZ84 (the current bundle, which ss-faltings' generator copied
   from TailZ83). TailZ77-82 were not regenerated, so they were not edited. The bergerSurveyF text is the integrator's,
   followed by ", for a de Rham p-adic representation V = E^n of G_Qp."

## 3. Item 1: ss-faltings (inbox 74)

**Merge and fold.**
- Merge 86231f4c, no conflicts. Hygiene: `BypassFold.lean` and `BypassCheck.lean` renamed to `.lean.txt`.
- Fold bfaf3521 (generator `scratch/fold-b115/fold_ssf.py`):
  - TailZ84 adds `OpenResearchLeaves58`: 27 fields, `OpenResearchLeaves57` with `sga7_IX_Cor3_3_Def34` replaced by
    `faltingsSemistableHeightBC`.
  - The conversion to SSFChain's `OpenResearchLeaves57SF`.
  - The new top `sixContactMin_of_open77`.
  - Main switched to it, with a docstring paragraph.
- Kinds row `faltingsSemistableHeightBC`: published, flag "pending reading: Faltings 1983 section 1 not read ...
  locator UNVERIFIED ...", GLUE/GLUE, pending-reading. Label and area_issue are kept from the old row. claims.tsv has
  no row for it.

**Closure (VERIFIED).** Absent: `SGA7_IX_Cor3_3_Def34`, both `SGA7_IX_Cor3_3`, `CToPrinted.SGA7_IX_3_3`,
`SemistablePersistsSHcp`, `SemistableNeronBaseChange`, `SemistablePersists`. Present: `FaltingsSemistableHeightBC`,
`SemistableReductionThmIF`, `semistableReductionThmIF_of_raynaud`. `SGA7_IX_3_5_ForwardGeom_Def34` is still present;
that is d2a6b's row. Field check: 27 vs 27 fields, only the swapped field differs. DischargesTest gains
`faltingsSemistableHeightBC` by `faltingsSemistableHeightBC_of_ss2`, conditional on SS2: the leaf is never stronger
than the old field. On-the-spot statements: none.

**Manuscript check** (diophantine_zq.tex, VERIFIED by reading):

| tex lines | step | verdict |
|---|---|---|
| L596-597 | after a finite extension `E` has good reduction (integral `j`) | OK |
| L597-598 | "This extension does not change its stable Faltings height." | gap filled (uncited; now the leaf `faltingsSemistableHeightBC`, Faltings 1983 §1, bibitem faltings1983 L11084) |
| L598, L875-876 | "stable Faltings height", "original stable Faltings height" | gap filled (the phrase occurs only there and is never defined; supplied in Lean by `stableFaltingsHeight_eq_of_semistableF`) |
| L620-621 | height variation under isogeny [faltings1983] | gap filled (needs a common semistable field for source and target; supplied at K(A[15])·K(B[15])) |
| L814-817 | `A[3]` (`A[5]` if p = 3), Raynaud's criterion [SZ Thm 3.5] | OK |

## 4. Item 2: Tau Ceti pin lines (inbox 72)

Commit d4fb006a. Edits:
- `Backport/RingTheory/HahnSeries/Map.lean:228`: `simp [lin, coeff_monomial, hf] at this`, the pin's line without
  `Finsupp.single_apply`.
- `Backport/Mathlib/Polynomial.lean:22`: `rw [ite_eq_right hn.ne, sub_zero] at h1`.
- `MathlibBackport/Sylow.lean`: the statement line split.
- `Homogeneous.lean` already met 72.4 on the base: the one-line "Vendored from Tau Ceti" header, no "Modified" lines,
  no `private`.

Build (VERIFIED): Main + Discharges + AllContrib, 16285 jobs, 19 min 53 s. The changed oleans rebuild the whole
OneProof chain. The hash guard shows no change. ThirdParty/TauCeti/NOTICE needs no edit.

Manuscript check: not applicable. This is vendored library code with no manuscript step.

## 5. Item 3: pb-dimform + htmult-model (inbox 73, 75)

**Merges.** pb-dimform merge 785db9ac (build log left out). htmult-model: five commits cherry-picked (see §2.6).
- `FontaineSt.IsPstF` is now the dimension form `BergerBst.IsAdmissible` over `BstFOf`.
- Closure check (VERIFIED): `BergerBst.IsAdmissible` present, the basis form `BmaxOne.IsAdmissibleT` absent.
- `PanPrintedF` and `BergerSurveyF` keep their names and Lean text, so no OneProof hash changed.
- Axioms (VERIFIED, `AxiomsFold3-output.txt`): all standard for `PstModel.localIsPstF_iff_forall`,
  `HTModel.localDistinctHTP_iff_forall`, `HTModel.htMultE_model_eq`, `PanDict.panBerger_of_F` and `frozenTarget`.
- DischargesTest gains `bergerSurveyF` by `bergerSurveyF_of_basis`, conditional on the basis-form leaf: the new leaf is
  weaker.

**Rows** (`row_edits_q29.py`, the integrator's texts verbatim, with inbox 75's two replacements in the panPrintedF
flag):
- panPrintedF changes kind from published to consequence in the same commit as its flag.
- Both rows: GLUE/GLUE, flag_class note, rated_by `pb-p1 (unreviewed); pb-dimform; queue29 verdict 11-17`.
- pages-wanted loses both rows. The count is unchanged.

**Manuscript check** (VERIFIED by reading):

| tex lines | step | verdict |
|---|---|---|
| L736-738 | de Rham at ℓ, two Hodge-Tate weights 0, −1 | gap filled for the model clause: the multiplicities do not depend on the finite coefficient model (`HTModel.localDistinctHTP_iff_forall`) |
| L739-741 | Berger's p-adic monodromy theorem [berger2002] makes it potentially semistable | gap filled: the citation has no theorem number (the bibitem, L11037-11040, says only "p-adic monodromy theorem"); locator Brinon-Conrad Thm 9.3.5 p. 148 (bibitem brinon-conrad L11019-11022); the BC 9.2.10 identification remains GLUE |
| L755-758 | Pan Thm 1.0.4 at ℓ = 5, no residual-image proviso | OK |
| L11019-11044 | bibitems brinon-conrad, berger2002, pan2022 (arXiv v2, Thm 1.0.4) | OK |

On-the-spot statements: none.

## 6. Files

- New: `ZInQKernel/OneProof/H/TailZ84.lean`, and `ZInQKernel/OneProof/H/SSFChain.lean` (moved from Contrib).
- Edited: `ZInQKernel/OneProof/Main.lean`; TailZ83 docstrings; three vendored Tau Ceti files; docs/one-proof
  (kinds.tsv and the regenerated files); STATUS.md.
- `scratch/fold-b115/`:
  - fold_ssf.py, row_edits_q29.py, field_docs_q29.py (replay);
  - run_checks.sh, DumpCompact.lean, cmp_hashes.py, FoldCheck.lean, AxiomsFold3.lean;
  - outputs `*-fold{1,2,3}.txt`, `cmp_fold*.txt`;
  - log.md, REPLAY.md.
