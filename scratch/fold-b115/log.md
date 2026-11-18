# fold-b115 log

Base wip/leaf-fold33b 1496913c (= fork main 67950e82 + inbox 71: Tau Ceti Homogeneous.lean restored, CloudW07 lemma
renamed `eval2_const_mul_chart`). H top `HDec.HSyn.sixContactMin_of_open76` (TailZ83, `OpenResearchLeaves57`).
Build tree `.lake/build` and `lean/.lake/build` copied (reflink) from a sibling worktree at the same commit.

## 0. Base checks (VERIFIED, 11-17 14:10)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15987 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- Base hash dump (DumpCompact): 18987 constants (/tmp/fb115/hashes_fold0.txt, not committed).
- `render_open.py`: 29 H hypotheses, strictest 5/24, 1 other; `--check` ok, 30 open hypotheses.
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**

## Fold 1: ss-faltings (inbox 74; sga7_IX_Cor3_3_Def34 -> faltingsSemistableHeightBC; bypass, count-neutral)

1. Merged origin/wip/ss-faltings d230fa8e (main f3402e89 merged into it; no conflicts: its Tau Ceti Homogeneous edits
   are already undone by the base's inbox-71 fix, the merge left Homogeneous.lean, HomogeneousCharts.lean and
   ThirdParty/TauCeti/NOTICE as on the base; commit 86231f4c). Hygiene: `scratch/ss-faltings/BypassFold.lean` and
   `BypassCheck.lean` (redeclare `HDec.HSyn.OpenResearchLeaves58SF`) renamed `.lean.txt`; no host paths, no session
   names; build logs on the branch are 8-line truncations (kept); no vendored code.
2. Generator `scratch/fold-b115/fold_ssf.py` (runs ss-faltings' `gen/gen_bypass.py`, then moves the module to the next
   TailZ, edits Main and the kinds row). Finding: with the branch's default names (`OpenResearchLeaves58SF`,
   `sixContactMin_of_open77sf`) `scratch/lane74/gate.sh` FAILS: `autofold: cannot parse Main.lean` (autofold's
   regex `sixContactMin_of_open(\d+) ` does not match `open77sf`). The fold therefore uses the generator's own
   arguments `OpenResearchLeaves58` / `sixContactMin_of_open77` (the names the integrator's note gives). Same text
   otherwise (gen_bypass.py with explicit arguments).
3. Finding: with `SSFChain.lean` in `ZInQKernel/Contrib/OneProof/`, `#discharges` (DischargesTest) lists every
   projection of its copied bundles as a self-match: 246 DISCHARGES lines instead of 16, and render_open copies them
   into CONTRIBUTING.md's worked example (+725 lines). The generated chain copy is therefore moved to
   `ZInQKernel/OneProof/H/SSFChain.lean` (with the earlier copy reroutes NoSGA3Copy, GoodModelIsoCopy,
   EichlerBoundCopy; `git mv`, content unchanged); the proof files `SSFaltings.lean`, `SSFaltingsGR9.lean` stay in
   Contrib. TailZ84's import and docstring path follow.
4. Fold: `ZInQKernel/OneProof/H/TailZ84.lean` (OpenResearchLeaves58, 27 fields = OpenResearchLeaves57 with
   `sga7_IX_Cor3_3_Def34` replaced by `faltingsSemistableHeightBC`; conversion
   `openResearchLeaves57SF_of_OpenResearchLeaves58`; `sixContactMin_of_open77`); Main -> TailZ84,
   `sixContactMin_of_open77`, docstring paragraph; kinds row `sga7_IX_Cor3_3_Def34` replaced by
   `faltingsSemistableHeightBC` (published; flag "pending reading: Faltings 1983 section 1 not read ... locator
   UNVERIFIED ..."; GLUE/GLUE; flag_class pending-reading; label, area_issue of the old row). claims.tsv: no row.
   gen_bypass count line: strict 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24.
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.OneProof.H.TailZ84
   ZInQKernel.OneProof.H.SSFChain ZInQKernel.Contrib.OneProof.SSFaltings ZInQKernel.Contrib.OneProof.SSFaltingsGR9` ok
   (15991 jobs); `sixContactMin_of_open76_sf` and `frozenTarget`: [propext, Classical.choice, Quot.sound].
6. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 18987 -> 19972, only before 0, only after 985
   (SSFChain 950, TailZ84 35), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold1.txt`). Closure
   (`FoldCheck-fold1.txt`, 292905 constants): sorryAx, `SGA7_IX_Cor3_3_Def34`, `SGA7_IX_Cor3_3` (both),
   `CToPrinted.SGA7_IX_3_3`, `SemistablePersistsSHcp`, `SemistableNeronBaseChange`, `SemistablePersists`,
   `OpenResearchLeaves57`, `sixContactMin_of_open76` absent; `FaltingsSemistableHeightBC`, `SemistableReductionThmIF`,
   `semistableReductionThmIF_of_raynaud`, `OpenResearchLeaves58`, `sixContactMin_of_open77`, `sixContactMin_of_open76_sf`
   present; `SGA7_IX_3_5_ForwardGeom_Def34` present (d2a6b's row, not in this task). Field check: 27 vs 27, only
   `sga7_IX_Cor3_3_Def34` <-> `faltingsSemistableHeightBC`, no other type differs. OpenStatements: 30. render_open and
   `--check` ok. DischargesTest: 16 DISCHARGES lines (base 15; new: `faltingsSemistableHeightBC` by
   `SSFaltings.faltingsSemistableHeightBC_of_ss2`, still assumes `SemistableNeronBaseChange` = the never-stronger
   witness). frontier_crosswalk 232 IDs, 4 matched, `--check` ok. autoform check exit 0 (776 articles, 645 fully
   proved). gate.sh: GATE=ok. `#discharges` cannot show the field (bypass; the old field does not follow from the new
   leaf); the closure check shows it gone. No autofold spec (nothing discharged outright); the fold is reproduced by
   `fold_ssf.py`.
   **render_open count after fold 1: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
7. Manuscript check (VERIFIED against diophantine_zq.tex): L596-597 OK; L597-598 gap filled (uncited invariance
   sentence, now the leaf faltingsSemistableHeightBC, Faltings 1983 section 1); L598 and L875-876 gap filled ("stable
   Faltings height" occurs only there and is never defined; supplied in Lean); L620-621 gap filled (isogeny step
   needs a common semistable field, supplied at K(A[15])K(B[15])); L814-817 OK; no errors.

## Item 2: Tau Ceti pin identity (inbox 72; vendored Tau Ceti code-identical to Deicyde/TauCeti 86b92544)

1. Edits (exact lines from the integrator's note):
   - `ZInQKernel/Contrib/TauCeti/Backport/RingTheory/HahnSeries/Map.lean:228`:
     `simp [lin, coeff_monomial, Finsupp.single_apply, hf] at this` -> `simp [lin, coeff_monomial, hf] at this`;
   - `ZInQKernel/Contrib/TauCeti/Backport/Mathlib/Polynomial.lean:22`: `rw [if_neg hn.ne, sub_zero] at h1` ->
     `rw [ite_eq_right hn.ne, sub_zero] at h1`;
   - `ZInQKernel/Contrib/TauCeti/MathlibBackport/Sylow.lean:24`: the joined statement line of `maximal_isPGroup` split
     after `(P : Sylow p G) :` with a 4-space continuation (Mathlib layout; the pin's exact layout is UNVERIFIED, see 3);
   - `Homogeneous.lean` (72.4): VERIFIED already as required on the base (line 6 is the one-line "-- Vendored from
     Tau Ceti (..., commit 5a01f5fe3621, module TauCeti.RingTheory.MvPolynomial.Homogeneous), Apache-2.0." header;
     no "Modified for the Z-in-Q kernel" line; no `private`); no change.
2. Compile (VERIFIED): both pin lines compile. `lake build` of the three modules ok; then `lake build
   ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.AllContrib` ok (16285 jobs, 19 min 53 s:
   the changed oleans rebuild the OneProof chain TailG..TailZ84 and their Contrib dependents); frozenTarget
   [propext, Classical.choice, Quot.sound]. No lead-outbox entry needed (no pin line fails).
3. Diff count against the pin: NOT computable on this host. The pin's source (Deicyde/TauCeti 86b92544 = Tau Ceti
   5a01f5fe + the Mathlib v4.35.0 port commit) is not on disk (no `.lake/packages/TauCeti` in any worktree, no object
   86b92544 in the repository's object store; network blocked). Against the integrator's list of differences
   (72.1-72.4) the count is 0 code differences after this commit. Two layout items are UNVERIFIED: the Sylow line break
   (Mathlib style chosen) and "the pin's comment wrapping" in Map.lean (header comments untouched: they carry the
   Apache-2.0 4(b) modification notice "imports rewritten", still true).
4. Checks (`run_checks.sh 2 hashes_fold1.txt`, VERIFIED): hash guard 19972 -> 19972, changed 0 (`cmp_fold2.txt`);
   closure unchanged (292905, no sorryAx); OpenStatements 30; render_open and `--check` ok; DischargesTest 16 lines;
   crosswalk ok; autoform exit 0; gate.sh GATE=ok. ThirdParty/TauCeti/NOTICE needs no edit (no entry for these lines).
   **render_open count after item 2: 30 open (H 29, strictest 5/24, 1 other); unchanged.**

## Fold 3: pb-dimform + htmult-model (inbox 73, 75; no field change, count-neutral)

1. Merged origin/wip/pb-dimform 3d69c488 (base lane74b, an ancestor of this base; no conflicts; commit 785db9ac).
   Hygiene: build log `scratch/pb-dimform/build2.txt` (3541 lines) left out; no host paths; no vendored code; no scratch
   file redeclares an HDec.HSyn bundle (`PstModelCore.lean` is in `HDec.PkgI4.PstModel`, never built).
2. htmult-model 36bbcafab: its five own commits cherry-picked (`-x`: 883434f3, 5a44c505, 7a69754a, 79deac48, 36bbcafa).
   Not merged: the branch also merges fork main 06660f4a (PRs #87, #88: blueprint/ and top-level docs, 81 files), and
   this task may not merge main nor edit blueprint/. Its merge of pb-dimform is the one in 1. No host paths.
3. Row edits (`scratch/fold-b115/row_edits_q29.py`, idempotent; the integrator's texts verbatim, with inbox 75's two
   replacements in the panPrintedF flag): panPrintedF kind published -> consequence in the same commit as its flag;
   both rows flag/strict GLUE/strictest GLUE/source/rated_by `pb-p1 (unreviewed); pb-dimform; queue29 verdict 11-17`/
   flag_class `note`. Neither flag has a must_be_glue marker; both GLUE through the kind. pages-wanted loses both rows.
4. Field docstrings (`scratch/fold-b115/field_docs_q29.py`, docstring-only): panPrintedF and bergerSurveyF in
   TailZ83 (`OpenResearchLeaves57`) and TailZ84 (`OpenResearchLeaves58`, the current bundle) now state the dimension
   form over the image in B_dR of Brinon-Conrad's B_st (integrator's texts; the bergerSurveyF text is followed by
   ", for a de Rham p-adic representation V = E^n of G_Qp."). TailZ77-TailZ82 copies not regenerated, so not edited.
5. FINDING (AllContrib): appending `import ZInQKernel.Contrib.OneProof.HTModel` to `ZInQKernel/Contrib/AllContrib.lean`
   FAILS on this base: `error: ZInQKernel/Contrib/AllContrib.lean:3:0: import ZInQKernel.HDecomp.Textbook.Different
   failed, environment already contains 'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local`
   (VERIFIED, /tmp build log). HTModel's closure (PstModel -> PanBergerFontaine -> the OneProof chain) reaches
   `HDecomp.Textbook.Different`, whose def `TraceContainsRamificationIdx` (line 1736) is also a def in
   `Contrib/Different/Local.lean:1732`, which AllContrib imports. This is the pre-existing clash fixed on
   wip/contrib-clashes (not in this base nor in main). AllContrib left unchanged (base AllContrib builds, VERIFIED:
   12447 jobs); HTModel is built by name. For the lead: add the HTModel line after contrib-clashes is folded.
6. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
   ZInQKernel.Contrib.OneProof.PstModel ZInQKernel.Contrib.OneProof.HTModel ZInQKernel.Contrib.OneProof.PanBergerFontaine
   ZInQKernel.OneProof.H.TailZ84` ok (the AllContrib target was the only failure, item 5). `AxiomsFold3.lean`
   (`AxiomsFold3-output.txt`): `PstModel.localIsPstF_iff_forall`, `HTModel.localDistinctHTP_iff_forall`,
   `HTModel.htMultE_model_eq`, `PanDict.panBerger_of_F`, `frozenTarget`: [propext, Classical.choice, Quot.sound].
7. Checks (`run_checks.sh 3 hashes_fold2.txt`, VERIFIED): hash guard 19972 -> 19972, changed 0 (the docstring edits
   are not hashed; `PanPrintedF`/`BergerSurveyF` keep name and text). Closure 292918 (was 292905), no sorryAx;
   `BergerBst.IsAdmissible` (dimension form) present, `BmaxOne.IsAdmissibleT` (basis form) absent, `FontaineSt.IsPstF`
   present. OpenStatements 30; render_open + `--check` ok; DischargesTest 17 lines (new: `bergerSurveyF` by
   `PanDict.bergerSurveyF_of_basis`, still assumes `BergerSurveyFBasis`: the old basis-form leaf implies the new one,
   the never-stronger witness); crosswalk ok; autoform exit 0; gate.sh GATE=ok.
   **render_open count after fold 3: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
8. Manuscript check (VERIFIED against diophantine_zq.tex): L739-741 (Berger's p-adic monodromy theorem, cited
   `berger2002` with no theorem number; bibitem L11037-11040 names only "p-adic monodromy theorem") gap filled:
   locator Brinon-Conrad Thm 9.3.5 p. 148 (bibitem brinon-conrad L11019-11022 is in the bibliography); L736-738 (de Rham,
   two Hodge-Tate weights 0, -1) gap filled for the model clause: the weights do not depend on the finite coefficient
   model (HTModel.localDistinctHTP_iff_forall); L755-758 (Pan Thm 1.0.4 at l = 5, no residual proviso) OK;
   bibitems pan2022 (L11041-11044, arXiv v2, Thm 1.0.4), berger2002, brinon-conrad OK; no errors.
