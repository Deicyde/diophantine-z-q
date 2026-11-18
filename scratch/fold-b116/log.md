# fold-b116 log

Base wip/leaf-fold33b d804d07d (= fork main + fold-b115). H top `HDec.HSyn.sixContactMin_of_open77` (TailZ84,
`OpenResearchLeaves58`). Build tree `.lake/build`, `lean/.lake/build` copied (reflink) from the fold-b115 worktree
(8bef0560; no Lean file differs from d804d07d).

## 0. Base checks (VERIFIED, 11-17 15:17)
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`: ok (15991 jobs, replayed); frozenTarget
  [propext, Classical.choice, Quot.sound].
- Base hash dump (DumpCompact): 19972 constants (/tmp/fb116/hashes_fold0.txt, not committed).
- **render_open count at base: 30 open (H 29, strictest 5/24, 1 other).**

## Item 1: inbox 83 amendment to ss-faltings (faltingsSemistableHeightBC)
1. Generator `scratch/fold-b116/item1_ssf_amend.py` (text edits only):
   - kinds row `faltingsSemistableHeightBC`: kind published -> consequence; strict/strictest GLUE/GLUE (unchanged);
     flag = the reading desk's text (inbox 83, verbatim); flag_class pending-reading -> note; source locator
     "section 1 (locator UNVERIFIED ...)" -> "§3, p. 354"; rated_by "ss-faltings; the reading desk 11-17 (page read)".
   - leaf docstring `ZInQ.SSFaltings.FaltingsSemistableHeightBC` (Contrib/OneProof/SSFaltings.lean) and its module doc:
     locator §3 p. 354; the claim "the reason he gives is SGA 7 IX 3.3" removed; the Néron-model step
     N'^0 = (N^0)_{R'} (SGA 7 IX Cor. 3.3 / BLR 7.4/3, cited neither by Faltings there nor by the manuscript) named as
     part of the leaf.
   - field docstring in TailZ84 and Main's fold paragraph: "section 1" -> "§3, p. 354", Cor. 3.3 content named inside
     the leaf.
   - Not edited (other declarations' docstrings that say "Faltings 1983 §1" for the stable height in general:
     G0StableBC, HeightDictionary, JavanpeykarDirect, JavanpeykarAnRetype, PrintedStableHeight, LPrefix, TailA, TailY).
2. Build (VERIFIED): `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
   ZInQKernel.Contrib.OneProof.SSFaltings ZInQKernel.Contrib.OneProof.SSFaltingsGR9 ZInQKernel.OneProof.H.SSFChain
   ZInQKernel.OneProof.H.TailZ84` ok (15991 jobs); frozenTarget standard.
3. Checks (`run_checks.sh 1 hashes_fold0.txt`, VERIFIED): hash guard 19972 -> 19972, no constant changed, none new
   (docstring-only edits; `cmp_fold1.txt`). Closure (`FoldCheck-fold1.txt`): sorryAx absent; state as after fold-b115
   (`SGA7_IX_Cor3_3_Def34` absent, `SGA7_IX_3_5_ForwardGeom_Def34` present). OpenStatements: 30. render_open and
   `--check` ok. DischargesTest: 17 DISCHARGES lines, output file unchanged. frontier_crosswalk 232 IDs, 4 matched,
   `--check` ok. autoform check exit 0 (776 articles, 647 fully proved). gate.sh: GATE=ok.
   kinds rows: none added or dropped (one row edited); claims.tsv unchanged.
   **render_open count after item 1: 30 open (H 29, strictest 5/24, 1 other); 5/24 on 29 (unchanged: the row was
   already GLUE/GLUE).**
4. Wording for the report and landing note: "SGA 7 IX Cor. 3.3 no longer a separate row; its content is named inside
   faltingsSemistableHeightBC".
5. Manuscript check (VERIFIED by reading diophantine_zq.tex): L596-598 ("This extension does not change its stable
   Faltings height", uncited): gap filled by the leaf faltingsSemistableHeightBC, now located at Faltings 1983 §3
   p. 354 (the reading desk's page read; not re-read here: UNVERIFIED by this task) with the Néron-model step
   (SGA 7 IX Cor. 3.3 / BLR 7.4/3) inside the leaf; bibitem faltings1983 L11084-11086 OK.

## Item 2: d2a6b (inbox 76; sga7_IX_3_5_ForwardGeom_Def34 -> elliotWildInertiaTrivial; bypass regenerated on this top)
1. Merged origin/wip/d2a6b 6570dbca (clean; commit 44fd0ac0). Hygiene: scratch/d2a6b BypassFold.lean, ClosureCheck.lean,
   PruneScanBypass.lean (redeclare `HDec.HSyn.OpenResearchLeaves58`) and Discharges.lean (imports the superseded
   Contrib chain) renamed `.lean.txt`; no host paths; no vendored code.
2. Generators copied to `scratch/fold-b116/gen-d2a6b/` and retargeted (d2a6b's own scratch files unchanged):
   TaintD.lean/TaintD2.lean import `OneProof.H.SSFChain`, root `HDec.HSyn.sixContactMin_of_open73_sf` (ss-faltings'
   copy of TailZ80's top; TailZ81-84 are field conversions); gen_chain.py TOP `sixContactMin_of_open73_sf`, module
   order from SSFChain, the r14 edit also matches `raynaudCriterionNF_of14_hf_gm_eb_sf`; gen_bypass.py CHAIN_R
   `OpenResearchLeaves54SF`, CHAIN_TOP `sixContactMin_of_open73_sf`, chain import `ZInQKernel.OneProof.H.D2A6Chain`.
3. Taint (VERIFIED): `lake build D2A6Wrap A6Z30` ok (14424 jobs); TaintD: closure 274018, IX 3.5: 28 carriers (base
   d2a6b on TailZ83: 31, incl. OpenResearchLeaves55-57 above its chain top), 829 T/S lines; TaintD2 28 carriers.
4. `python3 scratch/fold-b116/fold_d2a6b.py`: gen_chain 131 blocks (102 declarations, 29 structures; edits r14 1,
   qml3 1): 90 from SSFChain, 25 EichlerBoundCopy, 9 TailH, 7 HomFree Consumers (d2a6b on TailZ80: 91 from TailZ80,
   same others). Chain written to `ZInQKernel/OneProof/H/D2A6Chain.lean` (top `sixContactMin_of_open73_sf_u` on
   `OpenResearchLeaves54SFU`); d2a6b's superseded `Contrib/OneProof/D2A6Chain.lean` (generated on TailZ80, same
   declaration names) removed with `git rm`. gen_bypass --mode post: `OpenResearchLeaves58` (27 fields) ->
   `OpenResearchLeaves59` (27), top `sixContactMin_of_open78` (numeric names), module `TailZ85`; removed
   `sga7_IX_3_5_ForwardGeom_Def34`, added `elliotWildInertiaTrivial`, mapped `silverbergZarhinThm35`,
   `y3FullThreeRepZ30`; strict 5/24 on 29 -> 5/24 on 29, strictest 5/24 -> 5/24; new row elliotWildInertiaTrivial
   consequence GLUE/GLUE (note), replaces the sga7_IX_3_5_ForwardGeom_Def34 row in kinds.tsv. claims.tsv: no row for
   either field on this base (nothing to drop).
5. Build (VERIFIED): `lake build ZInQKernel.OneProof.H.D2A6Chain ZInQKernel.OneProof.H.TailZ85
   ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.A6Z30` ok (15997 jobs);
   frozenTarget [propext, Classical.choice, Quot.sound]. D2A6Chain has the source's linter warnings (ambiguous
   `open` namespaces), no errors.
6. Checks (`run_checks.sh 2 hashes_fold1.txt`, VERIFIED): hash guard 19972 -> 21006, only before 0, only after 1034
   (D2A6Chain 999, TailZ85 35), changed only `ZInQ.OneProof.frozenTarget` (`cmp_fold2.txt`). Closure
   (`FoldCheck-fold2.txt`, 292618 constants): absent sorryAx, `SGA7_IX_3_5_ForwardGeom_Def34`,
   `SGA7_IX_3_5_ForwardGeom`, the three `RaynaudCriterionNF`, `raynaudPlace_of_R6`, `torsFix_of_descent`,
   `modelG3G6_of_leaves3`, `good_of_QML3`, `SGRSplit.ShimuraIntegralModelRep`, every Cor. 3.3 form,
   `SemistableNeronBaseChange`, `SemistablePersists`, `OpenResearchLeaves58`, `sixContactMin_of_open77`; present
   `RaynaudWildNF`, `ElliotWildInertiaTrivial`, `SilverbergZarhinThm35`, `Y3FullThreeRepZ30`,
   `FaltingsSemistableHeightBC`, `D2A6.R6U`, `sixContactMin_of_open73_sf_u`, `OpenResearchLeaves59`,
   `sixContactMin_of_open78`. **Constants whose name contains `SGA7` or `sga7` in the closure: 0** (no SGA 7 IX 3.3 /
   3.5 row or statement left). Field check: 27 vs 27, only `sga7_IX_3_5_ForwardGeom_Def34` <->
   `elliotWildInertiaTrivial`, no other type differs. OpenStatements: 30. render_open and `--check` ok. DischargesTest:
   18 DISCHARGES lines (was 17; new: `elliotWildInertiaTrivial` by `SZRaynaud.elliot_of_semistableUnipotent`,
   conditional on SemistableUnipotent = IX 3.5: the new field is not stronger than the old). frontier_crosswalk 232
   IDs, 4 matched, `--check` ok. autoform exit 0. gate.sh: GATE=ok (numeric names parse).
   **render_open count after item 2: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
7. Manuscript check (VERIFIED by reading diophantine_zq.tex): L383-384 (S contains every prime <= 324) OK;
   L529-530 ("The proper model and its universal abelian scheme give good reduction outside the places over S",
   no argument) gap filled (A6Z30: classifying point, valuative criterion, base change, rigidity; on-the-spot bridge
   ofKer, proved); L557-558, L752-753, L781 OK (uses of L529-530); L814-816 (A[3], A[5] if p = 3; Raynaud's
   criterion [silverbergzarhin, Thm 3.5]) OK; L817-818 ("Its wild inertia acts trivially on each V_l(A)", uncited)
   gap filled (citation: the ELLIOT field elliotWildInertiaTrivial); L443-453, L464-472, L472-477 unverified
   (inside the leaf y3FullThreeRepZ30; not re-read); L453-462 OK per d2a6b (not re-checked here: unverified by this
   task). No errors.

## Item 3: r16-thm1b (inbox 79; afShimura + heckeJ1DS -> shimuraThm1Af + bShStandardModel; autofold)
1. Merged origin/wip/r16-shimura73 aa28045a (clean; commit 42e13ffc). Hygiene: scratch/r16-shimura73/FoldCheck.lean,
   TailZ75R16.lean, scratch/r16-thm1/FoldCheck.lean, scratch/r16-thm1b/FoldCheck.lean (redeclare HDec.HSyn bundles)
   renamed `.lean.txt`; scratch/r16-thm1b/build-main.txt (114841 lines) truncated to first/result lines (commit
   0478c133); no host paths; no vendored code.
2. `lake build ZInQKernel.Contrib.OneProof.R16Thm1b` ok (11363 jobs). Spec copied unchanged to
   `scratch/fold-b116/autofold-r16thm1b.json` (= scratch/r16-thm1b/autofold.json). Dry run: exit 0, strict 5/24 on 29 ->
   5/24 on 29, strictest 5/24 -> 5/24 (no --allow-rise).
3. `python3 scripts/one_proof/autofold.py scratch/fold-b116/autofold-r16thm1b.json`: TailZ86 (`OpenResearchLeaves60`,
   27 fields: heckeJ1DS, afShimura out; bShStandardModel, shimuraThm1Af in), top `sixContactMin_of_open79`; Main
   switched; kinds rows: afShimura, heckeJ1DS dropped, bShStandardModel and shimuraThm1Af added (both consequence
   GLUE/GLUE, pending-review), each byte-identical to scratch/r16-thm1b/kinds-diff.txt; claims.tsv: no row for either
   field. The G1 Prop `R16ShimuraLi.ShimuraTotalToComponents` is not in the spec.
4. Build (VERIFIED): `lake build ZInQKernel.OneProof.H.TailZ86 ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges`
   ok (16002 jobs); frozenTarget standard.
5. Checks (`run_checks.sh 3 hashes_fold2.txt`, VERIFIED): hash guard 21006 -> 21041, only after 35 (TailZ86), changed
   only `ZInQ.OneProof.frozenTarget`. Closure (292708): sorryAx absent; `R16ShimuraLi.ShimuraTotalToComponents` absent
   (G1 kept out); `R16Thm1b.ShimuraThm1Af`, `R16Thm1.BShStandardModel` present; `AfTateLam.AfShimura`, `HeckeJ1DS`
   present only as conclusions (filled by `afShimura_of_thm1Af`, `heckeJ1DS_of_bSh`; not fields); SGA7-named
   constants 0. Field check: 27 vs 27, only in old [heckeJ1DS, afShimura], only in new [bShStandardModel,
   shimuraThm1Af], no other type differs. OpenStatements 30. render_open, `--check` ok. DischargesTest 18 lines
   (renames only). crosswalk ok. autoform exit 0. gate.sh GATE=ok.
   **render_open count after item 3: 30 open (H 29, strictest 5/24, 1 other); strict 5/24 on 29 (count-neutral).**
6. On-the-spot pieces (labelled, from the merged branch, none added): (B1) the kernel's IsX1Gen model is Shimura's
   standard model; (B4) the double-coset convention dictionary (Shimura's xi_p, <d> act by DS's formulas); both inside
   the leaf bShStandardModel. shimuraThm1Af's three on-the-spot steps (C = I_f J; (ii) for all n from p, p^2;
   nu-compatible isomorphisms) are flagged in its row.
7. Manuscript check (VERIFIED by reading diophantine_zq.tex L764-775): L767-768 (absorb the character, primitive
   newform) OK; L768-770 (Li's Fricke formula) unverified here (not on the fold's route: the Euler clause is not in
   the row); L770-771 (Shimura's quotient construction [shimura-factors, Thm 1], bibitem L11053) OK as a citation,
   with the on-the-spot pieces B1, B4 and the three flagged steps; L771-773 ("therefore show that r_5 is a constituent
   of the Tate module of A_f") unverified (gap, not filled: the G1 Prop is kept out; the Lean route uses DS 9.6.5,
   afCharpolyDS965); no errors.

## Item 4: logp-transc (inbox 82; proof-only, count-neutral)
1. Files taken from origin/wip/logp-transc 707e4799 (the SHA in the inbox) with `git checkout 707e4799 -- ...`:
   Contrib/OneProof/LogPTranscendence.lean, LogPTranscendenceBdR.lean, docs/research/logp-transc.md,
   scratch/logp-transc/, .fleet/logp-transc.md. Not a merge: the branch also carries htmult-model's commits (already
   cherry-picked on this base) and its dependencies (PanBergerFontaine, PstModel, HTModel, BdRInvariants) are
   identical to this base's (`git diff HEAD 707e4799` empty on them). The branch has three later commits (bbd0679d,
   14:47: "units analogue", +217 lines in LogPTranscendence.lean); not taken (not in the inbox). Hygiene: no host
   paths; scratch copies of the Contrib files do not declare HDec.HSyn bundles.
2. Build (VERIFIED): `lake build ZInQKernel.Contrib.OneProof.LogPTranscendence
   ZInQKernel.Contrib.OneProof.LogPTranscendenceBdR` ok (10718 jobs; build-logp.txt). Axioms (AxiomsLogP-output.txt):
   logPTildeTranscendental_iff_notInFrac, _of_notInFrac, transcendental_bcris_of_notInFrac, bcrisOf_le_bmax,
   bstFOf_eq_adjoin, bcrisPolyEquiv, transcendental_bcrisOf: all [propext, Classical.choice, Quot.sound].
3. AllContrib: NOT added. Appending both imports makes `lake build ZInQKernel.Contrib.AllContrib` fail with the same
   pre-existing clash as HTModel: `import ZInQKernel.HDecomp.Textbook.Different failed, environment already contains
   'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local` (allcontrib-logp-attempt.txt);
   reverted. Add both lines once wip/contrib-clashes is folded.
4. Flag narrowing (optional, applied; `rows_items45.py logp`): in the panPrintedF and bergerSurveyF flags,
   "(BergerBst.LogPTildeTranscendental is an open Prop)" -> "(... is an open Prop, reduced in Lean to log[p~] not in
   Frac(B_max) (LogPTransc.logPTildeTranscendental_iff_notInFrac, Contrib/OneProof/LogPTranscendenceBdR.lean))".
   The inbox wrote the name as `LogPTranscendence.logPTildeTranscendental_iff_notInFrac`; the declaration is
   `HDec.PkgI4.LogPTransc.logPTildeTranscendental_iff_notInFrac` in LogPTranscendenceBdR.lean, so the flag uses that.
   Ratings unchanged (GLUE/GLUE, note).
5. Checks (`run_checks.sh 4 hashes_fold3.txt`, VERIFIED): hash guard 21041 -> 21041, nothing changed or new
   (nothing under OneProof imports the new files). Closure as after item 3. OpenStatements 30, render_open and
   `--check` ok, DischargesTest 18, crosswalk ok, autoform exit 0, GATE=ok.
   **render_open count after item 4: 30 open (H 29, strictest 5/24, 1 other); 5/24 on 29.**
6. Manuscript check: L739-741 (Berger's p-adic monodromy theorem [berger2002] makes the de Rham representation
   potentially semistable) unchanged from fold-b115 (gap filled for the citation; the BC 9.2.10 identification remains
   GLUE, now reduced in Lean to the one Prop log[p~] not in Frac(B_max)); the Galois half of Fontaine's argument is an
   on-the-spot (c) fill, proved (logp-transc §1). No errors.

## Item 5: docs edits (inbox 78 items 1-2, inbox 80)
1. `python3 scratch/fold-b116/rows_items45.py docs` (VERIFIED by the diff):
   - javanpeykarThm111An: "(Szpiro, Asterisque 127, Lemme 3.2.1, Ch. I)" -> "(Szpiro (ed.), Asterisque 127, Chap. I,
     Lemme 3.2.1)"; appended "; locators page-checked 11-17: arXiv v1 p. 1 (Thm 1.1.1), p. 9 (§2.3); ANT p. 90; ANT
     p. 98 not reachable, arXiv v1 is the cited print"; leading "reading risk: " dropped and flag_class reading-risk
     -> note (no other reading risk in the flag: the remaining items are a ruling request on the composite, the
     semistability-clause note and "locators UNVERIFIED" for the Faltings/Deligne independence step). Rating
     consequence GLUE/GLUE unchanged (the flag still contains "UNVERIFIED", so must_be_glue). pages-wanted loses the
     row.
   - r9a source: "Faltings 1983 Satz 3" -> "Faltings 1983 §5 Endomorphismen, Satz 3, p. 360"; r9b source: "Faltings
     1983 Satz 4, Kor. 1" -> "Faltings 1983 §5, Satz 4 p. 360 and Korollar 1 p. 361"; dsThm966Printed source locator
     -> "Deligne-Serre, Thm 4.1 with (4.1.1), pp. 513-514", flag + " (print not in the manuscript's bibliography)".
     Ratings unchanged.
   - Docstrings: dsThm966Printed field docstring in TailZ86 (the newest module; rebuilt anyway): "p. 514" -> "pp.
     513-514". r9a/r9b fields have no docstring in the bundles. The r9a docstring at Contrib/G9/I3Layer.lean:879
     (`PkgI3.FaltingsSemisimple`) NOT edited: the module is low in the import graph and no fold of this task rebuilds
     it (inbox 78: docstring edits only in modules the fold rebuilds anyway). Inbox 78 item 3 waits for #90.
   - claims.tsv (inbox 80, hand edit): hPC row added exactly as given (task "#83 / PR #90 (Theorem 5.3 headline)",
     status "PR #90 under review", holder_kind project, public_holder project, claim_url .../pull/90, hold held; since
     and issue empty). No PoincareComplement row: AVB1.PoincareComplement is not an open field on this head (OPEN.md
     lists 29 H fields + hPC; none is PoincareComplement). pazukiCor13Upper row dropped: origin/wip/pazuki-inputs last
     commit 11-16 23:33 PST, origin/wip/pazuki-route last commit 11-17 02:49 PST, no activity after 11-17 12:00 PST.
2. Build: TailZ86 + Main + Discharges ok (16002 jobs), frozenTarget standard.
3. Checks (`run_checks.sh 5 hashes_fold4.txt`, VERIFIED): hash guard unchanged (21041, nothing changed: docstring
   only); closure as after item 3; OpenStatements 30; render_open, `--check` ok; DischargesTest 18; crosswalk ok;
   autoform exit 0; GATE=ok.
   **render_open count after item 5: 30 open (H 29, strictest 5/24, 1 other); 5/24 on 29.**
4. Manuscript check: not applicable to locator text, except: Deligne-Serre is not in the manuscript's bibliography
   (VERIFIED: no bibitem for deligne-serre in diophantine_zq.tex); Faltings 1983 is (bibitem faltings1983 L11084).

## Report
- docs/research/fold-b116.md, scratch/fold-b116/REPLAY.md. Build logs build-wrap.txt (100234 lines) and
  build-logp.txt (3941 lines) truncated to their axioms/result lines.
- Final state (VERIFIED, after item 5): top `sixContactMin_of_open79` (TailZ86, `OpenResearchLeaves60`); 30 open
  (H 29, strictest 5/24, 1 other); strict 5/24 on 29; no SGA7-named constant in frozenTarget's closure.
