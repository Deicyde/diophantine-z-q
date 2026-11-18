# fold-b116: the ss-faltings amendment, d2a6b, r16-thm1b, logp-transc, row and claims edits

Task fold-b116, 2026-11-17. Base: wip/leaf-fold33b d804d07d (fork main plus fold-b115). The branch wip/fold-b116 is
that base plus this task's commits, so wip/leaf-fold33b can fast-forward to it. The results log is
scratch/fold-b116/log.md, and replay instructions are in scratch/fold-b116/REPLAY.md. This is model work and no person
has reviewed it.

Marks: **VERIFIED** means compiled, or read in a named file. **UNVERIFIED** means not checked here.

## 1. Result

**All five items are in, built and checked. No SGA 7 statement is left in the proof: the closure of
`ZInQ.OneProof.frozenTarget` has no constant whose name contains `SGA7` or `sga7` (VERIFIED).** The count is unchanged
at 5/24 on 29 strict (strictest 5/24), with 30 open hypotheses. No manuscript step was found to be an error.

| | top | open | H strict / strictest |
| --- | --- | --- | --- |
| base | `sixContactMin_of_open77` (TailZ84, `OpenResearchLeaves58`) | 30 | 5/24 on 29 |
| 1. inbox 83: `faltingsSemistableHeightBC` row and docstrings | unchanged | 30 | 5/24 on 29 |
| 2. d2a6b: `sga7_IX_3_5_ForwardGeom_Def34` → `elliotWildInertiaTrivial` (bypass, regenerated) | TailZ85, `sixContactMin_of_open78` (`OpenResearchLeaves59`) | 30 | 5/24 on 29 |
| 3. r16-thm1b: `afShimura`, `heckeJ1DS` → `shimuraThm1Af`, `bShStandardModel` (autofold) | TailZ86, `sixContactMin_of_open79` (`OpenResearchLeaves60`) | 30 | 5/24 on 29 |
| 4. logp-transc: two Contrib files, flag narrowing | unchanged | 30 | 5/24 on 29 |
| 5. inbox 78 items 1-2, inbox 80 | unchanged | 30 | 5/24 on 29 |

SGA 7 IX Cor. 3.3 is no longer a separate row; its content is named inside `faltingsSemistableHeightBC`. SGA 7 IX 3.5 is
gone: D2 now uses Raynaud's criterion as the manuscript cites it (`silverbergZarhinThm35`, already a field) together
with the manuscript's own uncited sentence L817-818 (`elliotWildInertiaTrivial`). A6 and the kernel field's good
reduction now use the model of Y₃ over ℤ[1/30] (`y3FullThreeRepZ30`, already a field).

**Checks after each item** (VERIFIED; files `scratch/fold-b116/*-fold<k>.txt`):
- The build of Main + Discharges + the touched modules succeeds, and `frozenTarget` uses only
  `[propext, Classical.choice, Quot.sound]`.
- DumpCompact hash guard against the previous step:
  - items 1, 4 and 5: no constant changed, none new (the Lean edits are docstrings only);
  - item 2: only `ZInQ.OneProof.frozenTarget` changed; 1034 new constants (D2A6Chain 999, TailZ85 35);
  - item 3: only `ZInQ.OneProof.frozenTarget` changed; 35 new constants (TailZ86).
- Closure: no `sorryAx`, and none of the removed Props.
- OpenStatements gives 30.
- render_open, frontier_crosswalk and both `--check` runs pass. DischargesTest was rerun, and the autoform check exits 0.
- `scratch/lane74/gate.sh` gives GATE=ok.

## 2. For the lead

1. **d2a6b's chain is rooted on ss-faltings' chain.** The new chain `ZInQKernel/OneProof/H/D2A6Chain.lean` copies
   the IX 3.5 carriers of `sixContactMin_of_open73_sf`, which is SSFChain's copy of TailZ80's top. Its copies are:
   - 90 from SSFChain, 25 from EichlerBoundCopy, 9 from TailH and 7 from HomFree Consumers;
   - 29 structures;
   - top `sixContactMin_of_open73_sf_u` on `OpenResearchLeaves54SFU`.

   The bypass maps `OpenResearchLeaves59` field by field onto `OpenResearchLeaves54SFU`, so later folds that only
   rename or convert top fields need no new chain (REPLAY.md §2). The retargeted generators are in
   `scratch/fold-b116/gen-d2a6b/`; d2a6b's own scratch files are unchanged. d2a6b's superseded
   `Contrib/OneProof/D2A6Chain.lean` was generated on TailZ80, nothing imports it, and it has the same declaration
   names, so it was removed (`git rm`).
2. **Names.** The bundle and top are `OpenResearchLeaves59` / `sixContactMin_of_open78`, so gate.sh parses them.
3. **Order of items 2 and 3 on a replay.** Keep d2a6b before r16-thm1b. gen_bypass refuses a top bundle whose fields
   it cannot map; after r16-thm1b those fields are `bShStandardModel` and `shimuraThm1Af` (REPLAY.md §3 gives the two
   conversion lines that would lift this).
4. **logp-transc: the inbox SHA 707e4799 was taken, not the branch tip.** The branch has three later commits
   (bbd0679d, 11-17 14:47: a "units analogue", +217 lines in LogPTranscendence.lean). They are not in the inbox and are
   not taken.
   - The files came in with `git checkout 707e4799 -- …`. A merge would re-merge htmult-model's commits, which this
     base has as cherry-picks. Their dependencies are byte-identical to this base.
   - **They are not in AllContrib.** The same pre-existing clash as HTModel stops it:
     `PkgI6.TraceContainsRamificationIdx` (Contrib/Different/Local vs HDecomp/Textbook/Different). The error is in
     `scratch/fold-b116/allcontrib-logp-attempt.txt`.
   - The flag cites the declaration's real name, `HDec.PkgI4.LogPTransc.logPTildeTranscendental_iff_notInFrac` (in
     LogPTranscendenceBdR.lean). The inbox wrote `LogPTranscendence.…`.
5. **Docstring not edited: `Contrib/G9/I3Layer.lean:879`** (r9a, `PkgI3.FaltingsSemisimple`). That module is low in
   the import graph and none of these folds rebuilds it. Inbox 78 limits docstring edits to rebuilt modules. The r9a
   and r9b bundle fields have no docstrings.
6. **javanpeykarThm111An's flag_class is set to `note`, as asked.**
   - The flag still says "Faltings 1983 section 1, Deligne Sem. Bourbaki 616 section 1; locators UNVERIFIED" for the
     independence-of-field step, so the row stays GLUE by `must_be_glue`.
   - Inbox 83's page read puts Faltings' invariance at §3 p. 354. That locator may be wanted in this flag too; I did
     not change it, because it is not in the inbox text.
   - The same "Faltings 1983 §1" locator remains in other declarations' docstrings, which were not edited: G0StableBC,
     HeightDictionary, JavanpeykarDirect, JavanpeykarAnRetype, PrintedStableHeight, LPrefix, TailA, TailY.
7. **claims.tsv.**
   - The hPC project row is added exactly as given; `since` and `issue` are empty.
   - No PoincareComplement row: it is not an open field on this head.
   - **The pazuki row is dropped.** The last commits are 11-16 23:33 PST on origin/wip/pazuki-inputs and 11-17 02:49
     PST on origin/wip/pazuki-route, so neither branch shows activity after 11-17 12:00 PST.
   - d2a6b's claims row: this base has none, so there was nothing to drop.

## 3. Item 1: inbox 83 (ss-faltings amendment)

Generator `scratch/fold-b116/item1_ssf_amend.py` (commit 41ab4253).
- **kinds row `faltingsSemistableHeightBC`.**
  - Kind published → consequence. Strict and strictest stay GLUE.
  - The flag is the reading desk's text, verbatim: Faltings 1983 §3 p. 354; the deciding step N'^0 = (N^0)_{R'}
    (SGA 7 IX Cor. 3.3 / BLR 7.4/3, cited in neither place); normalization at p. 351.
  - flag_class pending-reading → note. The locator "section 1 (UNVERIFIED)" becomes "§3, p. 354".
- **The leaf's docstring** (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`, Contrib/OneProof/SSFaltings.lean).
  - The claim that Faltings "gives SGA 7 IX 3.3 as the reason" is removed.
  - It now says what p. 354 prints: invariance for a semiabelian scheme, with no citation.
  - It names the Néron-model step as part of the leaf.
- The field docstring in TailZ84 and Main's fold paragraph are updated to match.
- The hash guard shows no change. The count is unchanged: the row was already GLUE/GLUE.

**Manuscript check** (diophantine_zq.tex, read here):

| tex lines | step | verdict |
|---|---|---|
| L596-598 | "This extension does not change its stable Faltings height." (uncited) | gap filled (the leaf `faltingsSemistableHeightBC`, now located at Faltings 1983 §3 p. 354 by the reading desk's page read, UNVERIFIED here; SGA 7 IX Cor. 3.3's content named inside it) |
| L11084-11086 | bibitem faltings1983 | OK |

On-the-spot statements: none.

## 4. Item 2: d2a6b (inbox 76)

**Merge.** Merge 44fd0ac0, no conflicts. Hygiene: `BypassFold.lean`, `ClosureCheck.lean` and `PruneScanBypass.lean`
redeclare `OpenResearchLeaves58`; `Discharges.lean` imports the superseded chain. All four were renamed to `.lean.txt`.

**Regeneration** (commit c2b73c4d; `scratch/fold-b116/fold_d2a6b.py` with the generators in
`scratch/fold-b116/gen-d2a6b/`):
- **Taint**, rooted at `sixContactMin_of_open73_sf`: closure 274,018 constants, 28 IX 3.5 carriers. d2a6b's run on
  TailZ83 had 31, because it included `OpenResearchLeaves55`-`57`, above its chain top.
- **Chain**: 102 declarations and 29 structures. The edits are d2a6b's: `R6U`, `r6u`, the r14 producer and
  `good_of_QML3U`, each applied once.
- **Bypass**: TailZ85 `OpenResearchLeaves59` has 27 fields, `OpenResearchLeaves58` with
  `sga7_IX_3_5_ForwardGeom_Def34` replaced by `elliotWildInertiaTrivial`. Then come
  `openResearchLeaves54SFU_of_OpenResearchLeaves59` and `sixContactMin_of_open78`.
  - The conversion maps `faltingsSemistableHeightBC` and builds
    `r6u := ⟨raynaudWildNF_of_leaves sz elliot (Néron from neronSchemeExtensionDedekind), y3FullThreeRepZ30⟩`.
  - It also makes the three conversions of TailZ81-83 itself (`raynaudSemistableSHOr`, `y3FineModuliAbP`,
    `carayolThmAIrr`).
- **Rows.** The kinds row `elliotWildInertiaTrivial` (consequence, GLUE/GLUE, note) replaces the
  `sga7_IX_3_5_ForwardGeom_Def34` row.

**Closure (VERIFIED, `FoldCheck-fold2.txt`).**
- Absent:
  - `SGA7_IX_3_5_ForwardGeom_Def34`, `SGA7_IX_3_5_ForwardGeom`, all three `RaynaudCriterionNF`;
  - `raynaudPlace_of_R6`, `torsFix_of_descent`, `modelG3G6_of_leaves3`, `good_of_QML3`,
    `SGRSplit.ShimuraIntegralModelRep`;
  - every Cor. 3.3 form, `SemistableNeronBaseChange`, `SemistablePersists`;
  - **every constant named `*SGA7*` / `*sga7*` (count 0)**.
- Present: `RaynaudWildNF`, `ElliotWildInertiaTrivial`, `SilverbergZarhinThm35`, `Y3FullThreeRepZ30`,
  `FaltingsSemistableHeightBC`, `D2A6.R6U`.
- Field check: only the swapped field differs.

**DischargesTest** gains `elliotWildInertiaTrivial` by `SZRaynaud.elliot_of_semistableUnipotent`, conditional on IX 3.5:
the new field is never stronger than the old one. The count is 5/24 on 29 → 5/24 on 29.

**Manuscript check** (diophantine_zq.tex, read here; the integrator's expected verdicts were checked against the text,
not copied):

| tex lines | step | verdict |
|---|---|---|
| L383-384 | `S` contains every prime ≤ 324 | OK |
| L443-453 | Buzzard; full five-marking; the étale Isom sheaf | unverified (inside the leaf `y3FullThreeRepZ30`) |
| L453-462 | lattices in a rank-one `B₃`-module are principal | OK per d2a6b's hand check (not redone here: unverified by this task) |
| L464-472 | free action of `G₅` | unverified |
| L472-477 | the quotient represents the full-three problem | unverified (the ELLIOT leaf `y3FullThreeRepZ30`) |
| L529-530 | "The proper model and its universal abelian scheme give good reduction outside the places over S." (no argument) | gap filled (A6: `D2A6.hasGoodReduction_of_z30`, A6Z30.lean; uses the on-the-spot, proved bridge `ofKer`) |
| L557-558, L752-753, L781 | uses of good reduction outside `T` / at `p` | OK |
| L814-816 | `F = L_v(A[3])` (`A[5]` if `p = 3`), Raynaud's criterion [silverbergzarhin, Thm 3.5] | OK |
| L817-818 | "Its wild inertia acts trivially on each V_ℓ(A) with ℓ ≠ p." (uncited) | gap filled (citation: the ELLIOT field `elliotWildInertiaTrivial`) |

On-the-spot statements: none new. The bridge `ofKer`/`toKer` is d2a6b's and is proved.

## 5. Item 3: r16-thm1b (inbox 79)

**Merge and fold.**
- Merge 42e13ffc, no conflicts. Hygiene: three scratch `FoldCheck.lean` and `TailZ75R16.lean` renamed to `.lean.txt`.
  `build-main.txt` (114,841 lines) was truncated in 0478c133.
- Autofold with r16-thm1b's own spec, unchanged (`scratch/fold-b116/autofold-r16thm1b.json`), commit d10f1c2c:
  - TailZ86 `OpenResearchLeaves60`, top `sixContactMin_of_open79`;
  - out: `afShimura`, `heckeJ1DS`; in: `shimuraThm1Af` and `bShStandardModel`, both consequence GLUE/GLUE;
  - each new row is byte-identical to `scratch/r16-thm1b/kinds-diff.txt`;
  - the count is 5/24 on 29 → 5/24 on 29, with no `--allow-rise`.
- **The G1 Prop `R16ShimuraLi.ShimuraTotalToComponents` is not in the fold:** it is absent from the closure (VERIFIED).

**Labelled on-the-spot pieces** (from the merged branch; none added):
- **(B1)** the kernel's `IsX1Gen` model is Shimura's standard model;
- **(B4)** the double-coset convention dictionary: Shimura's ξ_p, ⟨d⟩ act by Diamond-Shurman's formulas.

Both sit inside `bShStandardModel`. `shimuraThm1Af`'s flag names its three on-the-spot steps: C = I_f J, (ii) for all
n from p and p², and ν-compatible isomorphisms.

**Manuscript check** (L764-775 read here):

| tex lines | step | verdict |
|---|---|---|
| L767-768 | absorb the character, take the primitive newform | OK |
| L768-770 | Li's Fricke formula [li-newforms, p. 296] | unverified (feeds only the Euler clause, which the row does not carry) |
| L770-771 | Shimura's quotient construction [shimura-factors, Thm 1] (bibitem L11053) | OK as the citation; the row adds the labelled on-the-spot pieces B1, B4 and three flagged steps |
| L771-773 | "therefore show that r_5 is a constituent of the Tate module of A_f" | unverified (gap, not filled; the G1 Prop is kept out; the Lean route uses DS 9.6.5, `afCharpolyDS965`) |

## 6. Item 4: logp-transc (inbox 82)

- **Files** (commit 221bce19): `Contrib/OneProof/LogPTranscendence.lean` and `LogPTranscendenceBdR.lean` from
  707e4799, plus the branch's report, scratch and fleet note.
- **Axioms** (VERIFIED, `AxiomsLogP-output.txt`): all standard for `logPTildeTranscendental_iff_notInFrac`,
  `_of_notInFrac`, `transcendental_bcris_of_notInFrac`, `bcrisOf_le_bmax`, `bstFOf_eq_adjoin`, `bcrisPolyEquiv` and
  `transcendental_bcrisOf`.
- Nothing under OneProof imports them, so the hash guard shows no change. They are not in AllContrib (§2.4).
- **The panPrintedF and bergerSurveyF flags are narrowed:** "… is an open Prop, reduced in Lean to log[p~] not in
  Frac(B_max) (LogPTransc.logPTildeTranscendental_iff_notInFrac, …)". Ratings are unchanged.

**Manuscript check:**
- L739-741 (Berger [berger2002] makes the representation potentially semistable): gap filled, as in fold-b115. The
  BC 9.2.10 identification is still GLUE, and is now reduced in Lean to the single Prop log[p̃] ∉ Frac(B_max).
- The Galois half of Fontaine's argument is an on-the-spot (c) fill, and it is proved.
- No errors.

## 7. Item 5: inbox 78 items 1-2, inbox 80

Commit e317745a, script `scratch/fold-b116/rows_items45.py docs`.
- **javanpeykarThm111An:**
  - the citation is now exactly "Szpiro (ed.), Asterisque 127, Chap. I, Lemme 3.2.1";
  - the page-check note is appended;
  - "reading risk:" is dropped and flag_class changes to note (see §2.6).
- **Locators:**
  - r9a "Faltings 1983 §5 Endomorphismen, Satz 3, p. 360";
  - r9b "Faltings 1983 §5, Satz 4 p. 360 and Korollar 1 p. 361";
  - dsThm966Printed "Deligne-Serre, Thm 4.1 with (4.1.1), pp. 513-514", with "(print not in the manuscript's
    bibliography)" added to its flag. VERIFIED: diophantine_zq.tex has no Deligne-Serre bibitem.
  - The dsThm966Printed field docstring is updated in TailZ86 only.
- claims.tsv: see §2.7.
- Ratings are unchanged. Inbox 78 item 3 waits for #90.

Manuscript check: not applicable (locator and claims text).

## 8. Files

- **New:**
  - `ZInQKernel/OneProof/H/TailZ85.lean`, `TailZ86.lean`, `D2A6Chain.lean`;
  - from merges: Contrib/OneProof A6Z30, A6IntModel, D2A6Wrap, D2WildNF, R16ShimuraLi, R16Thm1, R16Thm1b,
    LogPTranscendence, LogPTranscendenceBdR.
- **Removed:** `Contrib/OneProof/D2A6Chain.lean` (d2a6b's, superseded).
- **Edited:**
  - Lean: `Main.lean`; docstrings only in SSFaltings, TailZ84 and TailZ86;
  - docs/one-proof: kinds.tsv, claims.tsv and the regenerated files; STATUS.md.
- **`scratch/fold-b116/`:**
  - log.md and REPLAY.md;
  - the scripts item1_ssf_amend.py, fold_d2a6b.py, rows_items45.py and gen-d2a6b/;
  - the spec autofold-r16thm1b.json;
  - the check tools run_checks.sh, FoldCheck.lean, DumpCompact.lean, cmp_hashes.py and AxiomsLogP.lean;
  - the outputs of every check.
