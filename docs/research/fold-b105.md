# fold-b105: three folds on wip/leaf-fold33b (chevalleyPerfect, semistab-assembly, pb-p1)

Task fold-b105, 2026-11-17. Base: wip/leaf-fold33b d67ea55f.
- H top before: `sixContactMin_of_open67`, TailZ74.
- Counts before: 36 open; H 31, strict and strictest 4/27.

Branch wip/fold-b105 is the base plus this task's commits, so it fast-forwards from d67ea55f. Results log:
`scratch/fold-b105/log.md`. This is model work; no person has reviewed it.

## 1. Result

**All three folds are in. Each builds, `frozenTarget` uses only the standard axioms, and every check passes.**

| fold | effect | new top | open | H strict / strictest |
| --- | --- | --- | --- | --- |
| base | | `sixContactMin_of_open67` (TailZ74) | 36 | 4/27 on 31 |
| 1 chevalleyPerfect | field removed outright, no new leaf (−1 field, −1 GLUE) | `sixContactMin_of_open68` (TailZ75, `OpenResearchLeaves49`) | 35 | 4/26 on 30 |
| 2 semistab-assembly | `bostLowerBoundAn`, `gaudronRemondThm14An` → `bostLowerBoundAnSS`, `gaudronRemondThm14AnSS` (count-neutral) | `sixContactMin_of_open69` (TailZ76, `OpenResearchLeaves50`) | 35 | 4/26 on 30 |
| 3 pb-p1 | `panPrintedP`, `bergerPrintedVT` → `panPrintedF`, `bergerSurveyF`; `r11r12 := panBerger_of_F` (count-neutral) | `sixContactMin_of_open70` (TailZ77, `OpenResearchLeaves51`) | 35 | 4/26 on 30 |

### Fold 1: bypass for `chevalleyPerfect`

fold-chev's generator stops at `sixContactMin_of_open67`. That step is coeff-field-tc's copy reroute: two `let` lines,
then a nested composite of 16 CF conversions.

The new generator `scratch/fold-b105/gen_chev_bypass.py` keeps fold-chev's helpers and adds:
- steps with `let` lines;
- nested research arguments, applied innermost first;
- a stop at the first conversion whose result has no `chevalleyPerfect`. Here that is `OpenResearchLeaves36EBCF`,
  after 11 conversions.

The three readers are rerouted to chevalley-free:
- `bostLowerBound` and `gaudronRemondThm14`, in the CF copy of 37EB→36EB, go to `ZInQ.ChevFree.*_of_printed_free`;
- `javanpeykarBound`, in 38EB→37EB, takes `semiAbelianDescendsPerfect_proof`.

The new top keeps the lets and re-enters the CF chain at 36EBCF.

`#discharges` cannot show `chevalleyPerfect` as discharged, because this is a bypass. The closure check shows the
field is gone instead.

### Fold 2: semistab-assembly autofold

- Spec: `scratch/fold-b105/autofold-semistab.json`. It is the branch's spec with both leaves set to kind `published`,
  as the lead ruled.
- Flags: both begin "pending review", so both rows are GLUE.
- `#discharges` on the fold-1 head lists both fields as DISCHARGED, with only the SS leaves assumed.

### Fold 3: pb-p1 bypass

- **Generator:** `scratch/fold-b105/gen_pbp1_bypass.py`. It rebuilds pb-p1's hand-written BypassFold on this head.
- **The one reader:** after fold 1, the only line that reads the two old fields is `r11r12`, inside fold 1's composite
  conversion. The generator rewrites it to `panBerger_of_F X.panPrintedF X.bergerSurveyF …`, with the same DS
  arguments. Every other conversion only passes the two fields through.
- **`#discharges` before the fold:**
  - `bergerPrintedVT` is DISCHARGED by `bergerPrintedVT_of_survey`.
  - `panPrintedP` is discharged only under `BmaxStToFontaine`, which is not a leaf. That is why this fold is a bypass.
- **Kinds rows:**
  - `panPrintedF`: published, flag "pending review; unread: …", GLUE/GLUE.
  - `bergerSurveyF`: published, flag "pending review (pb-p1; fold-b105): cited print; …", with no "unread". GLUE/GLUE.
- **Review row:** the audit's `panPrintedP` row in reviews.tsv failed render_open's row check. It was moved to
  reviews-retired.tsv, as was done for bergerPrintedV in batch TailZ72.
- **R11 docstring** in `PanBergerFontaine.lean`: "whose Théorème 0.7 is the same theorem" now reads "whose Théorème 0.6
  (= Théorème 5.19 of arXiv:math/0102179v3) is the same theorem (Théorème 0.7 there is Sen's theorem)". The same fix
  is in the new field's docstring in TailZ77.
- **B1:** the B1 sketch is not folded.

## 2. Provenance of every new statement

| statement | where it comes from | on-the-spot? |
| --- | --- | --- |
| `OpenResearchLeaves49` (fold 1) | the old bundle minus `chevalleyPerfect`; no new Prop | — |
| `ZInQ.SemistabAssembly.BostLowerBoundAnSS` | cited print: Bost, Sém. Bourbaki 795, Astérisque 237 (1996), display UNVERIFIED; the old row with semistability as printed (SGA 7 IX, geometric and k(𝔭) readings) | no |
| `ZInQ.SemistabAssembly.GaudronRemondThm14AnSS` | cited print: Gaudron–Rémond, Duke Math. J. 163 (2014) Thm 1.4; same change | no |
| `HDec.PkgI4.PanDict.PanPrintedF` | cited print: Pan, arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1. This is the manuscript's own citation: bibitem pan2022, diophantine_zq.tex l. 11041-11045 (VERIFIED) | no |
| `HDec.PkgI4.PanDict.BergerSurveyF` | cited print: Berger, arXiv:math/0210184v1 IV.5.1, a print of Berger's theorem. The manuscript cites the theorem as berger2002 (l. 739, 11037) | no |

No statement is on-the-spot. None of the four leaves appears as a Lean-level statement in diophantine_zq.tex; the
manuscript cites each result.

## 3. Checks (VERIFIED, after each fold; outputs in scratch/fold-b105/)

- **Build:** `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` plus the new TailZ module and the
  Contrib module succeeds (16217, 16219 and 16221 jobs).
- **Axioms:** `#print axioms` of `frozenTarget` and of each new top theorem is `[propext, Classical.choice,
  Quot.sound]`.
- **Hash guard** (`cmp_fold{1,2,3}.txt`): the base dump was taken against the base oleans. Each fold adds 36 constants,
  all in its own TailZ module, and changes only `ZInQ.OneProof.frozenTarget`. Totals: 17984 → 18020 → 18056 → 18092.
- **Closure** (`FoldCheck-fold{1,2,3}.txt`): no `sorryAx`. None of `ChevalleyPerfect`, `PanPrintedP`,
  `BergerPrintedVT` or `BergerPrintedV` appears in the closure of `frozenTarget`. In open-statements.json the old fields
  are gone and the new leaves are present.
- **Other checks:**
  - OpenStatements: 35.
  - render_open and `--check` pass.
  - DischargesTest was rerun.
  - frontier_crosswalk and `--check` pass.
  - autoform check exits 0: 776 articles, 701 fully proved.
- **Replay:** see `scratch/fold-b105/REPLAY.md`. A text-only test ran the three scripts on the base after a fake
  autofold, and they composed through correctly.

## 4. Findings for the lead

1. **Berger numbering.** The lead's correction is applied: Inventiones Théorème 0.6 = Théorème 5.19 of arXiv v3, and
   0.7 is Sen's theorem. However, the retired audit row of `bergerPrintedV` (docs/one-proof/reviews-retired.tsv)
   records "Théorème 0.7 = Corollaire 5.22" for the Inventiones author copy. The two readings disagree. I could not
   check either, since I have no network (UNVERIFIED).
2. **semistab-assembly kind.** The branch rated its two leaves `consequence`, because R3' (étale coordinates are
   holomorphic charts) is still a step inside `IsAnMetricSq`. Under the lead's ruling they are now `published`, kept
   GLUE by "pending review". A reviewer should decide whether R3' makes them consequences.
3. **Flag class.** Gaudron–Rémond's flag_class is set to `pending-review`, because its flag has no UNVERIFIED locator.
   Bost keeps `unverified-locator`.
