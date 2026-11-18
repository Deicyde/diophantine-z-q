# cm-fold-rebase: the CM-branch fold on main's current top, with its exact count

Task cm-fold-rebase (2026-11-17). Base: `origin/wip/cox-lattice` 6298e108 (cm-branch2's final fold 75e3c1d8 and
cox-lattice's proof). `origin/main` 67950e829 (fold-b112 and the hygiene commit; top `HDec.HSyn.sixContactMin_of_open76`,
TailZ83) merged with a merge commit (d28bdc4e, clean, no rebase). Results log: `scratch/cm-fold-rebase/log.md`. Marks:
VERIFIED (compiled, or read in the tree or in diophantine_zq.tex), STANDARD (published, exact reference), UNVERIFIED
(theorem numbers from memory; this host has no network), SPECULATIVE.

## 1. Result

**The CM-branch fold is regenerated and compiles on main's current top.** VERIFIED (`lake build`, EXIT 0; `#print axioms`
= `propext, Classical.choice, Quot.sound`):

```lean
structure HDec.HSyn.OpenResearchLeaves58CM : Prop   -- OpenResearchLeaves57 − gonzalezRotgerThm512X6RCF + 5 CM fields
theorem HDec.HSyn.sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) : ZInQ.SixContactMin
theorem HDec.HSyn.sixContactMin_of_open76_cmfold (r : OpenResearchLeaves57) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin
```

and the `frozenTarget` dry run (`scratch/cm-fold-rebase/MainDryRun.lean`: `ZInQKernel/OneProof/Main.lean` of main with
only the research bundle switched to `OpenResearchLeaves58CM` and the H argument to `sixContactMin_of_open77_cm r t l`)
compiles: `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.

The new top replaces `gonzalezRotgerThm512X6RCF` by the CM-branch inputs: `cmFibreSplit` (GLUE) and cm-branch's leaves
`fowlerProp27` (printed form), `cmjDegree`, `cmPotentialGood`, `cmHeight62` (consequence form), all pending review.
`CoxProperLattice` is proved (`CMBranch.coxProperLattice_proof`; cox-lattice's `CMBranch.CoxLattice.coxProperLattice_proof`
also works), and so are `HeightAdditivityUpper` and `ReducedCMPeriod`. On main, `OpenTextbookLeaves18` has no fields,
so the textbook statements these proofs use (`t35`, `homLatticeCorr`, `t11b`) are themselves proved by contributions.
`ReducedCMPeriod` (manuscript L598-599) is therefore fully proved on main's tree.

**Count (main's rule: kinds.tsv, H rows, every new leaf pending review counts as GLUE):**

| | H rows | strict LEAF / GLUE | strictest |
|---|---|---|---|
| before (main 67950e829, docs/one-proof/OPEN.md and kinds.tsv) | 29 (research 27, added 2, textbook 0) | **strict 5 LEAF / 24 GLUE on 29** | 5 / 24 |
| after (this fold) | 33 (research 31, added 2) | **strict 5 LEAF / 28 GLUE on 33** | 5 / 28 |
| after, if `fowlerProp27` is rated LEAF by a reviewer | 33 | **strict 6 LEAF / 27 GLUE on 33** | 6 / 27 |

Net change: −1 GLUE (`gonzalezRotgerThm512X6RCF`, consequence GLUE/GLUE), +1 GLUE (`cmFibreSplit`), and +4 leaves that
count as GLUE while pending review, so **+4 GLUE, LEAF unchanged**. If Fowler is rated LEAF: +3 GLUE, +1 LEAF. The other
three new leaves are in consequence form (kinds.tsv kind `consequence`), so under the kit's definition (LEAF = printed form
or a direct instance) they stay GLUE after review unless they are restated in printed form. Every new row sits in the
**research bundle** (`OpenResearchLeaves58CM`); the textbook and added bundles are unchanged. The five LEAF rows before and
after are `deRhamVpAbVarDirect`, `dsThm966Printed`, `r9a`, `r9b`, `silverbergZarhinThm35`. Since the fold raises the
strict GLUE count, `autofold.py` would refuse it without `--allow-rise`. The trade the integrator would accept is
González–Rotger's Thm 5.12, in a consequence form that is still pending its own reading, swapped for the manuscript's own CM
route (L581-605).

## 2. Why the fold had to be regenerated (not just rebased)

Main's TailZ80 (bost-gr9, fold-b112) is a copy-based reroute. The research bundles `OpenResearchLeaves53` … `8EB`, their
conversions, the height-row consumer and the chain `sixContactMin_of_open8` … `open72` are copied into `HDec.HSyn.GR9`
with `bostLowerBoundAnSS` replaced by the strictly weaker `gaudronRemondSec9LowerAnSS`, and `sixContactMin_of_open73 :=
GR9.sixContactMin_of_open72`. VERIFIED (TailZ80 L1-17, L3034-3054). cm-branch2's route (`CMBranch/R5Prune*.lean`,
`Open73.lean`) runs over the un-copied bundles, which need `bostLowerBoundAnSS`. So it cannot be fed from
`OpenResearchLeaves57`, and the CM-branch transformations had to be applied to the GR9 chain.

## 3. Construction (all generated; generators in `scratch/cm-fold-rebase/gen/`)

| step | file | content |
|---|---|---|
| 1 | `CMFoldRebase/Top3.lean` (`mk_top3.py`) | the 27 theorems `GR9.sixContactMin_of_open48_eb_k954` … `GR9.sixContactMin_of_open8_hf_pz_eb` copied verbatim in their namespace and context, with `c : CMBranch.CMInputs2` threaded and the callee renamed `…_cm2 (c := c)`. The bottom callee is cm-branch2's `HSyn.sixContactMin_of_open7_hf_pz_eb_cm2` (`CMBranch/Top2.lean`), whose base is the manuscript's CM branch (cm-branch's `sixContactMin_of_open4_cm`) |
| 2 | `scratch/cm-fold-rebase/Dirty3.lean` → `dirty3.tsv` | cm-branch2's dirty scan (constants of the closure whose type or value mentions `LeafQM.AV.R5ptProps`, to a fixpoint), rooted at `GR9.sixContactMin_of_open48_eb_k954_cm2` and the GR9 conversions 35→34→33→32→31: 954 dirty of 65663 |
| 3 | `CMFoldRebase/R5GR9_1.lean`, `R5GR9.lean` (`gen_r5b.py`) | the weak-row bypass (`R5ptProps` carried as `True`) for the dirty constants cm-branch2 had not copied: 191 copies needed, 107 reused from cm-branch2's `R5Prune*.lean` (same `_r5` names), 84 new (TailZ80's GR9 bundles, conversions, height-row consumer, and the Top3 chain). cm-branch2's renamer is made namespace-aware: a reference resolves as Lean resolves it, innermost namespace first, because the GR9 copies share last names with the originals. cm-branch2's three applicable patches each applied once, including the GR9 producer of `gonzalezRotgerX6Ab`, now filled from `x6CoarseModuli` and `shimuraMainThmIDeligneY3AbU` without González–Rotger |
| 4 | `CMFoldRebase/Open77.lean` (`gen_open77.py`) | `OpenResearchLeaves58CM`; `OpenResearchLeaves56_cm`, `55_cm`, `54_cm`, `GR9.OpenResearchLeaves36EBCF_cm`, `GR9.OpenResearchLeaves35EBCF_cm` (the bundles that carry the field, without it); conversions verbatim with the field's line dropped; the last one is the weak conversion 35_cm → `GR9.OpenResearchLeaves34EBCF_r5`; top `sixContactMin_of_open77_cm` |
| 5 | `ZInQKernel/Contrib/OneProof/CMFoldRebase.lean` | deliverable: `sixContactMin_of_open76_cmfold` (main's top bundles plus `c : CMInputs3`; `{ r with … }`) |

Sizes: R5GR9_1 140 KB, R5GR9 105 KB, Open77 110 KB, Top3 24 KB (each under the kit's 150 KB guideline).

## 4. Checks (VERIFIED)

* `lake build ZInQKernel.Contrib.OneProof.CMFoldRebase` (with `CMFoldRebase.Open77`, `R5GR9`, `Top3`): EXIT 0, 15411 jobs,
  first try (`scratch/cm-fold-rebase/build2.log`). `#print axioms` for `sixContactMin_of_open77_cm` and
  `sixContactMin_of_open76_cmfold`: `[propext, Classical.choice, Quot.sound]`.
* `frozenTarget` dry run: `scratch/cm-fold-rebase/MainDryRun.lean`, `lake env lean` EXIT 0, standard axioms
  (`maindryrun-out.txt`).
* Closure scan `scratch/cm-fold-rebase/GRUse77.lean` (`gruse77-out.txt`; closure of `sixContactMin_of_open77_cm`, 130504
  constants). The following are absent: `LeafQM.AV.R5ptProps`, `GRDict.r5ptProps_of_thm512`, `GRX6AbPrint.gonzalezRotgerX6Ab_of_print`,
  `GRDict.GonzalezRotgerThm512X6`, `GR512Bridge.GonzalezRotgerThm512X6RCF`, `GR512Bridge.gonzalezRotgerThm512X6_of_rcf`,
  the GR9 bundles' `gonzalezRotgerThm512X6` projections, `OpenResearchLeaves53/54/57`, the old NoCM base
  `sixContactMin_of_open4_hf_pz_eb` and `FS5NoCM.R1R2fpFullProps`. Present: the five CM statements,
  `CoxProperLattice` with `coxProperLattice_proof`, `HeightAdditivityUpper`, `ReducedCMPeriod`, and
  `GaudronRemondSec9LowerAnSS` (so bost-gr9's replacement is kept). **All 31 fields of `OpenResearchLeaves58CM` are read**
  (each projection occurs in the closure; a syntactic read).
* `#discharges` (`scratch/cm-fold-rebase/Discharges.lean`, output `discharges.txt`): "30 open hypotheses, 13341 theorems
  checked, 315 discharge one". Of these, 15 are pre-existing reductions on main: carayol, ds965, deRham ×2, javanpeykar,
  the two `X₆` rows, deligne, GR §9 from Bost, pazuki ×4, hodgeTate ×2. The other 300 are projections `X_r5.<field>` and
  `X_cm.<field>` of copied bundle structures, the known noise for copied structures (cm-branch2 §7.1). No theorem of this
  task discharges a top field, as expected: the removed field is unread on the new route, not proved, so the gain shows
  in the hand fold and not in `#discharges`.
* No existing file under `ZInQKernel/` is modified (`git diff --diff-filter=MD origin/main -- ZInQKernel` is empty).
  Every existing constant is unchanged; only new modules are added under `ZInQKernel/Contrib/OneProof/CMFoldRebase*`.

## 5. Spec and kinds rows

* `scratch/cm-fold-rebase/autofold.json`: a hand fold in cm-branch2's format (`replaces`). Replace
  `HDec.HSyn.sixContactMin_of_open76 r t l` by `HDec.HSyn.sixContactMin_of_open77_cm r t l`, and the bundle
  `OpenResearchLeaves57` by `OpenResearchLeaves58CM`. Import `ZInQKernel.Contrib.OneProof.CMFoldRebase.Open77`. Remove
  `gonzalezRotgerThm512X6RCF`. The new leaves have kind and flag; `cmFibreSplit` is glue. The mechanical `discharges`
  format does not apply, because the removed field is unread rather than proved.
* `scratch/cm-fold-rebase/kinds-rows.tsv` (main's 13 columns; to add to `docs/one-proof/kinds.tsv`, and remove the row
  `research/gonzalezRotgerThm512X6RCF`):

| bundle | field | kind | flag (provenance) | strict / strictest | flag_class |
|---|---|---|---|---|---|
| research | `fowlerProp27` | published | CITED, `\cite[Proposition 2.7]{fowler}`, ms L588-590; printed form over orders through `h(Δ) = #Pic(O_Δ)`, `Δ = f²d_k`; print read by the upstream audit; pending review | GLUE / GLUE | pending-review |
| research | `cmHeight62` | consequence | CITED-consequence, `\cite[Eq. (6.2)]{cmheight}`, ms L605 (normalization L598-605); good-reduction case, `≤` half; pending review | GLUE / GLUE | pending-review |
| research | `cmjDegree` | consequence | ELLIOT-literature, ms L586-587 (uncited); `#Pic(R) ≤ [L:ℚ]`; locator UNVERIFIED; pending review | GLUE / GLUE | pending-review |
| research | `cmPotentialGood` | consequence | ELLIOT-literature, ms L596-597 (uncited; reason given there: `j` integral); locators UNVERIFIED; pending review | GLUE / GLUE | pending-review |
| research | `cmFibreSplit` | glue | GLUE, ms L581-586 (CM fibers: matrix units, `E/L` with CM, `L`-isogeny `E² → A`) with A8 at a CM fibre (L520-562) | GLUE / GLUE | note |

The `area_issue` column is `elliotglazer/diophantine-z-q#86`, the issue of the removed row, as autofold does.

## 6. Rating of the new leaves (printed form or not)

Locators VERIFIED against diophantine_zq.tex (read L578-610): "CM fibers" L581-585, "The degree of `j(E)` is its order
class number" L586-587, `\cite[Proposition 2.7]{fowler}` with the bound `√|Δ| ≤ 2D² exp(21000D²)` L588-590, "After a finite
extension `E` has everywhere good reduction, since its `j`-invariant is integral" L596-597, `\cite[Eq. (6.2)]{cmheight}` L605.

| leaf | printed form? | reason |
|---|---|---|
| `FowlerProp27` | **yes** | Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026), Prop. 2.7, as the manuscript cites it. It is stated over orders through `h(Δ) = #Pic(R)`, `Δ = f²d_k`, with no exceptional field. The print was read by the upstream audit, not re-read on this host. It is the one new row that can become LEAF on review |
| `CMHeight62` | no (consequence) | Barquero-Sanchez et al., Res. Number Theory 3 (2017), Eq. (6.2): the good-reduction case and the `≤` half, with the stable height over `L₁` bounding that of `E`. The exact display of (6.2) is unread on this host |
| `CMjDegree` | no (consequence) | `[ℚ(j(E)):ℚ] = h(R)` weakened to `#Pic(R) ≤ [L:ℚ]`. The manuscript does not cite it (ELLIOT-literature) |
| `CMPotentialGood` | no (consequence; uncited) | CM ⇒ potentially good reduction. The manuscript gives integrality of `j` as the reason, and cites no source |

## 7. Labels, on-the-spot steps, Known issues

* **On-the-spot**: none new. The regeneration is mechanical: verbatim copies, the weak row `R5ptProps := True`, and the
  field line dropped. cm-branch2's on-the-spot steps (L598-599 reduced period, L620-621 additivity) are proved in Lean, as
  is Cox's lemma (cox-lattice).
* **ELLIOT-literature**: `CMjDegree` (L586-587) and `CMPotentialGood` (L596-597): classical facts the manuscript uses
  without citation.
* **Known issues** (inherited, unchanged; not papered over):
  1. `CMFibreSplit` needs A8 at a CM fibre without NoCM (cm-branch Known issue 2; cm-branch2 §2.3). The chain's A8 runs
     through `ConjMapsNoCM`; the manuscript's own A8 (Weil restriction, kernel field of the Galois action on the
     endomorphism lattice, L546-555) needs no rigidity, but it is not formalized. The row is open GLUE.
  2. Two of the four new leaves are uncited in the manuscript (ELLIOT-literature). Their classical sources (Cox Thm 11.1;
     Serre–Tate 1968) are UNVERIFIED locators, not in the manuscript's bibliography.
  3. Fowler Prop. 2.7 and (6.2) of [cmheight] were read only by the upstream audit, so all four leaves stay pending review.
* No Gross–Zagier or Tian–Yuan–Zhang argument is used. No consumer's statement is changed. The `_r5` and `_cm` copies are
  new constants with weakened statements: `R5ptProps` replaced by `True`, or the unread field dropped. Each is implied by
  its original.

## 8. What remains

* The integrator's fold: switch `Main.lean` as in `MainDryRun.lean`, apply the kinds rows (with `--allow-rise` or by
  hand), and regenerate OPEN.md.
* `cmFibreSplit`: open GLUE (task cm-fibre-split is working on it in parallel).
* Reviews of the four leaves. Only `fowlerProp27` can become LEAF in its current form.
