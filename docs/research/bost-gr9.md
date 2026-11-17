# bost-gr9: the lower bound for the stable Faltings height, rerouted to Gaudron–Rémond §9

Task bost-gr9, 2026-11-17. Base d67ea55f6 (wip/leaf-fold33b; origin/main an ancestor). Model work only, no human
review. No network: the sandbox refused both the author copy of the paper and arXiv (VERIFIED), so this task did
not read GR14 itself. Theorem numbers recalled from memory are marked UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, exact reference), **SPECULATIVE**,
**UNVERIFIED**. AUDIT-READ means read in the print by the locator audit (docs/research/locators.md row R21), not by
this task.

## 1. Result

**The consumer's current field `bostLowerBoundAn` cannot be proved from the source the manuscript cites. It is
strictly stronger than that source.** The field says `h_F ≥ −(g/2)·log(2π²) = −1.4913…·g` (Bost, Deligne's
normalization, converted). Gaudron–Rémond §9 records only `h_F ≥ −(3/2)·g`. The gap is a numerical one:
`(1/2)·log(2π²) < 3/2`, proved as `half_log_two_pi_sq_lt`, and `sec9_bound_lt_bost` shows the field's bound is
strictly larger for every `g ≥ 1`. So a GR §9 leaf cannot discharge the field by an autofold.

**What is done instead, all VERIFIED (compiled, standard axioms):**

1. **Leaf.** `ZInQ.BostGR9.GaudronRemondSec9LowerAn`, the GR §9 bound in printed form. It is stated over
   `ZInQ.R3Residual.IsAnStableHeight`, the object `GaudronRemondThm14An` uses, so the two GR leaves share their
   definitions.
2. **The consumer's real need, R21, proved from the new leaf.** R21 is `ZInQ.DefFaltings.R21_Bost`,
   `−(3/2)g ≤ h_F^st(A)`, the row the manuscript's E4 uses. It is proved through the same transports the old
   route used (§4).
3. **Normalization change, proved (§2).** Deligne `h_D = h_F + (g/2) log π`, at the level of the height formula.
4. **The new leaf is never stronger than the old row:** `gaudronRemondSec9LowerAn_of_bostLowerBoundAn`.
5. **Fold dry run** by a weaker-leaf bypass (§5). The 110 declarations of the live path that carry the field are
   copied into `HDec.HSyn.GR9`, with the field weakened. `HDec.HSyn.sixContactMin_of_open67_gr9` proves
   `ZInQ.SixContactMin` from the top bundle with `gaudronRemondSec9LowerAn` in place of `bostLowerBoundAn`, the
   other bundles unchanged. Only standard axioms (`scratch/bost-gr9/GR9Bypass.lean`, 7 s).

**Count.** In the dry run the field `bostLowerBoundAn` (GLUE/GLUE, reviewer verdict queue13-15) is replaced by one
new published leaf. Its rating:
- It enters flagged, so it counts GLUE until a reader checks it against p. 2098 (ruling 2026-11-17).
- It is also GLUE as long as the R3′ ruling stands, for the same reason as `gaudronRemondThm14An` (see §3).

So the count is neutral now. It becomes −1 GLUE once p. 2098 is checked and R3′ is resolved (jp-an-retype).

**Dependence on the analytic-structure predicate (coordination with jp-an-retype).** The leaf **depends on
`IsHolChart`**:
- `IsAnStableHeight` → `IsAnMetricSq` → `IsAnFormMeasure` → `HasAnFormDensityAt` → `IsHolChart`.
- This file does not edit that predicate. It uses `IsAnStableHeight` only through its name and through
  `isAnStableHeight_iff`.
- If jp-an-retype retypes `IsHolChart`, the leaf follows automatically, provided `isAnStableHeight_iff` keeps its
  statement.

## 2. The source and its exact statement

**Title and bibliography (VERIFIED in the tree).** Manuscript bibitem `gr2014`, `diophantine_zq.tex` L11063-11066:
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057-2108, "Theorem 1.4 and
Section 9". The locator audit (row R19) read the author's typeset journal copy (lmbp.uca.fr/~gaudron/art13.pdf)
with the same title. No arXiv version was compared (audit: UNVERIFIED).

**The manuscript's use (VERIFIED, read on the base).** At L894-895, step E4 (`\cite[Section 9]{gr2014}`), the
manuscript records the general lower bound `h_F(Z) ≥ −(3/2) dim Z ≥ −2g` and says it is recorded in GR14 §9. It is
used with additivity and Faltings' height variation (L896-899) to bound `h_F(A)`.

**What GR14 §9 prints (AUDIT-READ; not re-read here).** Locators row R21:
- In the proof of Lemme 9.1, p. 2098, GR use `h(A) ≥ −(3/2)·dim A`.
- They refer it to Bost and to their earlier paper (Comment. Math. Helv. 89 (2014), Cor. 8.4).
- They "warn about normalization". The audit did not record the content of the warning.

height-split §2 adds that this is "an inequality inside a proof, not a numbered statement".

**Normalization.** GR14 work with the stable Faltings height in Faltings' original normalization: the audit's
reading of Thm 1.4 (row R19, "stable original-Faltings normalization"), and the manuscript L876-877. The leaf is
stated in that normalization. See Known issue K3.

**Hypotheses.** Any abelian variety over a number field. No polarization, simplicity or semistability hypothesis
(AUDIT-READ for Thm 1.4's setting; for §9 the audit records none). The leaf quantifies over every number field `K`
and every `A/K` with `A.dim = g`. That is the printed generality or a specialization of it (GR state results over
number fields; the stable height does not depend on the field).

## 3. The leaf and its rating

```lean
def GaudronRemondSec9LowerAn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, ZInQ.R3Residual.IsAnStableHeight A x → -(3 / 2) * (g : ℝ) ≤ x
```

| new leaf | replaces | rating | reason |
| --- | --- | --- | --- |
| `ZInQ.BostGR9.GaudronRemondSec9LowerAn` | `bostLowerBoundAn` (in the dry run; strictly weaker) | **printed form**, flagged | Exactly GR14 p. 2098's inequality, `h(A) ≥ −(3/2) dim A`, in GR's (original Faltings) normalization. It is over the stable height built as the print builds it: Néron model over a field of semistable reduction, metric `(i/2)^g ∫ η∧η̄` integrated over `A_τ(ℂ)^an`. Flags: (a) the page was AUDIT-READ, but no statement check against the page is recorded; (b) the normalization warning on that page is unread (K3); (c) the reading R3′ inside `IsHolChart`, as for `gaudronRemondThm14An` |

**Shared definitions with `GaudronRemondThm14An`: yes.** Both are stated over `ZInQ.R3Residual.IsAnStableHeight`,
with the same binder shape `(K) (A) (g) (A.dim = g) (x) (IsAnStableHeight A x)`.

**Not stronger than the print.** Lean cannot prove that a Lean statement is no stronger than a printed one. Two
facts bear on it:
- the leaf is the printed inequality over the printed object;
- it is implied by the tree's previous row (`gaudronRemondSec9LowerAn_of_bostLowerBoundAn`), so adopting it never
  strengthens the hypothesis set.

## 4. Lean: `ZInQKernel/Contrib/OneProof/GaudronRemondSection9.lean` (namespace `ZInQ.BostGR9`)

It imports `ZInQKernel.Contrib.OneProof.AnalyticStableHeight`, which defines `IsAnStableHeight` and
`BostLowerBoundAn`, and `ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect`. It does not import
`OneProof.Main`. No `sorry`, no `axiom`, no code that runs at build time. It compiles in 7.5 s against the built
tree (VERIFIED). `scratch/bost-gr9/axioms.txt`: `r21_of_sec9An`,
`gaudronRemondSec9LowerAn_of_bostLowerBoundAn`, `bostAn_iff_faltings`, `deligne_heightFormula_shift`,
`sec9_bound_lt_bost`, `sec9An_of_printed` depend on `[propext, Classical.choice, Quot.sound]` (VERIFIED).

| declaration | statement | role |
| --- | --- | --- |
| `GaudronRemondSec9LowerAn` | the leaf (§3) | LEAF (printed form, flagged) |
| `GaudronRemondSec9LowerPrinted` | the same over height-fix's `IsPrintedStableHeight` | intermediate |
| `deligne_heightFormula_shift` | `(log s − ½Σ_τ log(r_τ/π^g))/[L:ℚ] = (log s − ½Σ_τ log r_τ)/[L:ℚ] + (g/2) log π` for `r_τ > 0` (Deligne's metric is `π^{−g}` times Faltings') | normalization, proved |
| `deligne_bound_iff` | `−(g/2) log 2π ≤ x + (g/2) log π ↔ −(g/2) log(2π²) ≤ x` | normalization, proved |
| `bostAn_iff_faltings` | `BostLowerBoundAn ↔ BostLowerBoundAnFaltings` (the old row in Faltings' normalization) | proved |
| `half_log_two_pi_sq_lt`, `sec9_bound_lt_bost` | `½ log(2π²) < 3/2`; `−(3/2)g < −(g/2) log(2π²)` for `g ≥ 1` | the old row is strictly stronger |
| `gaudronRemondSec9LowerAn_of_bostLowerBoundAn` | old row ⇒ new leaf | never stronger |
| `sec9Printed_of_an'`, `sec9Printed_of_an` | leaf ⇒ printed-height form (T35: `uniformizationLeafAll`, `mumfordTorsionAlgClosed`; `isAnStableHeight_iff`) | glue, proved |
| `sec9An_of_printed` | converse (given T35) | equivalence |
| `grBostBound_of_sec9Printed`, `…_chevalley` | ⇒ `ZInQ.HeightSplit.GRBostBound` (kernel height; `isPrintedStableHeight_of`, descent glue or `ChevalleyPerfect`) | glue, proved |
| `r21_of_grBost`, `r21_of_grBost'` | `GRBostBound` + N1, SS1, SS2, AN3U ⇒ `R21_Bost` | glue, proved (copy of `r21_of_leaves` without the constant step) |
| `r21_of_sec9An` | leaf + the bundle chain's inputs ⇒ `R21_Bost` | end to end |

`ZInQ.HeightSplit.GRBostBound` (TailY, docstring "The form printed by Gaudron–Rémond … §9") already existed. Until
now it was used only as an intermediate (`grBostBound_of_bost`).

## 5. Fold dry run: weaker-leaf bypass (VERIFIED)

The autofold mechanism needs a proof of the discharged field from the new leaves. That is impossible here (§1), so
the dry run uses the bypass recipe of raynaud-narrow and sga33-shpre.

**Closure.** `scratch/bost-gr9/Closure.lean` is a metaprogram that imports `TailZ74`. It finds the bundle
structures carrying the field in any of its three forms (`BostLowerBoundAn`, `BostLowerBoundPrinted`,
`HeightSplit.BostLowerBound`): 114 in the environment. It then collects every declaration reachable from
`sixContactMin_of_open67` whose type mentions one of them.
- Result: **110 declarations, all in `TailZ74`, `TailZ69`, `EichlerBoundCopy`**, listed in `closure.tsv` with their
  ranges.
- They are: the research bundles `OpenResearchLeaves8EB`–`48` (CF and GMEB variants), their conversions, the height
  rows consumer `heightRowsNo20_of8_hf_eb`, the `sixContactMin_of_open*` chain and 10 helpers.

**Copy.** `scratch/bost-gr9/gen_bypass.py` copies each declaration verbatim into `HDec.HSyn.GR9`, with its
original `namespace`/`open`/`set_option` context. The only edits:
- **Field types weakened:**
  - `BostLowerBoundAn` → `GaudronRemondSec9LowerAn`;
  - `BostLowerBoundPrinted` → `GaudronRemondSec9LowerPrinted`;
  - `HeightSplit.BostLowerBound` → `HeightSplit.GRBostBound`.
- **Top bundle field renamed:** `gaudronRemondSec9LowerAn`, with a new doc comment.
- **Three conversions replaced by their GR §9 analogues, with the same argument shapes:**
  - `bostLowerBoundPrinted_of_an` (TailZ74:990) → `sec9Printed_of_an`;
  - `bostLowerBound_of_printed_chevalley` (TailZ74:465) → `grBostBound_of_sec9Printed_chevalley`;
  - `r21_of_leaves'` (EichlerBoundCopy:482) → `r21_of_grBost'`.
- **One SGRFold sibling** (`added12_of_open29_hf_pz`) qualified with `_root_`, because it is not on the resolution
  path from `HSyn.GR9.SGRFold`.

**Checks (in `GR9Bypass-compile.txt`):**
- `lake env lean scratch/bost-gr9/GR9Bypass.lean` (4037 lines): no error.
- `'HDec.HSyn.sixContactMin_of_open67_gr9' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- The field check in the same file prints: `original fields: 29, copy fields: 29`, `only in original:
  [bostLowerBoundAn]; only in copy: [gaudronRemondSec9LowerAn]`, and no other field type differs.

**For the integrator.** Folding this is a bypass module, not an autofold: the generated `GR9Bypass.lean` without
the scratch `run_cmd` check, as `TailZ75`, with `frozenTarget` switched to `HDec.HSyn.sixContactMin_of_open67_gr9`
(or the bypass's names promoted).
- `scratch/bost-gr9/autofold.json` records the leaf row (kind, flag, source) in autofold's format, with
  `"mode": "bypass"` and the reason. Its `discharges[0].proof` names the bypass top theorem rather than a proof of
  the field, so `autofold.py` must not be run on it as is.
- Hash guard: the bypass adds constants under `HDec.HSyn.GR9` and changes none (no existing module edited).

## 6. Known issues

**K1. The tree's row is stronger than the manuscript's citation.** `bostLowerBoundAn` asserts Bost's bound,
`h_D ≥ −(g/2) log 2π`, equivalently `h_F ≥ −(g/2) log(2π²)`. Its record:
- Bost is not cited by the manuscript.
- Bost's display is unread (locators R21, "UNVERIFIED from Bost").
- GR14 §9 records only `−(3/2)·dim`.

The manuscript needs only `−(3/2)·dim` (L894). The corrected field is `GaudronRemondSec9LowerAn`, which is all R21
and E4 use. This is a case of "a consequence of the leaf is stronger than the print": the old row was not false,
but it was not the cited source. A second print that would give the old row exactly is GR CMH 2014 Cor. 8.4
(`h_F ≥ −log(π√2)·dim`, read only by upstream's V16 reviewer, a model; up-h §3). Per the rules this task does not
use it: the manuscript cites GR14 §9.

**K2. GR14 §9 records the bound; it does not prove it.**
- The inequality appears inside the proof of Lemme 9.1 (p. 2098), with references to Bost and to GR CMH 2014
  Cor. 8.4 (AUDIT-READ).
- The manuscript's wording, "recorded in", is accurate, so the locator is not wrong.
- But the leaf is a published, refereed statement whose proof is elsewhere (Bost, Sém. Bourbaki 795, Astérisque 237
  (1996), display unread).

A reviewer may want the leaf flagged "cited statement inside a proof".

**K3. Normalization of the §9 inequality not confirmed on the page.** The leaf reads `−(3/2) dim A` in Faltings'
original normalization:
- This is GR14's normalization for Thm 1.4 (AUDIT-READ) and the manuscript's (L876-877).
- But the audit notes that GR "warn about normalization" at p. 2098, and the content of that warning was not
  recorded. This task could not fetch the page.

This matters for the route:
- Read in Deligne's normalization, the inequality would give only `h_F ≥ −(3/2 + ½ log π) dim ≈ −2.07·dim`. That
  is not R21's `−(3/2)·g`.
- It would not always give the manuscript's `≥ −2g` either. With `dim Z = g − 2`, that needs `g ≤ 57`.

The Faltings reading is true (it follows from the old row, `gaudronRemondSec9LowerAn_of_bostLowerBoundAn`, and from
Bost's bound as converted in locators §2). But whether it is the print's reading is open. **Action:** read p. 2098
and record the warning before the leaf's flag is cleared.

**K4. GR14 not read by this task.** The network is blocked (VERIFIED: WebFetch refused `lmbp.uca.fr` and
`arxiv.org`). Everything about §9's content is AUDIT-READ from locators.md row R21 and height-split §2.

## 7. Files

- `ZInQKernel/Contrib/OneProof/GaudronRemondSection9.lean` (new; the only file under `ZInQKernel/` touched).
- `scratch/bost-gr9/`:
  - `log.md`;
  - `Closure.lean`, `closure.tsv`;
  - `gen_bypass.py`, `GR9Bypass.lean`, `GR9Bypass-compile.txt`;
  - `Discharges.lean`, `discharges.txt`;
  - `autofold.json`;
  - build logs.

## 8. `#discharges` (VERIFIED)

- Build: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.GaudronRemondSection9` succeeded (16216 jobs; `frozenTarget` standard axioms).
- Run: `lake env lean scratch/bost-gr9/Discharges.lean`, output in `scratch/bost-gr9/discharges.txt`. It lists
  19 discharges, all by declarations already in the tree, and **none by `ZInQ.BostGR9`**.
- This is expected. No theorem in the new file has the type of an open field, because the only candidate,
  `BostLowerBoundAn`, is strictly stronger than the leaf (§1).
- The fold check is the bypass (§5) instead.

## 9. What remains

- **Reading.** Read GR14 p. 2098: the inequality's normalization and the warning (K3). Add a statement-check row
  for `GaudronRemondSec9LowerAn` to locators.md and STATEMENT-CHECKS.md (this task edits no shared docs).
- **Integration.** Promote the bypass to a TailZ module with `frozenTarget` switched (§5), or reroute by
  sem-prune's weaker-hypothesis threading.
- **The other two `IsAnStableHeight` leaves** (`gaudronRemondThm14An`, `javanpeykarThm111`) are untouched.
