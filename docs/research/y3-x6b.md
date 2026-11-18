# y3-x6b: the moduli row over `Y₃` on the current CM fold (both `X₆` rows dropped)

Task y3-x6b, 2026-11-17. It ports y3-x6 (origin/wip/y3-x6 e9c0d2dd7, docs/research/y3-x6.md) onto cm-fold-rebase's CM fold.
Branch wip/y3-x6b is origin/wip/cm-fold-rebase 664e00417 (the CM fold on fork main 67950e829) merged with origin/wip/y3-p1j
d1eb63916. Base route: `HDec.HSyn.sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) t l` (CMFoldRebase/Open77.lean).
Lean: `ZInQKernel/Contrib/OneProof/Y3X6/` (`Row.lean` is y3-x6's, hand-written; `Copy1-5.lean` and `Top.lean` are generated
by `scratch/y3-x6b/gen/gen_y3b.py` and `gen_top_b.py`), plus the contribution file `ZInQKernel/Contrib/OneProof/Y3X6Fold.lean`.
Results log: `scratch/y3-x6b/log.md`. Marks: VERIFIED, STANDARD, UNVERIFIED, SPECULATIVE, ON THE SPOT, as in y3-x6.

## 0. Verdict

**GLUE count against this base (cm-fold-rebase's fold): change 0 in the strict column and 0 in the strictest.** Under the
kinds.tsv rule (new leaves pending review count as GLUE), H rows go from 5 LEAF / 28 GLUE on 33 to 5 LEAF / 28 GLUE on 33.
* Removed: `x6CoarseModuliIdeal` (GLUE/GLUE) and `elkiesX6StarEveryIdeal` (GLUE/GLUE).
* Added: `y3ToP1j` (y3-p1j's leaf; kind consequence, flag ELLIOT; GLUE until rated) and `heckeSqrtBranchAny` (glue).

So y3-p1j's +1 is back to 0, and the field count is unchanged. VERIFIED: everything compiles with `lake build` on the first
try, the axioms are the standard three, and the closure scan and reader grep were run on this tree. The new top theorem:

```lean
theorem HDec.HSyn.sixContactMin_of_open78_y3x6 (r : OpenResearchLeaves59Y3) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) : ZInQ.SixContactMin
```

`OpenResearchLeaves59Y3` = `OpenResearchLeaves58CM` − `x6CoarseModuliIdeal` − `elkiesX6StarEveryIdeal` + `y3ToP1j` +
`heckeSqrtBranchAny`. That makes 31 fields, as before. The contribution entry point is
`HDec.HSyn.sixContactMin_y3x6b` in `Y3X6Fold.lean`, an alias of the top.

What changed from y3-x6:
1. **The chain is regenerated on this base.** `gen_y3b.py` (y3-x6's `gen_y3.py`, adapted) reads every weak-row copy of the
   CM fold, in import order: cm-branch2's `CMBranch/R5Prune{1,2,3,}.lean` (still the bottom of this fold's chain) and
   cm-fold-rebase's `CMFoldRebase/R5GR9_1.lean`, `R5GR9.lean` (bost-gr9's `HSyn.GR9` copies). It writes 244 `_y3` blocks
   to `Y3X6/Copy1-5.lean`, applying y3-x6's transformations (row → `Y3X6.R1R2fpY3`, the five readers replaced, the X₆
   producers deleted, `X6ConicModel_y3 := True`, the carried fields renamed).
   * New patches: the GR9 copies of the `x6Rows_of_open14` and `openGlue7_of_OpenGlue8` patches.
   * New deletions: `GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb` and the GR9 conversion 35 → 34. The latter is
     unused on the route, because Open77's conversion replaces it.

   `gen_top_b.py` regenerates `Top.lean` from `CMFoldRebase/Open77.lean`:
   * the bundles 58CM, 56, 55, 54 and GR9 36EBCF, 35EBCF are copied (suffix `_y3x6`) without the X₆ fields and with
     `y3ToP1j` and `heckeSqrtBranchAny`;
   * the last conversion fills `GR9.OpenResearchLeaves34EBCF_y3` with `y3row := n.y3ToP1j` and
     `heckeSqrtY3 := n.heckeSqrtBranchAny`.
2. **`Y3X6/Base.lean` is dropped.** On this base `CMBranch/Top2.lean` compiles, because cm-branch d4073125e's
   `CMHomFieldSplit` change is not in this tree. So `Row.lean` imports `CMFoldRebase.Top3` and `Y3ToP1j` directly.
   y3-x6's "Tree issue" does not arise here.
3. **No cm-branch or cm-branch2 content was brought over.** Only y3-x6's own files were checked out (Y3X6/, Y3X6Fold.lean,
   scratch/y3-x6/, its report and note); the CM content is this base's.

`HeckeSqrtBranchAny` stays a GLUE field, statement unchanged (§4). The reason is y3-x6's: the manuscript's tame local
equation (L517-526) is local at p > 324 and gives no global square root.

## 1. Manuscript check (carried over from y3-x6, re-read; unchanged)

One row per manuscript step this task formalizes or relies on (diophantine_zq.tex). The rows L411-440 rely on y3-p1j's
check of the same lines (docs/research/y3-p1j.md §1), re-read here. y3-x6b changes no statement and no mathematical step, so
the table is y3-x6's (§1 of docs/research/y3-x6.md). The computation is `scratch/y3-x6/pullback_check.py` →
`pullback_check.txt` (VERIFIED by y3-x6; inputs and output unchanged in this tree).

| tex lines | step | verdict | reason |
|---|---|---|---|
| L411-418 | `B = (2,−3)`, `𝒪`, `μ = 2j+ij`, Gram matrix of `Trd(μ⁻¹xȳ)`, determinant one | OK | recomputed by y3-p1j with exact rationals (`scratch/y3-p1j/gram.txt`); read again here |
| L420-422 | normalizer quotient `P¹_j`, branch values `0, ∞, −16/27`, indices `4, 6, 2` [BG, LY] | OK with the known caveats | this is the content of the leaf `y3ToP1j` (branch values as biconditional CM clauses); BG Thm 2.1/Lemma 3.1 read by locators.md; indices are orbifold orders (y3-p1j Known issue 1); the `j`-normalization is a Möbius choice. The indices are used only in the ON THE SPOT argument for `heckeSqrtBranchAny` (§4), not in Lean |
| L423-429 | `K₀`, `K₃`, `N` normalizes `K₃`, `\|N/𝔸_f^×K₀\| = 4` | OK | y3-p1j §1 (STANDARD local normalizers); `N/𝔸_f^×K₀ ≅ W` is the group-theoretic source of the character in §4 step 3 |
| L430-434 | central finite ideles act trivially | OK | `z = q·w`, sign of `q` chosen so that `w₃ ≡ 1 mod 3`; then `w ∈ K₃` (read again) |
| L434-440 | `Y₃` (all components) has the action of `N/𝔸_f^×K₃` with quotient `P¹_j`; `deg ≤ 324` | gap filled (implicit standard step, y3-p1j) | relied on through `y3ToP1j`; fibres = twist classes, onto, `≤ 324` (true degree 144, y3-p1j) |
| L481-509 | normalizer action extends to the stable model; tame action at `p > 324`; quotient smooth with three disjoint branch sections; integral model in the `j`-coordinate | unverified (not used) | not formalized; this is the integral-model route that would replace sgr-direct's Lemma NV route (§4). The argument reads as standard (cyclic stabilizers in tame characteristic, Hensel lift of the fixed point) |
| L511-516 | `J(u) = −57600F²/G⁶`; `G⁶ − 97200F² = H²` | OK | exact polynomial identity (VERIFIED, `scratch/y3-x6/pullback_check.txt`); `57600·27/16 = 97200`, so `27G⁶(J + 16/27) = 16H²` |
| L517-518 | pullback orders `2, 6, 2`; after tame normalization `e/gcd(e,a)` = `2, 1, 1` | OK | orders of `J` over `0` (`F²`), `∞` (`G⁶`), `−16/27` (`H²`) are `2, 6, 2`; with `e = 4, 6, 2`: `4/2, 6/6, 2/2` |
| L518-519 | discriminants and resultants have prime support `≤ 13`, so the picture persists at `p > 324` | OK | the six roots of `F`, `G`, and the three quadratic factors of `H` are pairwise coprime away from `{2,3,5,7,11,13}`, discriminants and leading coefficients included (VERIFIED, computed) |
| L519-521 | normalized cover of `P¹_u` has degree `≤ 324` and is branched only at the six contacts | OK | the degree of a pullback is the degree of `Y₃ → P¹_j`, not times `deg J = 12`; only the roots of `F` keep index `2`. `u = ∞` maps to `J(∞) = −57600/7⁶`, which is not a branch value |
| L521-526 | local equation `u − c = z²` after unramified extension; even positive contact valuation unramified; negative valuation goes to the unbranched point at infinity | OK (local statement) | Kummer for `p ∤ 2`; distinct contacts do not meet mod `p > 60`. This is the step the task asked to re-route `HeckeSqrtBranchAny` to: it is local at `p` and gives no global square root (§4), so it is not used in Lean |

**Known issues** (all inherited, nothing new in the manuscript): y3-p1j §6 (indices as orbifold orders; the
`j`-normalization is not in BG Thm 2.1/Lemma 3.1; the bibliography cites the BG preprint; the polarization point from
y3-route-a). New: none.


## 2. The readers and their re-sourcing on this base

Method: the code-line grep `scratch/y3-x6b/grep-x6.txt` over the cm-fold-rebase files and the y3-x6b files, plus the
closure scan (§3). Every reader that y3-x6 re-sourced on cm-branch2's route is in cm-branch2's `R5Prune*` copies. Those
copies are still the bottom of this chain and are handled exactly as in y3-x6 (docs/research/y3-x6.md §2 table):
* `R1R2fp_Y`, `residue_unramified_over_branch`, `exists_fibre_object`, `Pin.cm_objects_of_R1R2fp` and `r1rec_of_rep` →
  `Y3X6/Row.lean`;
* `GapST.cm_pointW` and `descend_main` → patched;
* `pairsLift_of_rep` → `pairsLift_of_t5`;
* `x6ConicModel*` → `True`;
* `SGRDirect.elkies_coordinate` → the glue field.

**Readers that exist on this base and not on cm-branch2's route.** These are bost-gr9's GR9 copies and cm-fold-rebase's
Open77. Every one is re-sourced; none is blocked.

| reader (this base) | X₆ input read | re-sourced to | how |
|---|---|---|---|
| `GR9.openResearchLeaves36EBCF_cm_of_54_cm` (Open77) | `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal` (→ `x6CoarseModuli_of_ideal`, `elkiesX6StarEvery_of_ideal'`) | — | fields dropped in `GR9.OpenResearchLeaves36EBCF_y3x6`; `y3ToP1j`, `heckeSqrtBranchAny` passed down |
| `GR9.openResearchLeaves34_r5_of_35_cm` (Open77) | `x6CoarseModuli` → `gonzalezRotgerX6Ab_r5_of_coarse`; `elkiesX6StarEvery` → `elkiesX6StarFunctionField_of_every` with `x6ModuliWitness_of_coarse` | `Y3ToP1j`; the glue field | `GR9.openResearchLeaves34_y3_of_35_y3x6`: `y3row := n.y3ToP1j`, `heckeSqrtY3 := n.heckeSqrtBranchAny` |
| `GR9.x6Rows_of_open14_hf_gm_pz_eb_r5` (R5GR9) | `gonzalezRotgerX6Ab`, `babaGranathRationalAb`, `elkiesEquationsX6Ab` → `x6Rows_of_leavesW_r5` | `Y3X6.r1r2fpY3_of r.y3row (rayClass)` | patched copy (same patch as the HSyn version) |
| `GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb_r5` (R5GR9) | `elkiesX6StarPrinted` + the row (`SGRDirect.heckeSqrtBranchAny_of_elkies_r5`) | the glue field | deleted; `GR9.openGlue7_of_OpenGlue8_y3` patched to `r.heckeSqrtY3` |
| `GR9.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_r5` (R5GR9_1) | `gonzalezRotgerX6Ab_r5_of_coarse`, `elkiesX6StarFunctionField_of_every` | — | deleted (not on the route: Open77's conversion replaces it) |
| GR9 bundle conversions 14 … 34 (R5GR9*) | carry or convert `gonzalezRotgerX6Ab`, `babaGranathRationalAb`, `elkiesX6StarPrinted` (`elkiesEquationsX6Ab_of_printed`), `elkiesX6StarFunctionField` | `y3row`, `heckeSqrtY3` | generator's field rule (as y3-x6) |
| GR9 bundles `OpenResearchLeaves9EB`, `8EB` field `r1r2 : R1R2fpRepW_r5` | the row | `R1R2fpRepW_y3 := Y3X6.R1R2fpY3` | replacement def (as y3-x6) |

None of the `Y3X6/*` files and neither `Y3X6Fold.lean` mentions an X₆ field or clause name on a code line
(`grep-x6.txt` (b) is empty).

## 3. Checks and deliverables

* **Build** (VERIFIED): `lake build ZInQKernel.Contrib.OneProof.Y3X6Fold` exits 0 (15415 jobs, first try;
  `scratch/y3-x6b/build1.log`). The Copy files are each under 140 KB.
* **Axioms** (VERIFIED, `scratch/y3-x6b/axioms.txt`): `sixContactMin_of_open78_y3x6`, `sixContactMin_y3x6b`, the five
  Row theorems, `r1r2fpY3_of` and `GapST.cm_pointW_y3` depend on `[propext, Classical.choice, Quot.sound]`.
* **Closure scan** (VERIFIED, `scratch/y3-x6b/Closure.lean` → `closure.txt`). The closure of `sixContactMin_of_open78_y3x6`
  has 129961 constants.
  * Not in it: `X6Props`, `R2X6Props`, `CMExists`, `X6Surj`, `R2X6PropsIff`, `R5ptProps`,
    `X6ALIdeal.X6CoarseModuliIdeal`, `X6ALIdeal.ElkiesX6StarEveryIdeal`, `GRX6AbPrint.X6CoarseModuli`,
    `ElkiesX6StarEvery`, `ElkiesX6StarPrinted`, `ElkiesX6StarFunctionField`, `ElkiesEquationsX6Ab`,
    `BabaGranathRationalAb`, `GonzalezRotgerX6Ab_r5`, `gonzalezRotgerX6Ab_r5_of_coarse`, `x6ModuliWitness_of_coarse`,
    `SGRDirect.elkies_coordinate`, `GR9.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb`, `R1R2fpRepW`,
    `R1R2fpRepW_r5`, `R1R2fp`, `X6ConicModel`, `OpenResearchLeaves57`.
  * In it: `Y3P1j.Y3ToP1j`, `SGRDirect.HeckeSqrtBranchAny`, `Y3X6.R1R2fpY3`, and both new projections of
    `OpenResearchLeaves59Y3`.
  * No `_r5` or cm-fold-rebase `_cm` copy is in the closure. The three names with those suffixes are unrelated lemmas:
    `RayClassCFT.nrd_pos_of_cm`, `GapST.twist_of_cm`, `GlueAssembly.max_one_hA_le_cm`.
  * The closure names containing "X6" are the same four kinds as in y3-x6:
    * the proved count fields `gonzalezRotgerProp56X6` and `gonzalezRotgerCountX6(Ab)`;
    * the `x6ConicModel` fields of the added bundles (type `X6ConicModel_y3 = True`);
    * quaternion-arithmetic lemmas named `x6`;
    * the new bundles' names (`_y3x6`).
* **Dry-run fold** (`scratch/y3-x6b/MainDryRun.lean` → `maindryrun-out.txt`): fork main's `Main.lean` with the research
  bundle switched to `OpenResearchLeaves59Y3` and the H argument to `sixContactMin_of_open78_y3x6 r t l`. It is the
  generation after `sixContactMin_of_open77_cm`. `lake env lean` exits 0, and the output is `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice,
  Quot.sound]` (VERIFIED).
* **`#discharges`** (`scratch/y3-x6b/Discharges.lean` → `discharges.txt`): it imports Main, Discharges and `Y3X6Fold` (all built with `lake build`, EXIT 0,
  `build-main.log`). The summary line is "30 open hypotheses, 14230 theorems checked, 405 discharge one" (VERIFIED).
  * The open hypotheses are those of fork main's current `frozenTarget` (`OpenResearchLeaves57`, TailZ83). Main is not
    switched to the CM fold on this branch.
  * 15 of the 405 are the pre-existing reductions on main. They are the same 15 that cm-fold-rebase lists: carayol,
    ds965, deRham ×2, javanpeykar, the two X₆ rows (`ideal_of_elkiesX6StarEvery`, `x6CoarseModuliIdeal_of_twist`),
    deligne, GR §9 from Bost, pazuki ×4, hodgeTate ×2.
  * The other 390 are projections `X.<field>` of copied bundle structures: cm-branch2's and cm-fold-rebase's `_r5`/`_cm`
    copies (300, as in cm-fold-rebase) and this task's `_y3`/`_y3x6`/`59Y3` copies (90). This is the known noise for
    copied structures.
  * No y3-x6b theorem discharges a top field, as expected for a re-route. There is no `sorry`.
* **Autofold spec**: `scratch/y3-x6b/autofold.json`. It is a hand fold (re-route): replace
  `sixContactMin_of_open77_cm r t l` by `sixContactMin_of_open78_y3x6 r t l` and the bundle `OpenResearchLeaves58CM` by
  `OpenResearchLeaves59Y3`, and import `ZInQKernel.Contrib.OneProof.Y3X6Fold`. It removes the two X₆ fields and lists the
  new leaf (with kind and flag) and the glue. It lands as one package with cm-fold-rebase's fold, applied after it.
* **kinds rows**:
  * add (`scratch/y3-x6b/kinds-rows.tsv`, main's 13 columns): `research/y3ToP1j` (consequence, ELLIOT, GLUE/GLUE) and
    `research/heckeSqrtBranchAny` (glue, GLUE/GLUE);
  * remove (`kinds-remove.tsv`): `research/x6CoarseModuliIdeal` and `research/elkiesX6StarEveryIdeal`, both GLUE/GLUE in
    kinds.tsv lines 27 and 10 (VERIFIED, read).
* **Rating of the new statements** (unchanged from y3-x6):
  * `y3ToP1j` is not in printed form. It is the manuscript's derivation (L425-440) over Baba–Granath's quotient, rated in
    y3-p1j.
  * `heckeSqrtBranchAny` is glue, not a leaf.
  * Every other new declaration is proved.

## 4. `HeckeSqrtBranchAny` on the `Y₃` route (carried over from y3-x6, unchanged)

Statement (`SGRDirectNV.lean:1143`, unchanged): take a triple `(Y, Φ, π)` with R1fp, R1hecke, R2fp, and a finite Galois
`E/ℚ(X)` with the normalization chart. Then some `c ∈ ℚ^×` and `s ∈ E` satisfy `s² = c(27X + 16)`. On this base its producer and consumers have
bost-gr9 copies (`GR9.SGRFold.heckeSqrtBranchAny_of_open29`, `GR9.openGlue7_of_OpenGlue8`); its one consumer is still
`heckeVertWitness_of_nvSqrtAny` (sgr-direct's Lemma NV route), which feeds `HeckeVertWitness` and then `PropTSAll`.

**Why the manuscript's route cannot supply it.**
* The manuscript reaches the same goal by another path: vertical unramifiedness of the fibre field at `p > 324`.
* Its steps are the stable model and the tame normalizer action (L481-509), then the pullback along `J(u)`
  (L511-519), then the local equation `u − c = z²` after unramified extension (L521-526).
* That is a statement about the completed local rings at `p` of the pulled-back cover. It does not produce a global
  element of `E`.

So "re-route `HeckeSqrtBranchAny` to the tame local equation" really means: replace sgr-direct's NV consumer
(`HeckeVertWitness` from a global square root, `NVLocalInertia`, `HeckeBranch`) by the integral-model argument. That is
the route the tree had before sgr-direct. It needs L481-509 in Lean (stable-model uniqueness, tame quotients,
`P¹_{ℤ_p}` with three sections), which is not there. Out of scope for this task; listed under "remains".

**A `Y₃`-only argument (ON THE SPOT; not proved, not built on).**
1. The Hecke automorphisms of `Y` (twists by `Aut 𝒪`, `rightMul` by `𝒪^×`; `R1heckeProps`) are `ℚ`-automorphisms that
   preserve `π`. By the fibre clause of `Y3ToP1jAt` they act transitively on every geometric fibre. So for the image
   `Γ` in `Aut(E/ℚ(X))`, where `E ≅ ℚ(Y)` by the normalization chart, `ℚ(Y)^Γ = ℚ(X)`, and `Γ` is the Galois group.
2. The geometric inertia groups over `0, ∞, −16/27` are cyclic of orders `4, 6, 2` (L421-422, L500), and their
   generators multiply to `1`.
3. The quotient `Γ → N/(𝔸_f^×K₀) ≅ W ≅ (ℤ/2)²` (L425-429) has a character `χ` with `χ(σ₀) = 0` and
   `χ(σ_∞) = χ(σ_{−16/27}) = 1`. This is the Atkin–Lehner element fixing the `CM(−4)` points; it is the kernel's
   `ALFixedPoints` leaf in group-theoretic form.
4. `E^{ker χ}` is a quadratic extension `ℚ(X)(√f)` that is geometrically ramified exactly over `−16/27` and `∞`. Taking
   `f` squarefree in `ℚ[X]`, `f = c(27X + 16)` with `c ∈ ℚ^×`: it is not a constant extension, because it is ramified.

Steps 1 and 3 need the Galois theory of function fields with monodromy, which is not in Mathlib 4.35. Hence the glue
field.


## 5. On-the-spot steps, labels, known issues

* ON THE SPOT: §4's argument for `heckeSqrtBranchAny` (docstring of the field in `Y3X6/Top.lean`). Nothing is built on
  it. This is unchanged from y3-x6.
* Known issues: y3-x6's tree issue (Top2 on cm-branch d4073125e) does not apply to this base. If cm-branch's
  `CMHomFieldSplit` change is merged later, Top2 and therefore this chain need the one-line fix (pass the reduced input).
  Manuscript known issues are inherited from y3-p1j §6; there are no new ones.
* No statement was changed. `Y3ToP1j`, `HeckeSqrtBranchAny` and every kept field are verbatim. The removed X₆ fields are
  not restated.

## 6. Remains

* Prove `heckeSqrtBranchAny` (§4), or replace sgr-direct's NV route by the manuscript's integral-model route (L481-526).
  Either gives net −1 GLUE.
* The integrator applies cm-fold-rebase's fold, then this one (autofold.json, kinds rows).
* Optional: prune the 244 copies to the route's closure. The copies include cm-branch2's un-GR9 upper chain, which is
  unused on this route; this is harmless and compiles.
