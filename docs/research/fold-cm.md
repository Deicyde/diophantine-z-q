# fold-cm: the CM-branch package folded at +4 (both components, regenerated on fold-c8's top)

Task fold-cm, 2026-11-17. Base: wip/leaf-fold33b 0bcb3b0b1 (main + inbox 85; top `sixContactMin_of_open80` on
`OpenResearchLeaves61`, TailZ87, C8Chain). The branch wip/fold-cm is that base plus this task's commits, so
wip/leaf-fold33b can fast-forward to it. Results log: `scratch/fold-cm/log.md`. Replay: `scratch/fold-cm/REPLAY.md`
and `scratch/fold-cm/autofold.json`. This is model work; no person has reviewed it.

Jack's ruling, verbatim, to the question "Should [the CM-branch package] fold now?": **"Fold now at +4 (Recommended)"**.

Marks: **VERIFIED** means compiled, computed, or read in a named file on this host. **UNVERIFIED** means not checked
here. Theorem numbers quoted from the specs and not read here are marked UNVERIFIED.

## Manuscript check

**No step was found to be an error.** Every row was read in `diophantine_zq.tex` on this host. The computations are
`scratch/fold-cm/pullback_check.py` → `pullback_check.txt` and `scratch/fold-cm/gram_check.py` → `gram_check.txt`
(pure Python with exact rationals; this host has no sympy). The cited prints (Fowler, [cmheight], Gaudron–Rémond,
Baba–Granath, Lin–Yang) are not on this host.

| tex lines | statement (paraphrase) | verdict |
| --- | --- | --- |
| L578-580 | case split on `End⁰(A_ℚ̄)` (CM fibres / non-CM fibres) | OK. The Lean form is `CMBranch.sixContactMin_of_branches` (cm-branch). |
| L581-586 | CM fibres: matrix units give `E/L` with CM and an `L`-isogeny `E² → A` | OK as written. It uses L560-561 (`L` defines every geometric endomorphism). In Lean this is the open GLUE row `cmFibreSplit`. Inherited known issue: A8 at a CM fibre, cm-branch2 §2.3. |
| L586-587 | `[ℚ(j(E)):ℚ]` is the order class number, so `h(Δ) ≤ d ≤ D` | OK. It is classical and uncited (ELLIOT-literature), and is the leaf `cmjDegree` in consequence form `#Pic(R) ≤ [L:ℚ]`. Cox Thm 11.1 is UNVERIFIED. |
| L588-593 | Fowler Prop. 2.7: `√|Δ| ≤ 2D² exp(21000D²)`, no exceptional field | OK at the level of the citation; the print was not read here. This is the leaf `fowlerProp27` (printed form, pending review). |
| L594-598 | good reduction after a finite extension (`j` integral); the stable height does not change | OK. The first half is uncited, so it is the leaf `cmPotentialGood`. The second half holds by definition of the stable height. |
| L598-600 | reduced CM period: `√3/2 ≤ y ≤ √|Δ|/2` | **OK, correct as written** (the integrator's expected verdict). For a reduced form `(a,b,c)`, `y = √|Δ|/(2a)` with `a ≥ 1`, and `y ≥ √3/2` holds on the fundamental domain. The Lean proof is `ReducedCMPeriod` (cm-branch2). |
| L600-605 | archimedean summand `−log 2π + πy/6 − ½ log y − 2Σ log|1−qⁿ|` by (6.2) of [cmheight] | OK. It equals `−(1/12) log(|Δ(τ)| y⁶)` with `Δ = (2π)¹² q ∏(1−qⁿ)²⁴` (expansion checked by hand). The display of (6.2) was not read here, so the row is the leaf `cmHeight62` (consequence form). |
| L606-611 | `ρ = e^{−2πy} < 1/100`, `2ρ/(1−ρ)² < 200/9801`, `−½ log y < 1/10` | OK. At `y ≥ √3/2`, `ρ ≤ e^{−π√3} ≈ 0.0043` and `−½ log(√3/2) ≈ 0.072` (computed). |
| L611-614 | `h_F(E) ≤ π√|Δ|/12 + 1 ≤ D² 3^{21000D²} + 1` | OK, since `π/6 < 1` and `e < 3`. |
| L615-627 | Gaudron–Rémond 2014 Thm 1.4 with source `E²`; Faltings' isogeny variation; `C_cm` arithmetic | OK. The arithmetic was checked: `256 log 28 < 1024`, `log(2B_cm) ≤ 2 + 2D + 42000D²`, and the sum gives `1028 + 5D + 84000D²`. The citations are unchanged leaves of the existing route. |
| L629-631 | the degree of the auxiliary extension does not enter | OK. |
| L411-418 | `B = (2,−3)`, `𝒪`, `μ = 2j + ij`; the matrix of `Trd(μ⁻¹xȳ)`; determinant one | OK, VERIFIED: the matrix equals the printed one with the + sign, and its determinant is 1 (`gram_check.txt`). |
| L420-422 | normalizer quotient `P¹_j`, branch values `0, ∞, −16/27`, indices `4, 6, 2` [BG, LY] | OK at the level of the citations (prints not read here). This content is the leaf `y3ToP1j`, with y3-p1j's caveats: the indices are orbifold orders, and the `j`-normalization is a Möbius choice. |
| L423-429 | `N` normalizes `K₃`; `\|N/𝔸_f^×K₀\| = 4` | OK. `B` is ramified exactly at 2 and 3: `(2,−3)₃ = (2/3) = −1`, then the product formula (`gram_check.txt`). |
| L430-434 | central finite ideles act trivially on `Y₃` | OK. |
| L434-436 | "Consequently" all of `Y₃` has the action of `N/𝔸_f^×K₃` with quotient `P¹_j` | **OK with an implicit step** (the integrator's expected verdict): the quotient of `Y₃` by `K₀/K₃` and then by `N/𝔸_f^×K₀` is `P¹_j`. **Gap filled** by the leaf `y3ToP1j` (y3-p1j's every-witness form). |
| L436-440 | `deg(Y₃ → P¹_j) ≤ 4\|(𝒪/3𝒪)^×\| ≤ 324` | OK. `\|(𝒪/3𝒪)^×\| = 81 − 9 = 72` at the ramified prime 3. |
| L481-509 | normalizer action on the stable model, tame quotient, integral model in the `j`-coordinate | **bypassed, unchecked**. Not used in Lean: the route uses d2a6b's `Y3FullThreeRepZ30` and sgr-direct's Lemma NV. |
| L511-516 | `J(u) = −57600F²/G⁶` and `G⁶ − 97200F² = H²` | OK, **VERIFIED by exact computation** (`pullback_check.txt`; `F`, `G` from L381-383). |
| L517-519 | pullback indices `2, 6, 2`, `2, 1, 1` after tame normalization; prime support `≤ 13` | OK. The prime support of the discriminants, leading coefficients and pairwise resultants of the ten factors is {2, 3, 5, 7, 11, 13} (VERIFIED). |
| L519-521 | normalized cover of degree `≤ 324`, branched only at the six contacts | OK. `J(∞) = −57600/7⁶` is not a branch value (VERIFIED). |
| L521-526 | local equation `u − c = z²`; even positive contact valuation unramified | OK as a local statement. It is not used in Lean: `heckeSqrtBranchAny`'s global square root over `Y₃` is an **on-the-spot** argument (y3-x6 §4), and its kinds row says so. |
| L770-773 | G1: Shimura's quotient construction | Unchanged. It stays on Diamond–Shurman 9.6.5 (Jack: "Keep DS 9.6.5 (Recommended)"). **`ShimuraTotalToComponents` is not folded**; it occurs nowhere in `ZInQKernel/OneProof/` (VERIFIED). |

The integrator's expected verdicts are confirmed:
* L581-631 OK, with L598-600 correct as written.
* L411-526 has no error, and L511-519 is verified by `G⁶ − 97200F² = H²`.
* L425-436 is OK, with an implicit step at L434-436.

## 1. Result

**Both components are folded, built and checked. The measured count is the expected one: H strict 5/24 on 29 →
5/28 on 33 (strictest 5/24 → 5/28), i.e. +4, with 30 → 34 open hypotheses** (VERIFIED: render_open and
OpenStatements).

| step | top | rows out | rows in | H strict / strictest |
| --- | --- | --- | --- | --- |
| base | `sixContactMin_of_open80` (TailZ87, `OpenResearchLeaves61`) | | | 5/24 on 29 |
| 1: cm-fold-rebase 664e00417 | `sixContactMin_of_open81` (TailZ88, `OpenResearchLeaves62`) | `gonzalezRotgerThm512X6RCF` | `cmFibreSplit` (glue), `fowlerProp27`, `cmjDegree`, `cmPotentialGood`, `cmHeight62` (pending review) | 5/28 on 33 |
| 2: y3-x6b 9a2bbbe3f | `sixContactMin_of_open82` (TailZ89, `OpenResearchLeaves63`) | `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal` | `y3ToP1j` (pending review), `heckeSqrtBranchAny` (glue) | 5/28 on 33 |

`frozenTarget` now takes `(r : OpenResearchLeaves63) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves28) (hPC)`.
Each new leaf counts as GLUE until it is rated:
* `fowlerProp27` is published, with a flag beginning "pending review".
* `cmjDegree`, `cmPotentialGood`, `cmHeight62` and `y3ToP1j` are of kind consequence, with flags beginning "pending review".
* No published row is "unread:".

The trade is the one Jack approved. Four routes the manuscript does not cite (González–Rotger 5.12, the NoCM route, `X₆`
as coarse moduli, Elkies) are replaced by the manuscript's CM branch (L581-631) and its level-3 curve `Y₃` (L411-526).

## 2. How it was built (VERIFIED)

autofold.py's `discharges` format cannot express this fold: the removed fields are unread on the new route, not proved
(cm-fold-rebase §5 says the same). So the fold is a chain of generators in `scratch/fold-cm/gen/`, run with the
`--allow-rise` semantics the ruling grants. Each generator asserts the text it edits and is idempotent (a rerun on this
tree gives identical output). Main moved three copy reroutes past the components' base (SSFChain, D2A6Chain, C8Chain;
live chain base `sixContactMin_of_open4_hf_pz_eb_u_c8`), so both components were regenerated on the live chain; no old
TailZ numbers were replayed.

1. **Merges.** Both merges were clean and only add files. Hygiene renamed these files to `.lean.txt`, because they
   redeclare `HDec.CMBranch`/`HDec.HSyn` names or `frozenTarget`:
   * `scratch/cm-branch/CMBranchMain.lean`;
   * `scratch/cm-branch2/gen/top2_header.lean` (its generator `mk_top2.py` updated to match);
   * `scratch/cm-fold-rebase/MainDryRun.lean`;
   * `scratch/y3-x6b/MainDryRun.lean`.

   Host paths were removed from `scratch/cm-branch/gen/mk_localize.py` and `scratch/cm-branch2/gen/gen_open73.py`. Neither
   branch vendors code, so there are no LICENSE/NOTICE files to keep.
2. **The CM branch on the live bundles** (`ZInQKernel/Contrib/OneProof/CMBranchUC8.lean`, a proof file kept separate from
   the fold). It holds cm-branch's localized theorems (fibre context `FibreCtxNC`) composed with d2a6b's and fold-c8's
   replacements:
   * `good_of_QML3` → `good_of_QML3U`;
   * `localGlue_at` → `localGlue_at_u`;
   * `qmModelG3_of` → `D2A6.qmModelG3U_of_z30`;
   * `{3} ⊆ T u` → `T324 ⊆ T u`;
   * `GaloisPieces` → `GaloisPiecesC8`.

   Its top is `sixContactMin_of_open4_cm_u_c8` over `OpenResearchLeaves2EBU` / `OpenAddedLeaves4PZC8`. No mathematics
   changes. It compiled on the second try.
3. **Component 1** (each generated module compiled on the first try):
   * `mk_top_live.py` → `OneProof/H/CMTopLive.lean`: the 31 chain theorems open80 … open6, copied with
     `c : CMBranch.CMInputs3` threaded. The base `..._u_c8_cm` has `ReducedCMPeriod` and `HeightAdditivityUpper` proved
     (cm-branch2) and `CoxProperLattice` proved (cox-lattice).
   * `DirtyCM.lean` gives 939 dirty constants of 97067.
   * `gen_r5live.py` (cm-fold-rebase's `gen_r5b.py` retargeted) → `CMR5_1`, `CMR5_2`, `CMR5`: 117 new `_r5` copies. 74
     copies are reused from cm-branch2's `R5Prune*`. cm-fold-rebase's three producer patches are applied: the
     González–Rotger producer is replaced by `gonzalezRotgerX6Ab_r5_of_coarse`.
   * `gen_open81.py` → `CMOpen.lean`: the bundles 60, 59, 54SFU, GR9 36EBCFSFU and 35EBCFSFU, copied without the
     González–Rotger field. It also writes `TailZ88.lean`.
   * `fold_main1.py` writes `Main.lean` and kinds.tsv.
4. **Component 2:**
   * `gen_y3live.py` imports y3-x6b's `gen_y3b.py` and replaces its bost-gr9 entries by the live `_sf_u_c8` copies. It
     writes `OneProof/H/Y3Copy1-6`: 274 blocks, suffixed `_y3c` because y3-x6b's `_y3` names exist in
     `Contrib/OneProof/Y3X6/Copy*`. The second compile succeeded after three top chain theorems that inline the deleted
     35→34 conversion were added to DELETE.
   * `gen_top_y3.py` → `Y3Open.lean` + `TailZ89.lean`. `TailZ89` imports `TailZ88`, so no constant leaves the
     environment.
   * `fold_main2.py` writes `Main.lean` and kinds.tsv.

**Files.**
* New Lean files:
  * `Contrib/OneProof/CMBranchUC8.lean`;
  * `OneProof/H/{CMTopLive, CMR5_1, CMR5_2, CMR5, CMOpen, TailZ88, Y3Copy1..6, Y3Open, TailZ89}.lean`.
* Changed:
  * `OneProof/Main.lean` (import, binder, call, two paragraphs);
  * `docs/one-proof/kinds.tsv` (3 rows dropped, 7 added);
  * the regenerated docs.
* No existing declaration of `ZInQKernel/OneProof/H/` is changed. **claims.tsv and volatile.tsv were not written**
  (volatile.tsv does not exist on this base, and claims.tsv has no row for the removed fields).

**kinds.tsv rows** (bundle research):
* removed: `gonzalezRotgerThm512X6RCF`, `x6CoarseModuliIdeal`, `elkiesX6StarEveryIdeal`;
* added, from the branches' kinds-rows.tsv:
  * `fowlerProp27` (published), `cmjDegree`, `cmPotentialGood`, `cmHeight62` (consequence) and `y3ToP1j`
    (consequence): each flag is prefixed "pending review (new leaf, GLUE until a reviewer rates it); ", with flag_class
    pending-review;
  * `cmFibreSplit` (glue);
  * `heckeSqrtBranchAny` (glue): its flag begins "on-the-spot: the Y3-only argument (the quadratic subcover of
    Y3 -> P^1_j ramified over -16/27 and oo gives the global square root) is not in the manuscript, whose route
    (L481-526) is local".

## 3. Checks (VERIFIED; `scratch/fold-cm/run_checks-fold{1,2}.txt`, `axioms-out.txt`, `closure-x6.txt`)

* **Build.**
  * `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` with all new modules: EXIT 0 after each
    component (16353 and 16364 jobs).
  * `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `ZInQ.OneProof.frozenTarget`, `open82`, `open81`,
    the CM bases, the `_r5` / `_y3c` chain tops, the 35→34 conversions, `coxProperLattice_proof`,
    `reducedCMPeriod_of_leaves`, `heightAdditivityUpper_of_t35` and `Y3X6.r1r2fpY3_of`.
* **Hash guard** (DumpCompact + cmp_hashes):
  * component 1: 21343 → 22561 constants, 1218 new, only `ZInQ.OneProof.frozenTarget` changed;
  * component 2: 22561 → 24772, 2211 new, 0 removed, only `frozenTarget` changed.
* **Closure of `frozenTarget`** (295296 constants after both components):
  * Absent:
    * `sorryAx`;
    * every González–Rotger 5.12 constant (`GonzalezRotgerThm512X6RCF`, `GonzalezRotgerThm512X6`, `_of_rcf`,
      `r5ptProps_of_thm512`, `gonzalezRotgerX6Ab_of_print`, `GonzalezRotgerX6`, `GonzalezRotgerX6Ab_r5`,
      `gonzalezRotgerX6Ab_r5_of_coarse`);
    * `R5ptProps`;
    * the NoCM bases `sixContactMin_of_open4_hf_pz_eb(_u_c8)` and `FS5NoCM.R1R2fpFullProps`;
    * every X₆ clause def (`X6Props`, `R2X6Props`, `CMExists`, `X6Surj`, `R2X6PropsIff`);
    * every X₆ leaf (`X6CoarseModuliIdeal`, `ElkiesX6StarEveryIdeal`, `X6CoarseModuli`, `ElkiesX6StarEvery`,
      `ElkiesX6StarPrinted`, `ElkiesX6StarFunctionField`, `ElkiesEquationsX6Ab`, `BabaGranathRationalAb`);
    * every X₆ producer (`x6Rows_of_leavesW`, `x6ModuliWitness_of_coarse`, `elkies_coordinate`);
    * `R1R2fpRepW(_r5)`, `R1R2fp`, `X6ConicModel`;
    * the old tops and bundles 61, 62, open80, open81.
  * Present: the five CM statements, `coxProperLattice_proof`, `HeightAdditivityUpper`, `ReducedCMPeriod`, `Y3ToP1j`,
    `R1R2fpY3` and `HeckeSqrtBranchAny`.
  * **Name scan (`ClosureX6.lean`, 62 matches; every one is classified, and none is a González–Rotger statement or an
    X₆ clause, leaf or producer):**
    * 23 bundle projections `gonzalezRotgerProp56X6` / `gonzalezRotgerCountX6(Ab)`. Their type is
      `GR56.R5fpCountLe` (the CM-point count), filled by the proved `EichlerBound.r5fpCountLe_of_two` from the textbook
      bundle. The name mentions González–Rotger; the content is proved.
    * `GRCountX6.*` helpers of that proof.
    * The quaternion elements `x6`, `x6i` (LeafQCheck, PeriodGlue).
    * `X6ConicModel_y3c := True` (y3-x6's replacement) and its carried `x6ConicModel` fields.
    * `x6Rows_of_open14_…_y3c`, patched to build `R1R2fpY3` from `y3row`.
    * `Y3X6.*` (the row over `Y₃`).
    * Two `FS5NoCM._proof_1` auxiliary instance terms.
    * `FS5NoCM.CMOptimalEmbedding` (in lower added bundles), `CMBranch.NoCMAt` (the CM branch's own predicate) and the
      proved `ConjMapsNoCM`.
* **Field checks:** `OpenResearchLeaves62` = `61` − `gonzalezRotgerThm512X6RCF` + 5 CM fields, and
  `OpenResearchLeaves63` = `62` − `x6CoarseModuliIdeal` − `elkiesX6StarEveryIdeal` + `y3ToP1j` + `heckeSqrtBranchAny`. No
  field type differs.
* **`#discharges` on the folded tree:** 34 open hypotheses, 13499 theorems checked, 135 discharge one, all with the
  standard axioms. Most are projections of copied structures (`CMInputs2/3.*`, bundle copies), the known noise. The
  rest are pre-existing reductions, for example `heckeSqrtBranchAny` from Elkies-based theorems that still assume the
  X₆ leaves. The removed fields leave by the reroute, not by a discharging theorem; the closure check is the evidence,
  as for every copy reroute (cm-fold-rebase §4, fold-c8 §3).
* **OpenStatements:** 34. **render_open:** 33 H hypotheses, strict 5/28, strictest 5/28, 1 other; `--check` ok.
  **frontier_crosswalk:** 232 IDs, 3 matched; `--check` ok. **DischargesTest** rerun: 135 DISCHARGES lines, no error.
  **autoform check:** exit 0 (776 articles, 647 fully proved). **`scratch/lane74/gate.sh`:** GATE=ok, after each
  component.
* Not run: the AllContrib clash scan. The new OneProof modules are not in AllContrib. The `_y3c` suffix keeps them
  apart from y3-x6b's `_y3` Contrib copies, so the one co-import risk of this fold is avoided.

## 4. For the integrator

* **Inbox 84.1 is not live** (VERIFIED, read 11-17 18:55 on this host). The running autoland loop started 11-17 04:14 and
  runs `autoland-loop.sh` with mtime 04:14. That script's docs-only merge filter has no claims.tsv/volatile.tsv
  exemption. The exemption exists only in `autoland-loop.sh.new` (15:23), which is not installed. So the desk's claims
  Action (#100) would still be blocked.
* Suggested landed.txt note (the ruling quoted): `fold-cm: CM-branch package at +4 (5/24 on 29 -> 5/28 on 33); Jack:
  "Fold now at +4 (Recommended)"`.
* A replay on a later head is `scratch/fold-cm/REPLAY.md`, whose head-dependent points are listed there. An autofold
  that adds research generations above 61 needs one more copied generation in `gen_open81.py`.

## 5. Known issues and what remains (inherited, not papered over)

* `cmFibreSplit` is open GLUE: A8 at a CM fibre without NoCM (cm-branch2 §2.3).
* Reviews are pending:
  * `fowlerProp27` is the one row that can become LEAF as printed;
  * `cmjDegree` and `cmPotentialGood` are uncited (ELLIOT-literature; UNVERIFIED locators);
  * `cmHeight62` and `y3ToP1j` are consequence forms.
* `heckeSqrtBranchAny` is glue whose `Y₃`-only argument is on-the-spot (y3-x6 §4): the manuscript's route is local.
* The un-pruned intermediate modules are imported but off the route: `CMTopLive`, and the `_r5` copies superseded by
  `_y3c`. They hold new constants only.
