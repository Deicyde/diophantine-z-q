# theta-fold: `thetaRatiosAlgebraic` replaced in `ZInQ.OneProof.frozenTarget` by Igusa's theta expressions and Lin–Yang's Example 29

Task theta-fold, 2026-11-15. Base a47f9162 (origin/wip/leaf-fold23: fork main plus leaf-fold14 to leaf-fold23;
`frozenTarget` through `HDec.HSyn.sixContactMin_of_open28`, 56 bundle fields). The input is linyang-printed
(origin/wip/linyang-printed 3bb5a828, read with `git show`, not merged): its
scratch/linyang-printed/LinYangPrintedFull.lean contains igusa-alg's file verbatim, which in turn contains theta-split's
and theta-glue's files. Results log: scratch/theta-fold/log.md. This is model work with no human review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means textbook mathematics.
**SPECULATIVE** means a judgement. Locators recalled from memory are **UNVERIFIED**.

## 1. Main result

**`frozenTarget` loses the added-leaf field `thetaRatiosAlgebraic` (GLUE, composite) and gains two printed leaves,
`igusaThetaExpressions` and `linYangEx29All`.** VERIFIED:
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds (12992 jobs);
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
* PruneScan finds 0 unused fields among the 57.

| | H fields | strict (kinds.tsv, H rows) | strictest | all rows of kinds.tsv (with the 7 `frozenTarget` Props) |
|---|---|---|---|---|
| before (a47f9162) | 56 | 46 LEAF / 10 GLUE | 45 / 11 | 63 rows: strict 49 / 14, strictest 48 / 15 |
| after | **57** | **48 / 9** | **47 / 10** | 64 rows: strict 51 / 13, strictest 50 / 14 |

As expected: GLUE −1 and fields +1, in both readings. render_open.py reports "57 H hypotheses, strictest 47/10".

**Why `thetaRatiosAlgebraic` could not simply be proved** (VERIFIED by reading). The field `ThetaRatiosAlgebraic`
(TailA) is universal: for every abelian variety over every number field, with any uniformization and any period
matrix, the theta-constant ratios are algebraic. The printed leaves only speak about the QM curve
`τ ↦ Ω(τ)`. They give theta-split's use form `ThetaRatiosAtQM`, not the universal statement. So the field's consumer
had to change; autofold could not be used.

**The consumer** (VERIFIED by grep and PruneScan). The chain read `thetaRatiosAlgebraic` in exactly one place:
TailK's `gluePieces_of_open4`, via `thetaPointOfFibre_of_qm_ratios hQM l.thetaRatiosAlgebraic`. Every other occurrence
(TailO's `openAddedLeaves4_of_Q5` and `openAddedLeavesQ5_of_Q6`, TailO l.2595/l.2625, and the `field := l.field`
lines) only carries the field from one bundle generation to the next. theta-split's
`thetaPointOfFibre_of_qm_atQM hQM hT` is the same proof with `ThetaRatiosAtQM` applied at the `τ` that
`FibreQMPeriod` provides. igusa-alg and linyang-printed prove
`ThetaRatiosAtQM` from `IgusaThetaExpressions`, `LinYangEx29All` and the chain's `PkgI1.QMHauptmodul`.

### 1.1 Step 1, the plumbing (scratch/theta-fold/plumb.py, compiled on the first try)

* **Moved into TailK, unchanged.** theta-split's `ThetaSplit.ThetaRatiosAtQM`, `ThetaSplit.Jmap_ne_zero` and
  `ThetaSplit.thetaPointOfFibre_of_qm_atQM` (LinYangPrintedFull.lean l.660–712, igusa-alg's verbatim copy of
  scratch/theta-split/ThetaUse.lean §1) now sit in namespace `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`, just before
  `gluePieces_of_open4`. They were not in the chain before (grep, and DumpCompact's new constants). They had to go
  before TailK so that the consumer can name them.
* **The consumer.** `gluePieces_of_open4` takes the new binder
  `hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM`, and its field `thetaPoint` is now
  `ThetaSplit.thetaPointOfFibre_of_qm_atQM (fibreQMPeriod_main_rep …) (hθ l.qmHauptmodul)`. The `QMHauptmodul`
  argument is there because `LinYangEx29All` asserts only the relations for a Hauptmodul supplied from outside.
  The consumer already has `l.qmHauptmodul`, but at the top of the chain it is derived (TailO's `qmHauptmodul_of6`).
  So the top supplies `hθ` as a function of `QMHauptmodul`.
* **Threading.** `sixContactMin_of_open4`, `_open6` … `_open28` take `hθ` as their last binder and pass it down. This
  includes the off-chain `_open12`–`_open16`. The `example` after `_open6` (TailO) states the new binder.
* **New generation (TailZ41).** `OpenAddedLeaves18` is `OpenAddedLeaves17` plus the two new fields
  `igusaThetaExpressions : G0Split.ThetaPt.LinYangPrinted.IgusaThetaExpressions` and
  `linYangEx29All : G0Split.ThetaPt.LinYangPrinted.LinYangEx29All`. TailZ41 also has the conversion
  `openAddedLeaves17_of_OpenAddedLeaves18` and `sixContactMin_of_open29`. The latter supplies
  `hθ := IgusaAlgFinal.thetaRatiosAtQM_of_printedAll l.igusaThetaExpressions l.linYangEx29All`.
  Main.lean imports TailZ41 and uses `sixContactMin_of_open29` with `l : OpenAddedLeaves18`.
* **Contributor modules** (scratch/theta-fold/mk_modules.py cuts them from LinYangPrintedFull.lean by line ranges;
  each imports defining modules, never Main):

  | module | size | content |
  |---|---|---|
  | `ZInQKernel/Contrib/OneProof/LinYangKron.lean` | 51 KB | igusa-alg's Kronecker engine `IgusaAlgEval` (`Data.gen_eq_zero`, `decide +kernel`, no `native_decide`) |
  | `LinYangSplit.lean` | 16 KB | theta-split §2–§4 and §7: reduction of `ThetaRatiosAtQM` to symmetric functions of `θ⁸`, `qmR`, `ThetaEightSquare`, `QMThetaSymmetricCurve`, `thetaPointOfFibre_of_qm_curve` |
  | `LinYangGlue.lean` | 64 KB | theta-glue: duplication formula, `thetaEightSquare`, Igusa's theta expressions `psi4Th` … `chi12Th`, `LinYangThetaCurve`, the reduction to `IgusaAlg k`, igusa-alg's Kronecker proofs of `IgusaAlg 3..9`, igusa-alg's `thetaRatiosAtQM_of_linYang`, `thetaPointOfFibre_of_linYang` |
  | `LinYangPrinted.lean` | 31 KB | linyang-printed §1–§4: `siegelEis` (sum over `Γ_∞\Sp₄(ℤ)`), `igusaChi10E`, `igusaChi12E`, `lyS2` … `lyS6`; the LEAVES `IgusaThetaExpressions`, `LinYangEx29All` (and the existence variant `LinYangEx29`, used only as an intermediate); the density glue; `linYangThetaCurve_of_printed[All]`; and §10: `thetaRatiosAtQM_of_printed`, the new `thetaRatiosAtQM_of_printedAll`, `thetaPointOfFibre_of_printed[All]` |

  * **Not copied**, because the fold does not use them:
    * theta-split §0 (the verbatim-copy check of the field) and §1 (now in TailK);
    * theta-split §5–§6 (Route 2 through Shimura's CM theorem; 36 declarations, unused by Dead.lean);
    * linyang-printed §5–§9: `qmHauptmodul_of_printed`, the J-tuple cross-check, the modularity of `siegelEis`,
      `igusaPsi4_of_printed` and `igusaChi10_of_printed`, and the 31-field research bundle. `igusaPsi4` and
      `igusaChi10` are already theorems of the chain (gt-theta, `Contrib/OneProof/ThetaModularityM46.lean`).
  * **Deduplicated** (scratch/theta-fold/DupScan.lean: same type hash, and for definitions the same value, against
    every constant of the environment):
    * theta-glue's verbatim copies of theta-split's `thetaEight`, `qmR`, `ThetaEightSquare`,
      `QMThetaSymmetricCurve` and `esymm_cons_succ` are replaced by `export ThetaSplit (…)`;
    * linyang-printed's `SpMat` is gt-theta's `GapTheta.Mat4` (Contrib), so LinYangPrinted imports
      ThetaModularityM46 and uses `Mat4`;
    * linyang-printed's `countable_B` instance is the chain's (TailZ3, `HDec.LeafQCheck.QMglue`), so it is deleted.

    A second DupScan finds no copies left. The only equal-valued pairs are `IgusaAlgEval.blkR0..3`, which are
    equal by design inside the engine. VERIFIED.
  * Two proofs are copies of inner proof steps, not of declarations: the analyticity of `θ_m∘Ω` in LinYangPrinted
    (period-map's step inside `thetaOmegaAnalytic_of`) and the duplicated `thetaTerm` summand body (from
    `PkgI1.thetaConst`). There is no declaration to reuse in either case.

After step 1, PruneScan reports exactly `OpenAddedLeaves18.thetaRatiosAlgebraic` UNUSED. The prune set has 12 fields
(`OpenAddedLeaves4/6/7/8/9/12/13/14/15/16/17/18.thetaRatiosAlgebraic`) and no constants
(scratch/theta-fold/prune-set-step1.txt). DeadCascade lists three dead readers: `addedLeaves5_of_open6` (TailO),
`addedLeaves11_of_open12` and `sixContactMin_of_open16` (TailZ22), plus the generated `casesOn`/`recOn`.

### 1.2 Step 2, the prune (scratch/theta-fold/prune_edit.py; every deleted line in prune_edit_out.txt)

Deleted:
* the 12 fields of the prune set;
* the 13 assignments into them:
  * `addedLeaves4_of_open5` (TailN, off the chain), `addedLeaves4_of_open6` (TailO);
  * `addedLeaves6_of_open7` (TailX), `addedLeaves7_of_open8` (TailZ4), `addedLeaves8_of_open9` (TailZ13);
  * `addedLeaves9_of_open10` (TailZ17, off the chain), `addedLeaves9_of_open14` (TailZ23),
    `addedLeaves12_of_open13` (TailZ24);
  * `openAddedLeaves13_of_OpenAddedLeaves14`, `…14_of_…15`, `…15_of_…16`, `…16_of_…17`, `…17_of_…18` (TailZ26,
    TailZ30, TailZ31, TailZ34, TailZ41);
* the element `l.thetaRatiosAlgebraic` of the anonymous constructor in `openAddedLeaves4_of_Q5` (TailO l.2595);
* the three dead readers, with their `#print axioms` lines.

Kept:
* Older generations off the chain keep their `thetaRatiosAlgebraic` fields, as in earlier prunes:
  `OpenAddedLeaves5` (TailN), `OpenAddedLeavesQ5`–`Q10` (TailO; `openAddedLeavesQ5_of_Q6` at l.2625 still carries
  it), `OpenAddedLeaves10/11` (TailZ17/18), and the bundles in TailA, TailD, TailE, TailI.
* The general theorems `ThetaPt.thetaNullAlgebraic_of_ratios` and `thetaPointOfFibre_of_qm_ratios` (TailA) are still
  declared. They are now off the closure.

## 2. Every hypothesis after the fold

The full statements are in docs/one-proof/OPEN.md (regenerated) and the kinds in docs/one-proof/kinds.tsv.
* **OpenResearchLeaves21** (29 fields), **OpenTextbookLeaves11** (12) and **OpenGlue7** (1): unchanged.
* **OpenAddedLeaves18** (15 fields):
  * `tateTwistInvariants`, `axSenTate`, `milneIsogenyQuasiInverse`, `shimuraTaniyamaQbar`, `egaIV_8_10_5_xii`;
  * `deligneComponentsY3PrintedAb`, `deligneComponentsX6PrintedAb`, `geomConnOfAlgClosure`;
  * `picRepresentableAbVar`, `picZeroAbVar`, `phiAmpleIsogeny`, `weilPairingMumford`, `shimuraIntegralModelRep`;
  * new: `igusaThetaExpressions`, `linYangEx29All`.
* The 7 non-bundle hypotheses of `frozenTarget` (`h11`, `h29`, `hCM`, `hX`, `h33`, `hL2`, `hL3`) are unchanged.

kinds.tsv rows (both `published`, LEAF/LEAF, flag `pending review; locator UNVERIFIED`, flag class
`pending-review,unverified-locator`, area issue as the removed row):
* `igusaThetaExpressions`: Igusa, Amer. J. Math. 86 (1964) and 89 (1967) p. 848. On `𝔥₂`, `ψ₄`, `ψ₆` (the Siegel
  Eisenstein series) and Igusa's 1962 `χ₁₀`, `χ₁₂` equal the theta expressions. The 76 Fourier coefficients agree
  exactly (linyang-printed py/fourier.py).
* `linYangEx29All`: Lin–Yang, Math. Z. 295 (2020); arXiv:1807.00466v1 Example 29. Wherever `j₆` is finite,
  `s₃² = j₆ s₂³`, `s₅ = s₂s₃`, `s₆ = (j₆+1)s₂³`, for every normalized Hauptmodul. It states the relations only.

The removed row: `thetaRatiosAlgebraic` (composite, GLUE/GLUE). claims.tsv: the `thetaRatiosAlgebraic` row is
deleted.

## 3. The remaining leaves by the theory they come from

This is unchanged from leaf-fold23, except in the group "theta functions and Siegel modular forms of genus 2":
* it loses the composite "theta-constant ratios of every abelian variety over `ℚ̄` are algebraic". That was Shimura
  1976 with Mumford's Tata II and Igusa, never a single printed statement;
* it gains Igusa's theta expressions of `ψ₄`, `ψ₆`, `χ₁₀`, `χ₁₂` and Lin–Yang's Example 29 (Igusa's generators
  restricted to the discriminant-6 quaternionic locus, as functions of the Hauptmodul `j₆`).

The rest is proved in Lean:
* elimination of `j₆` and density off one countable `Γ*`-orbit (linyang-printed);
* the polynomial identities `IgusaAlg 3..9`, by one Kronecker evaluation each (igusa-alg);
* the duplication formula and the global identity `Σθ¹⁶ = (Σθ⁸)²/4` (theta-glue);
* algebraicity from symmetric functions with coefficients in `ℚ(j)` (theta-split).

## 4. Checks (all VERIFIED; one Lean process at a time)

* **Base (a47f9162):**
  * `lake build +ZInQKernel.OneProof.Main` OK. The build tree in the worktree was stale; this was the first build of
    the base, and it built.
  * DumpCompact: 13861 constants (scratch/theta-fold/hashes_before.txt, frozenTarget_before.txt).
  * PruneScan: 56 fields, 0 unused (prunescan_base_out.txt, *-base.txt).
* **After step 1:**
  * `lake build +ZInQKernel.OneProof.Main` OK, with no error on the first try (LinYangGlue 109 s, the rest of the new
    modules under 40 s each);
  * PruneScan as in §1.1 (prunescan_step1_out.txt, *-step1.txt); DeadCascade (dead-cascade.txt).
* **After step 2 and the dedupe/trim:**
  * `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK;
  * the axioms of `frozenTarget` and of `sixContactMin_of_open29` are standard;
  * the printed type of `frozenTarget` differs only in `OpenAddedLeaves17` → `OpenAddedLeaves18`
    (frozenTarget_after.txt).
* **PruneScan (rooted at `frozenTarget`):** OpenResearchLeaves21 29, OpenTextbookLeaves11 12, OpenAddedLeaves18 15,
  OpenGlue7 1 = 57 fields, 0 unused, prune set empty (prunescan_after_out.txt).
* **DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt): 13861 → 13876 constants.
  * **Removed 14:**
    * the 11 pruned fields' projections that existed in the base (`OpenAddedLeaves4/6/7/8/9/12/13/14/15/16/17`);
    * the 3 dead readers `addedLeaves5_of_open6`, `addedLeaves11_of_open12`, `sixContactMin_of_open16`.
  * **New 29:**
    * TailK, 6: `ThetaSplit.ThetaRatiosAtQM`, `ThetaSplit.Jmap_ne_zero` with three `_simp_1_k` auxiliaries, and
      `ThetaSplit.thetaPointOfFibre_of_qm_atQM`;
    * TailZ41, 23: `OpenAddedLeaves18` and its generated `mk`, `rec`, `casesOn`, `recOn`, `mk._flat_ctor` and 15
      projections, plus `openAddedLeaves17_of_OpenAddedLeaves18` and `sixContactMin_of_open29`.
    * The contributor modules are outside `ZInQKernel.OneProof` and are not hashed.
  * **Changed 254:**
    * 216 generated auxiliaries and projections of the 11 edited bundle structures;
    * 13 conversions, value only, each by one deleted assignment or constructor element:
      `addedLeaves4_of_open5`, `addedLeaves4_of_open6`, `addedLeaves6_of_open7`, `addedLeaves7_of_open8`,
      `addedLeaves8_of_open9`, `addedLeaves9_of_open10`, `addedLeaves9_of_open14`, `addedLeaves12_of_open13`,
      `openAddedLeaves13_of_OpenAddedLeaves14`, `…14_of_…15`, `…15_of_…16`, `…16_of_…17`, `openAddedLeaves4_of_Q5`;
    * 23 stack theorems with a changed type (the binder `hθ`): `sixContactMin_of_open4`, `_open6`–`_open15`,
      `_open17`–`_open28`;
    * the edited consumer `gluePieces_of_open4` (type and value);
    * `ZInQ.OneProof.frozenTarget` (type: `l : OpenAddedLeaves18`).
  * No other constant changed. There is no auxiliary `_proof_N` renumbering: the block moved into TailK creates only
    `_simp` auxiliaries under its own names.
* **DupScan, Dead.lean** (scratch/theta-fold/dupscan.txt, dead.txt) as in §1.1.
* **scratch/contrib-kit/DischargesTest.lean** (output in DischargesTest-output.txt):
  * the same discharges and controls: t1 still assumes `QuotientP1Coordinate`, and t3 on `cartierSmooth` is flagged
    for `sorry`;
  * the base's six contribution discharges are listed under `OpenResearchLeaves21`;
  * 64 open hypotheses (base 63).
* **Docs:**
  * `lake env lean scripts/one_proof/OpenStatements.lean` wrote 64 open hypotheses;
  * `render_open.py` reported "57 H hypotheses, strictest 47/10, 7 others", and `--check` reported "ok";
  * open-statements.json, OPEN.md, pages-wanted.md, CONTRIBUTING.md and STATUS.md were regenerated. STATUS.md was
    stale at the base (it still named `OpenResearchLeaves20`).
* FaithCheck was not needed: no HDec copy was replaced by a kernel declaration.

## 5. Not done, and why

* **The two leaves' locators are UNVERIFIED** (no network). The kinds.tsv rows say so.
  * Lin–Yang's display was not re-read. Its `j₆` CM values were read in arXiv v1 by h-v14.
  * Igusa's 1962 constants are VERIFIED only through the Fourier check.
* **`LinYangEx29All` needs `QMHauptmodul` from the chain**, so `hθ` is a function of `QMHauptmodul`.
  linyang-printed's `qmHauptmodul_of_printed` derives `QMHauptmodul` from the existence variant `LinYangEx29`. Using
  it would drop `valenceFormulaCocompactEq` and `shimizuCovolumeO1` only if `QMDenZeroCM3` also followed from the
  printed leaves. That needs "ψ₄, ψ₆, χ₁₀, χ₁₂ have no common zero on `Ω(ℍ)`", which is not proved
  (linyang-printed §5). Not attempted here.
* **Files this task may not edit, which their owners should update:**
  * docs/one-proof/frontier-crosswalk.tsv still has rows H-44, H-133, H-134, H-191 for `thetaRatiosAlgebraic`;
  * the module doc of TailZ22 still names the deleted `sixContactMin_of_open16`.
* The first base build was started with a shell `&` instead of the harness's background mode. It was still the only
  Lean process.

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:** `OpenAddedLeaves17.thetaRatiosAlgebraic : HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic`. For every
  abelian variety over a number field, every uniformization `Φ : ℂ² → A(ℂ)_σ` and every period matrix `Ω ∈ 𝔥₂`,
  some `θ_{m₀}(0, Ω) ≠ 0` and all ratios `θ_m(0, Ω)/θ_{m₀}(0, Ω)` are algebraic. Composite, GLUE/GLUE.
* **Added** (fields of `OpenAddedLeaves18`, which replaces `OpenAddedLeaves17` as `frozenTarget`'s `l`):
  * `igusaThetaExpressions : HDec.HSyn.G0Split.ThetaPt.LinYangPrinted.IgusaThetaExpressions`. For all
    `Ω ∈ PkgI1.SiegelH2`: `siegelEis 4 Ω = psi4Th Ω`, `siegelEis 6 Ω = psi6Th Ω`, `igusaChi10E Ω = chi10Th Ω` and
    `igusaChi12E Ω = chi12Th Ω`. Published (Igusa 1964/1967), LEAF/LEAF, pending review.
  * `linYangEx29All : HDec.HSyn.G0Split.ThetaPt.LinYangPrinted.LinYangEx29All`. For every `j₆ : ℍ → P¹(ℂ)` that is
    continuous, has the `Γ*`-orbits as fibres, is surjective and takes the values `0, ∞, −16/27` at the CM points of
    discriminants `−4, −3, −24`: wherever `j₆ τ = z ≠ ∞`, `s₃² = z s₂³`, `s₅ = s₂s₃`, `s₆ = (z+1)s₂³` at `Ω(τ)`.
    Published (Lin–Yang 2020, Ex. 29), LEAF/LEAF, pending review.
* The other three bundle binders and the seven `Prop` binders are unchanged.

## 7. State of the branch

wip/theta-fold, on a47f9162:
* step 1 at 69c71fa4;
* the prune at 9936f171;
* the dedupe/trim at f016e90b;
* the checks at 752a67f1;
* the regenerated docs at ab7cf427;
* then this report and .fleet/theta-fold.md.
