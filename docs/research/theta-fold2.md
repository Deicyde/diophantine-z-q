# theta-fold2: `thetaRatiosAlgebraic` removed from the single proof, in place, with no new leaf

Task theta-fold2, 2026-11-16. Base 47aaf586 (origin/wip/leaf-fold31; it builds, §4). Source: theta-direct
(origin/wip/theta-direct 584bbb24, which contains 311bd23a; docs/research/theta-direct.md), merged. theta-direct's
fold.patch was **not** applied: the fold was redone in place on this base with a shorter threading (§1.1). Results
log: scratch/theta-fold2/log.md. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement.

## 1. Main result

**`frozenTarget` loses one hypothesis and gains none** (VERIFIED):
* removed: `OpenAddedLeaves17.thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic` (composite, GLUE);
* `lake build +ZInQKernel.OneProof.Main` succeeds (13706 jobs);
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
* PruneScan: 44 fields, 0 unused;
* no new leaf, no new GLUE statement, no new bundle generation; frozenTarget's statement text and hash are unchanged
  (its binder `OpenAddedLeaves17` has one field fewer).

| docs/one-proof/kinds.tsv | H fields | strict | strictest | all rows strict | all rows strictest |
|---|---|---|---|---|---|
| before (47aaf586) | 45 | 34 LEAF / 11 GLUE | 34 / 11 | 56: 42 / 14 | 42 / 14 |
| after | **44** | **34 / 10** | **34 / 10** | 55: 42 / 13 | 42 / 13 |

Fields −1, GLUE −1, as expected. (The generated docs committed at the base were stale: STATUS.md said 48 H and
39/9, with `OpenTextbookLeaves11`; the regenerated STATUS.md says 44 H, strictest 34/10.)

**Why the field is not needed.** Its only reader, TailK's `gluePieces_of_open4` (field `thetaPoint`), used it only
through theta-split's use form `ThetaRatiosAtQM` (the theta-null ratios at pkg-I1's QM period matrices `Ω(τ)` with
`j_θ(Ω(τ)) ∈ ℚ ∖ 0`), and theta-direct proved that use form with no hypotheses
(`HDec.ThetaDirect.thetaRatiosAtQM_proof`, ZInQKernel/Contrib/OneProof/ThetaDirect.lean; VERIFIED again here: it is now
in frozenTarget's closure and frozenTarget's axioms are standard).

### 1.1 Step 1: the plumbing (scratch/theta-fold2/plumb.py; compiled before any deletion)

TailK cannot import the proof: ThetaDirect's import closure reaches TailZ24 (through `ThetaModularityM46` and
`GammaStarArea`, which import TailZ24, and `Kron`, which imports TailZ19; VERIFIED with scratch/theta-fold2/closure.py).
So the "closed theorem used directly in TailK" route is impossible. But **TailZ25 is outside that closure**, so the
argument only has to be threaded up to `sixContactMin_of_open19`, not to the top as theta-direct's patch did:

* **TailK**: theta-split's block (`G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero`,
  `thetaPointOfFibre_of_qm_atQM`) moved verbatim from theta-direct's `ThetaDirect/UseForm.lean` to just before
  `gluePieces_of_open4`, with its section comment extended by a theta-fold2 note.
* **`gluePieces_of_open4`** gets the new last binder `(hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)`;
  `thetaPoint := ThetaSplit.thetaPointOfFibre_of_qm_atQM (fibreQMPeriod_main_rep …) (hθ l.qmHauptmodul)` instead of
  `thetaPointOfFibre_of_qm_ratios (…) l.thetaRatiosAlgebraic`.
* `hθ` is threaded (new last binder, passed down) through `sixContactMin_of_open4` (TailK), `_open6` (TailO, and the
  `example` after it), `_open7` (TailX), `_open8` (TailZ4), `_open9` (TailZ9), `_open10` (TailZ11), `_open11` (TailZ13),
  `_open12` (TailZ15), `_open13` (TailZ17), `_open14` (TailZ18), `_open15` (TailZ19), `_open17` (TailZ23) and `_open18`
  (TailZ24). (`_open12`–`_open15` are off frozenTarget's path, since `_open17` calls `_open11`, but they call the
  threaded theorems, so they take the binder too.)
* **TailZ25** imports `ZInQKernel.Contrib.OneProof.ThetaDirect`, and `sixContactMin_of_open19` passes
  `HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul` to `_open18`. **Its signature is unchanged**, and so are those of
  `_open20`–`_open35`, Main.lean and `frozenTarget`. The Contrib callers of the top (`X0ModuliUsed.frozenTarget_of_*`
  call `_open29`; `SGRFold`) compile unchanged. No Contrib file names `_open4`–`_open18` or `gluePieces_of_open4`
  (VERIFIED, grep).
* **Contributor modules**: theta-direct's `ThetaDirect/UseForm.lean` (a copy of the block now in TailK) is deleted, and
  `ThetaDirect/Split.lean` imports `ZInQKernel.OneProof.H.TailZ19` instead of it (theta-direct's fold plan §3 item 5).

PruneScan after step 1 (VERIFIED, prunescan-step1-out.txt): exactly `OpenAddedLeaves17.thetaRatiosAlgebraic` is unused,
and the prune set is the field in `OpenAddedLeaves4, 6, 7, 8, 9, 12, 13, 14, 15, 16, 17` (11 entries; the same set
as theta-direct's patch).

### 1.2 Step 2: the prune (scratch/theta-fold2/prune.py; prune_out.txt lists the 24 deleted or edited lines)

* The 11 fields: `OpenAddedLeaves4` (TailK), `6` (TailO), `7` (TailX), `8` (TailZ4), `9` (TailZ13), `12` (TailZ22),
  `13` (TailZ24), `14` (TailZ26), `15` (TailZ30), `16` (TailZ31), `17` (TailZ34).
* The 12 assignments into them: `addedLeaves4_of_open5` (TailN), `addedLeaves4_of_open6` (TailO),
  `addedLeaves6_of_open7` (TailX), `addedLeaves7_of_open8` (TailZ4), `addedLeaves8_of_open9` (TailZ13),
  `addedLeaves9_of_open10` (TailZ17), `addedLeaves9_of_open14` (TailZ23), `addedLeaves12_of_open13` (TailZ24),
  `openAddedLeaves1{3,4,5,6}_of_OpenAddedLeaves1{4,5,6,7}` (TailZ26, TailZ30, TailZ31, TailZ34).
* The element `l.thetaRatiosAlgebraic` of the anonymous constructor in `openAddedLeaves4_of_Q5` (TailO).
* No dead readers remain on this base: theta-direct's list (`addedLeaves5_of_open6`, `addedLeaves11_of_open12`,
  `sixContactMin_of_open16`) had already been deleted by earlier folds (VERIFIED, grep).
* Older off-closure bundles keep the field: `GluePieces2` (TailA), `GluePieces3` (TailD), `OpenAddedLeaves2` (TailE),
  `3` (TailI), `5` (TailN), `10` (TailZ17), `11` (TailZ18), `OpenAddedLeavesQ5`–`Q10` (TailO). They are not in
  PruneScan's prune set, as in earlier folds.
* docs/one-proof/kinds.tsv and claims.tsv: the field's one row in each deleted (saved in
  scratch/theta-fold2/removed-rows.txt).

## 2. Every hypothesis (kinds.tsv after the prune; full statements in docs/one-proof/OPEN.md)

55 open hypotheses: 44 H fields (`OpenResearchLeaves26` 25, `OpenTextbookLeaves12` 10, `OpenAddedLeaves17` 8,
`OpenGlue8` 1) and 11 other arguments of frozenTarget. Format: field (kind, strict).

**research** (25): `bostLowerBound` (published, LEAF), `deRhamH1AbVarT` (published, LEAF), `dsThm965Weak` (published, LEAF), `dsThm966` (published, LEAF), `eigenformHTNew` (consequence, GLUE), `elkiesX6StarFunctionField` (published, LEAF), `gaudronRemondThm14` (published, LEAF), `gonzalezRotgerProp56X6` (published, LEAF), `gonzalezRotgerX6Ab` (published, LEAF), `hodgeTateDecompAbVar` (published, LEAF), `javanpeykarBound` (published, LEAF), `mumfordGroupLaw` (published, LEAF), `neronBaseChangeStrictHenselization` (published, LEAF), `pazukiCor13Upper` (published, LEAF), `r11r12` (composite, GLUE), `r16CoreY` (composite, GLUE), `r17` (consequence, GLUE), `r7a` (published, LEAF), `r9a` (published, LEAF), `r9b` (published, LEAF), `raynaudSemistableSH` (published, LEAF), `sga3_VIB_3_10` (published, LEAF), `sga7_IX_3_3_SH` (published, LEAF), `sga7_IX_3_5_ForwardGeom` (published, LEAF), `shimuraMainThmIDeligneY3AbU` (composite, GLUE)

**textbook** (10): `cartierSmooth` (published, LEAF), `charPolyIndepOfEllAlgClosed` (published, LEAF), `gagaMorphism` (published, LEAF), `geomConnOfRationalPoint` (published, LEAF), `groupSchemeEquidim` (published, LEAF), `homFreeFiniteAlgClosed` (published, LEAF), `mumfordTorsionAlgClosed` (published, LEAF), `neronSchemeExtensionExists` (published, LEAF), `poincareComplement` (published, LEAF), `uniformizationLeafAll` (consequence, GLUE)

**added** (8): `axSenTate` (published, LEAF), `egaIV_8_10_5_xii` (published, LEAF), `milneIsogenyQuasiInverse` (published, LEAF), `phiAmpleIsogeny` (consequence, GLUE), `picRepresentableAbVar` (published, LEAF), `picZeroAbVar` (consequence, GLUE), `tateTwistInvariants` (published, LEAF), `weilPairingMumford` (consequence, GLUE)

**glue** (1): `nvLocalInertia` (project glue, GLUE)

**frozenTarget** (11): `h11` (published, LEAF), `hL29` (published, LEAF), `hT21` (published, LEAF), `hP23` (published, LEAF), `hfx` (published, LEAF), `hL3s` (published, LEAF), `hJP` (published, LEAF), `hCM` (consequence, GLUE), `h33` (published, LEAF), `hFH` (consequence, GLUE), `hL3` (composite, GLUE)

None of these statements changed.

## 3. The remaining leaves by the theory they come from

The only change is in the theta/Siegel-modular group. It loses the composite GLUE field asserting algebraicity of theta-null
ratios at every period matrix of every abelian surface over a number field (Shimura, Duke 43 (1976); Mumford, *Tata
Lectures on Theta II* IIIa §8; Igusa; locators UNVERIFIED). Its one use, at the QM period matrices `Ω(τ)`, is now a
Lean proof (theta-direct, from gt-theta's squared theta laws and the valence formula, with no leaf). Every other group is
unchanged.

## 4. Checks (all VERIFIED; one Lean process at a time)

**Base**, 47aaf586 + the theta-direct merge (Main does not import ThetaDirect at the base):
* the build succeeds (13697 jobs); frozenTarget's axioms are the three standard ones;
* DumpCompact (OneProof and Contrib.OneProof modules in Main's closure): 17299 constants, saved in hashes_before.txt;
  dumpcompact_before_out.txt holds frozenTarget's pp.all type;
* PruneScan: 0 unused of 45.

**After step 1:** the build succeeds (13706 jobs), and PruneScan finds exactly the one field unused.

**After step 2:**
* the build succeeds (13706 jobs) and frozenTarget's axioms are standard;
* PruneScan: 25 + 10 + 8 + 1 = 44 fields, 0 unused, prune set empty (prunescan-out.txt).

**DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt): 17299 constants before, 18176 after.
* **Removed (11):** the projections `OpenAddedLeaves{4,6,7,8,9,12,13,14,15,16,17}.thetaRatiosAlgebraic`. No dead
  reader was deleted.
* **New (888):**
  * 882 constants of theta-direct's contributor modules `ThetaDirect` (69), `.Analytic` (1), `.Glue` (274),
    `.Kron` (277), `.Modular` (51), `.Nodes` (69), `.Relations` (42), `.Split` (71) and `.Valence` (28). They are
    now in Main's closure through TailZ25.
  * 6 in TailK: the moved `ThetaSplit.ThetaRatiosAtQM`, `Jmap_ne_zero` (with its 3 `_simp` auxiliaries) and
    `thetaPointOfFibre_of_qm_atQM`. These are the same declarations that were in UseForm.lean, which was not in the
    base closure.
* **Changed (206):**
  * 178 generated auxiliaries and projections (`mk`, `rec`, `casesOn`, …, field projections) of the 11 edited structures;
  * 13 conversions, value only: `addedLeaves4_of_open5`, `addedLeaves4_of_open6`, `addedLeaves6_of_open7`,
    `addedLeaves7_of_open8`, `addedLeaves8_of_open9`, `addedLeaves9_of_open10`, `addedLeaves9_of_open14`,
    `addedLeaves12_of_open13`, `openAddedLeaves4_of_Q5`,
    `openAddedLeaves1{3,4,5,6}_of_OpenAddedLeaves1{4,5,6,7}`;
  * the edited consumer, with its type changed (new binder `hθ`): `gluePieces_of_open4`;
  * the `sixContactMin_of_open*`, type changed (new binder `hθ`): `_open4`, `_open6`, `_open7`, `_open8`, `_open9`,
    `_open10`, `_open11`, `_open12`, `_open13`, `_open14`, `_open15`, `_open17`, `_open18`;
  * value only: `sixContactMin_of_open19` (now supplies `hθ`).
* `frozenTarget`, `sixContactMin_of_open20`–`_open35` and the Contrib tops (`X0ModuliUsed.frozenTarget_of_*`,
  `ThetaWP8.frozenTarget_noHX`) keep their hashes. frozenTarget's pp.all type text is identical. No other constant
  changed.

**DischargesTest** (scratch/contrib-kit/DischargesTest-output.txt): the controls behave as before.
* `t1` discharges `OpenGlue8.nvLocalInertia` and still assumes it.
* `t2` discharges nothing.
* `t3` discharges `OpenTextbookLeaves12.cartierSmooth` and is flagged for `sorry`.
* The 7 real discharges are the existing contributions.
* 55 open hypotheses. The previously saved output said 59 and `OpenTextbookLeaves11`, because it predated
  leaf-fold30/31 and pi0-fold.

**OpenStatements.lean:** 55 open hypotheses → open-statements.json. **render_open.py** wrote OPEN.md,
pages-wanted.md, CONTRIBUTING.md and STATUS.md ("44 H hypotheses, strictest 34/10, 11 others"). **`--check`:** "ok: 55
open hypotheses, all classified; 4 generated files up to date".

**FaithCheck:** not needed, since no HDec copy was replaced by a kernel declaration.

## 5. Not done, and why

* **Older bundles keep the field.** The 13 older bundles of §1.2 still have `thetaRatiosAlgebraic` (GluePieces2/3,
  OpenAddedLeaves2/3/5/10/11, Q5–Q10). They are off frozenTarget's closure and not in PruneScan's prune set. Deleting
  them would touch conversions that no proof of frozenTarget uses.
* **`ThetaPt.thetaPointOfFibre_of_qm_ratios` and the definition `ThetaRatiosAlgebraic` stay.** They are off the closure
  now, but other modules may cite them.
* **theta-direct's fold.patch was not applied,** for two reasons:
  * its threading to the top (`_open19`–`_open29`, Main.lean, X0ModuliUsed.lean) is unnecessary once TailZ25 can import
    the proof;
  * it would have required editing a Contrib file of another task (X0ModuliUsed.lean).

  Its prune part was redone on this base and produced the same prune set.

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:** `OpenAddedLeaves17.thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic`. The field asserts the
  following, for every number field `K`, abelian surface `A/K`, embedding `σ : K → ℂ`, uniformization `Λ, Φu` of
  `A(ℂ)` and Siegel period matrix `Ω` of `Λ`: some even theta constant `θ_{m₀}(0, Ω)` is nonzero and every ratio
  `θ_m(0, Ω)/θ_{m₀}(0, Ω)` is algebraic. Kind composite, GLUE. Sources: Shimura 1976; Mumford, *Tata II* IIIa §8;
  Igusa; locators UNVERIFIED.
* **Added:** none. frozenTarget's binders are the same types; `OpenAddedLeaves17` has one field fewer.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/theta-direct 584bbb24 (⊇ 311bd23a) | yes | the ThetaDirect contributor modules (UseForm.lean moved into TailK, so deleted), the fold plan (§3 of theta-direct.md) and the plumbing recipe; fold.patch not applied |
| origin/wip/pi0-fold | in the base | PruneScan, DeadCascade, DumpCompact, cmp_hashes, prune_lib, kinds_counts copied to scratch/theta-fold2/ |
| origin/wip/leaf-fold31 47aaf586 | base | builds (13697 jobs) |
