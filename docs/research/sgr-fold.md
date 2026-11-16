# sgr-fold: `shimuraIntegralModelRep` and `quotientP1Coordinate` removed from `ZInQ.OneProof.frozenTarget`; one new glue field `nvLocalInertia`

Task sgr-fold, 2026-11-15. Base 862bd440 (origin/wip/leaf-fold-hx: main 43513d87 plus the hX removal and
re-ratings) merged with origin/wip/sgr-direct 56478c75 (route NV, `ZInQKernel/Contrib/OneProof/SGRDirectNV.lean`
and `SGRDirectElkies.lean`, docs/research/sgr-direct.md). The fold follows sgr-direct's plan
(docs/research/sgr-direct.md §5, scratch/sgr-direct/autofold.json), done by hand in r6-nf's style. Results log:
scratch/sgr-fold/log.md. Model work, no human review.

Marks: **VERIFIED** means compiled, or read in a named file on this host. **STANDARD** means textbook mathematics
with a reference. **SPECULATIVE** means judgement. Theorem numbers recalled without a source are **UNVERIFIED**.

## 1. Main result

**`frozenTarget` loses two strict-GLUE fields and gains one.** The two lost fields are
`OpenAddedLeaves17.shimuraIntegralModelRep : SGRSplit.ShimuraIntegralModelRep` (the integral model of the level-3
Shimura curve over `ℤ_(p)`, rated consequence, GLUE, pending reading) and `OpenGlue7.quotientP1Coordinate :
MCRGlue.QuotientP1Coordinate` (project glue, GLUE). The new field is
`OpenGlue8.nvLocalInertia : SGRDirect.NVLocalInertia` (project glue, GLUE).

VERIFIED:
* `lake build +ZInQKernel.OneProof.Main` succeeds (13000 jobs). Every module under `ZInQKernel/OneProof` and
  `ZInQKernel/Contrib` also builds (3202 modules named, 13129 jobs).
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `ZInQ.OneProof.frozenTarget`,
  `HDec.HSyn.sixContactMin_of_open30`, `HDec.HSyn.glue4_of_open6`,
  `HDec.HSyn.SGRFold.heckeSqrtBranchAny_of_open29` and `HDec.HSyn.SGRFold.openGlue7_of_nvLocalInertia`.
* The type of `frozenTarget` changes in exactly one binder, `(g : HDec.HSyn.OpenGlue7)` → `(g : HDec.HSyn.OpenGlue8)`
  (scratch/sgr-fold/frozenTarget_before.txt, frozenTarget_after.txt).
* PruneScan finds 0 unused fields among the 55 that remain (prunescan-after-out.txt).

| | H fields | strict (kinds.tsv) | strictest | open hypotheses (`#discharges`) |
|---|---|---|---|---|
| before (base) | 56 | 45 LEAF / 11 GLUE | 43 / 13 | 62 |
| after | **55** | **45 / 10** | **43 / 12** | **61** |

**Net −1 GLUE.** The nv-local task is proving `NVLocalInertia` in parallel. When that proof lands, folding it
removes the new field too (another −1 GLUE). It would be a plain autofold: a theorem of type
`SGRDirect.NVLocalInertia` discharges `OpenGlue8.nvLocalInertia`.

**What left the trust base** (from sgr-direct §1):
* the integral model of the Shimura curve `Y₃` over `ℤ_(p)`, `p > 324`: Kottwitz/Lan representability, the
  pending reading of relative Lemma P, and the level comparison;
* the tame-quotient coordinate `𝒴/Γ' ≅ P¹_{ℤ_(p)}`, i.e. mcr-quot's scheme theory.

Both fed one consumer, `HDec.HeckeRestNV.HeckeVertWitness`: no vertical ramification of the Hecke cover at
`p > 324`. That consumer is now proved by route NV, from fields already in the bundles plus `NVLocalInertia`.

## 2. How the fold was done

### 2.1 The consumer (step A; VERIFIED, compiled)

On the chain, `HeckeVertWitness` is filled in TailO's `HSyn.glue4_of_open6`
(`sixContactMin_of_open6 → sixContactMin_of_open4`). TailN's `glue4_of_open5` is its generation-5 twin and is off
the `sixContactMin` stack. It is unchanged.

The changes:
* **TailO** now imports `ZInQKernel.Contrib.OneProof.SGRDirectNV`. That module imports only `OneProof.H.TailG`, so
  the import adds no Mathlib module and no instance.
* **`glue4_of_open6`** now sets
  ```lean
  heckeVertWitness := SGRDirect.heckeVertWitness_of_nvSqrtAny (LeafAdopt.R1R2fp_of_rep r.r1r2)
    (torsionStructure_ofK5 t.t5) l.qmAutCard
    (serreRigidity3_of_T35_5 (uniformizationExists_ofK5 t.t35) (homLatticeCorr_ofK5 t.homLatticeCorr))
    l.alFixedPoints g.nvLocalInertia g.heckeSqrtBranchAny
  ```
  The arguments are:
  * the generation-6 fields `r1r2`, `t5`, `qmAutCard` and `alFixedPoints`;
  * Serre's rigidity, built exactly as `addedLeaves4_of_open6` builds it;
  * two Props carried in the glue bundle.
* **`OpenGlue6` and `OpenGlue7` gain two fields:** `nvLocalInertia : SGRDirect.NVLocalInertia` and
  `heckeSqrtBranchAny : SGRDirect.HeckeSqrtBranchAny`. `glue6_of_open7` copies them.
* **Stack theorem types are unchanged.** Every stack theorem keeps `g : OpenGlue7`. So the contributor files that
  pass `g` to `sixContactMin_of_open29` (X0ModuliUsed, ThetaWeierstrass8) compile unchanged.

### 2.2 The prune (step B; deletions only)

After step A, PruneScan reported exactly `OpenAddedLeaves17.shimuraIntegralModelRep` and
`OpenGlue7.quotientP1Coordinate` as unused (prunescan-stepA-out.txt). The prune set has 12 FIELD lines
(prune-set-stepA.txt):
* `OpenAddedLeaves6.shimuraGoodReduction` and `OpenGlue6.modelCoordinateResidue` (TailO);
* `OpenAddedLeaves7.shimuraGoodReductionNoGuard` and `OpenGlue7.quotientP1Coordinate` (TailX);
* `shimuraGoodReductionNoGuard` in `OpenAddedLeaves8`, `9`, `12`, `13`, `14`, `15` and `16` (TailZ4, Z13, Z22, Z24,
  Z26, Z30, Z31);
* `OpenAddedLeaves17.shimuraIntegralModelRep` (TailZ34).

scratch/sgr-fold/prune_sgr.py deletes these fields and every assignment into them; prune_sgr_out.txt lists all 64
deleted lines. Two cascades were needed in off-chain code:
* `addedLeaves11_of_open12` (TailZ22) is read by the off-chain `sixContactMin_of_open16`, and it read gen 12's
  field. So `shimuraGoodReductionNoGuard` was also deleted from the off-chain `OpenAddedLeaves11` and
  `OpenAddedLeaves10`, which unused-all-stepA.txt shows are wholly unused, together with their two assignments.
* `addedLeaves5_of_open6` (TailO) read gen 6's `shimuraGoodReduction` and was referenced only by its `#print`. It
  was deleted as a dead reader.

**No other field became unused.** Gen 6's `curveBijIso` was read by the old consumer, but it is filled by the proof
`curveBijIso_lf7`.

### 2.3 The new generation (step C)

* **`ZInQKernel/Contrib/OneProof/SGRFold.lean`** (contributor file; imports `OneProof.H.TailZ35` and
  `Contrib.OneProof.SGRDirectElkies`):
  * `HSyn.SGRFold.research14_of_open29` and `added12_of_open29`: the top bundles converted down to generations 14
    and 12 by the existing conversions, as the stack `open29 … open18` does;
  * `HSyn.SGRFold.heckeSqrtBranchAny_of_open29 r t l : SGRDirect.HeckeSqrtBranchAny`, which is
    `SGRDirect.heckeSqrtBranchAny_of_elkies` applied to
    * `R1R2fp`, from `(x6Rows_of_open14 …).1` (the term TailZ23 uses for gen 9's `r1r2`);
    * T5, from `AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed`;
    * the research field `r.elkiesX6StarPrinted`;
  * `HSyn.SGRFold.openGlue7_of_nvLocalInertia`.
* **`ZInQKernel/OneProof/H/TailZ36.lean`** contains:
  * `structure OpenGlue8 : Prop`, with the one field `nvLocalInertia`;
  * `openGlue7_of_OpenGlue8 r t l g`, which sets `nvLocalInertia := g.nvLocalInertia` and
    `heckeSqrtBranchAny := SGRFold.heckeSqrtBranchAny_of_open29 r t l`;
  * `sixContactMin_of_open30 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17)
    (g : OpenGlue8)`.
* **Main** imports TailZ36 and calls `sixContactMin_of_open30` with `g : OpenGlue8`. One sentence was added to its
  docstring.

The build after B and C succeeded on the first try.

### 2.4 Hash guard (DumpCompact; VERIFIED)

scratch/sgr-fold/cmp_hashes_out.txt compares 16258 constants before with 16335 after:

* **Removed (15):** the 14 pruned field projections and `addedLeaves5_of_open6`.
* **New (92):**
  * 69 in SGRDirectNV and 6 in SGRDirectElkies. Both are now in Main's import closure; neither changed.
  * 4 in SGRFold.
  * 9 in TailZ36.
  * 2 each in TailO and TailX: the new projections `nvLocalInertia` and `heckeSqrtBranchAny`.
* **Changed (137):**
  * 122 bundle auxiliaries (`mk`, `rec`, `casesOn`, projections of the edited structures);
  * 14 conversions: `glue4_of_open6`, which is the edited consumer, `glue6_of_open7`, and 12 added-leaves
    conversions that lost an assignment;
  * `frozenTarget`, whose type changed in the `g` binder.

No stack theorem's hash changed. No other declaration changed.

### 2.5 Discharges

* **The fold's own check:** scratch/sgr-fold/Discharges.lean, with output in Discharges-output.txt. It reports
  "61 open hypotheses, 2173 theorems checked, 7 discharge one". These are the same seven discharges as before
  the fold, each still assuming its input. None comes from SGRFold, as expected: its theorems are fold plumbing.
* **The kit's control file:** scratch/contrib-kit/DischargesTest.lean's positive control `t1` assumed
  `QuotientP1Coordinate`, which is no longer open. It now uses `SGRDirect.NVLocalInertia`, and the docstring and
  the CONTRIBUTING.md sentence that name it were changed to match. Its rerun output
  (scratch/contrib-kit/DischargesTest-output.txt) reports "61 open hypotheses, 2176 theorems checked, 9 discharge
  one":
  * `t1` discharges `OpenGlue8.nvLocalInertia` and still assumes it;
  * `t3` discharges `cartierSmooth` but is flagged for `sorry`.

### 2.6 Ledgers

* **kinds.tsv:** the rows `added shimuraIntegralModelRep` and `glue quotientP1Coordinate` were removed. A new row
  `glue nvLocalInertia` (project glue, no flag, GLUE/GLUE) takes the old glue row's place. Its area issue is
  quotientP1Coordinate's (`elliotglazer/diophantine-z-q#37`); packet, label and tier are left empty for the
  integrator.
* **claims.tsv:**
  * The rows `quotientP1Coordinate` (p1-quot) and `shimuraIntegralModelRep` (sir-printed) were removed. **Those two
    host tasks now target fields that are gone.**
  * A row `nvLocalInertia` was added: nv-local, host task, `wip/nv-local`, held.
* **Regenerated:** `scripts/one_proof/OpenStatements.lean` rewrote open-statements.json (61 open hypotheses). Then
  `render_open.py` rewrote OPEN.md, pages-wanted.md, CONTRIBUTING.md and STATUS.md. `render_open.py --check`
  passes: "ok: 61 open hypotheses, all classified; 4 generated files up to date".
* **Not changed:**
  * No credits.tsv row was added. The table has only `proof` rows, and this fold proves no field.
  * frontier-crosswalk.tsv's H-84 row still maps to `quotientP1Coordinate`. Earlier folds also left removed fields'
    crosswalk rows in place.

## 3. The new field, rated

`SGRDirect.NVLocalInertia` (statement in `ZInQKernel/Contrib/OneProof/SGRDirectNV.lean`, copied verbatim into the
bundle's field type) is **not printed form: GLUE (project glue, commutative algebra)**.

* **What it says.** Let `E/ℚ(X)` be finite Galois of degree `< p`, with branch data in `S ∪ {∞}`, where `S ⊂ ℚ` is
  `p`-integral and pairwise distinct mod `p`. Let `b ∈ S` be such that every residue field of `E` over `X = b` is
  unramified at `p`. Then every inertia element of a prime over `pℤ[X]` has a conjugate in an inertia group of a
  prime over `X − b`.
* **Where it comes from.** It is h-b1 §3 Lemma NV step 3. rv-h-b1 §3 checked that step and found it holds as stated
  (as sgr-direct reports).
* **Why it is a consequence, and of what.** The argument (sgr-direct §4; SPECULATIVE until proved):
  * The closure of a vertical prime `q` is finite over `V(p)`, so it passes through a point `𝔓` over `(p, X − b)`,
    and `I_q ⊆ I_𝔓`.
  * Near `𝔓` the branch locus is `{p = 0} ∪ {X = b}`. This uses Zariski–Nagata purity (SGA 1 X 3.1; dimension 2 is
    proved in the chain, `PropTSGlue.PurityGlobalDim2`), `S` distinct mod `p`, and the rationality of the branch
    points.
  * The branch locus is a normal-crossings divisor, and the cover is tame along it because the degree is `< p`. So
    Abhyankar's lemma (SGA 1 XIII 5.3, UNVERIFIED) makes the strict henselization a quotient of
    `ℤ_p^{sh}[z^{1/n}, p^{1/n}]`.
  * The horizontal branch's residue field is then `k(p^{1/c})` with `c = [I_𝔓 : I_Q]`. If that field is
    unramified, `I_𝔓 = I_Q`.
* **Why it is not proposed as a LEAF.** No published statement has this form.
* **Hand test cases** are tabulated in sgr-direct §4; all agree with the statement.
* **Not vacuous.** Every hypothesis can hold: for example `ℚ(X)(√(pX))` with `b = 0`.

The parallel task nv-local is proving it in Lean.

## 4. What remains

* **The nv-local fold.** When nv-local proves `NVLocalInertia`, the field `OpenGlue8.nvLocalInertia` is discharged
  by autofold: H goes to 54 fields, strict 45/9, strictest 43/11. OpenGlue6 and OpenGlue7 keep carrying
  `nvLocalInertia` below the top; the conversion fills it with the proof.
* **Off-chain leftovers, kept as in earlier prunes:**
  * TailN's `glue4_of_open5` and the bundles `OpenAddedLeaves5` / `OpenGlue5` still use the old route;
  * TailZ34 still imports `Contrib.OneProof.ShimuraGoodReductionNoGuard`, which is now off the proof's closure;
  * TailZ40's docstring explains why `QMFamilyGroupLaw` was needed, citing the two removed fields. PruneScan still
    finds `mumfordGroupLaw` used, through gen 14's `*_iff_ab_gl` conversions (`x6Rows_of_open14`), which
    `heckeSqrtBranchAny_of_open29` also uses. Whether rigidity can now be dropped elsewhere was not examined.
* **The integrator still has to:**
  * set packet, label and tier for the kinds.tsv row;
  * decide what happens to the p1-quot and sir-printed host tasks, whose fields are gone;
  * record the fold in fold-queue.tsv and credits.tsv if wanted.

## 5. Files

* **Lean, new:**
  * `ZInQKernel/Contrib/OneProof/SGRFold.lean` (contributor file);
  * `ZInQKernel/OneProof/H/TailZ36.lean`.
* **Lean, edited:**
  * `ZInQKernel/OneProof/H/TailO.lean`, `TailX.lean` (step A and prune);
  * `TailZ4`, `Z13`, `Z17`, `Z18`, `Z22`, `Z23`, `Z24`, `Z26`, `Z30`, `Z31`, `Z34` (prune only);
  * `ZInQKernel/OneProof/Main.lean`.
* **Ledgers:** docs/one-proof/kinds.tsv and claims.tsv (rows); open-statements.json, OPEN.md, pages-wanted.md,
  CONTRIBUTING.md and STATUS.md (regenerated).
* **Kit:** scratch/contrib-kit/DischargesTest.lean (control `t1`) and its output.
* **scratch/sgr-fold/:**
  * `log.md`;
  * `autofold.json` (fold spec, with the new field's kind and flag);
  * PruneScan, DumpCompact, DeadCascade, cmp_hashes.py and prune_lib.py, copied from wip/prune-scan and wip/r6-nf;
  * `prune_sgr.py` and `prune_sgr_out.txt`;
  * the scan outputs for base, step A and after;
  * `hashes_before.txt`, `hashes_after.txt` and `cmp_hashes_out.txt`;
  * `frozenTarget_before.txt` and `frozenTarget_after.txt`;
  * `Discharges.lean` and `Discharges-output.txt`;
  * `build-base.txt`.
