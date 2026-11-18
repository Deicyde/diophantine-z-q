# d2a6b: A6 through the manuscript's Y₃ leaf; the D2/A6 reroute is count-neutral

Task d2a6b, 2026-11-17. Base: fork main f3402e89 (fold-b112: sz-raynaud, y3-route-a, bost-gr9 and carirr-refold
folded; top `HDec.HSyn.sixContactMin_of_open76`, TailZ83), merged into this branch after
`origin/wip/d2a6-reroute` (698c8c9e) and `origin/wip/y3-route-a` (6558e2ff). All merges were clean. Results log:
scratch/d2a6b/log.md.

Marks: **VERIFIED** means compiled or read in a named file in this repository. **STANDARD** means published, with an
exact reference. **SPECULATIVE** means judgement. Theorem numbers recalled from memory are **UNVERIFIED** (no
network). Model work, no human review.

## 1. Result

**Verdict: yes. A6 rides on `Y3RouteA.Y3FullThreeRepZ30`, so `shimuraIntegralModelRep` stays out of the bundle,
and the reroute is count-neutral.**

- **A6 and the kernel field's good reduction are proved from `Y3FullThreeRepZ30`.** The proofs are
  `D2A6.hasGoodReduction_of_z30` and its readers in the new file `ZInQKernel/Contrib/OneProof/A6Z30.lean`. The two
  steps are diophantine_zq.tex L529-530 (used at L557-558, L752-753 and L781). They need no step outside the
  manuscript except textbook facts that are proved in Lean, and no new leaf (§2).
- **`SGRSplit.ShimuraIntegralModelRep` is absent** from the closure of the new top theorem
  `HDec.HSyn.sixContactMin_of_open77`. So are the SGA 7 IX 3.5 row and R6. VERIFIED, §4.
- **The fold** is a bypass built on TailZ83 (scratch/d2a6b/BypassFold.lean). It removes
  `sga7_IX_3_5_ForwardGeom_Def34`, adds `elliotWildInertiaTrivial` (ELLIOT, L817-818), and maps the two fields that
  are already in the bundle:
  - `silverbergZarhinThm35`, which gives `raynaudSemistableSHOr` (d2a6-reroute's Known issue 5);
  - `y3FullThreeRepZ30`, which gives `y3FineModuliAbP` and, through `R6U`, A6.
- **Every new theorem uses only `propext`, `Classical.choice` and `Quot.sound`**, including the top theorem
  `sixContactMin_of_open77`. Nothing imports `ZInQKernel.OneProof.Main`.

**Count** (docs/one-proof/kinds.tsv of f3402e89, H rows, computed by autofold.py's `counts`; the new row is rated by
`render_open.must_be_glue`):

| | fields | strict LEAF / GLUE | strictest LEAF / GLUE |
|---|---|---|---|
| f3402e89 before (`OpenResearchLeaves57`, TailZ83) | 29 | 5 / 24 | 5 / 24 |
| after this fold (`OpenResearchLeaves58`, BypassFold.lean) | 29 | 5 / 24 | 5 / 24 |
| for comparison: d2a6-reroute on TailZ79, A6 on `shimuraIntegralModelRep` | 30 | 5 / 25 | 5 / 25 |

- **Removed:** `sga7_IX_3_5_ForwardGeom_Def34` (GLUE: consequence, pending review).
- **Added:** `elliotWildInertiaTrivial` (GLUE: ELLIOT consequence).
- **Mapped, no new row:** `silverbergZarhinThm35` and `y3FullThreeRepZ30`.

On f3402e89, y3-route-a's autofold (`y3FineModuliAbP` → `y3FullThreeRepZ30`) is already folded (TailZ82), so "this
base alone" and "combined with y3-route-a's autofold" are the same base. Fold-b112 found each of its folds
count-neutral, at 5/24 on 29. **Net effect of this task: one SGA 7 row (GLUE) is traded for the manuscript's own
sentence (GLUE). No `--allow-rise` is needed.**

## 2. A6 on `Y3FullThreeRepZ30` (Step 1; VERIFIED by reading and compiling)

### 2.1 What A6 took from `ShimuraIntegralModelRep`, and what `Y3FullThreeRepZ30` gives

d2a6-reroute's `hasGoodReduction_of_intModel` uses its leaf at one prime `p`, and only in four ways:
1. the universal property at the single base `Spec K` (`K ⊇ ℚ` a field, so locally noetherian), applied to the object
   `qml3AsQMAb_of PK`;
2. properness of the model, used through the valuative criterion;
3. the universal family's group law and the properties proper, smooth and geometrically connected;
4. uniqueness of maps to the base.

The table compares this with what `Y3FullThreeRepZ30` provides:

| need | `ShimuraIntegralModelRep` (sgr-split) | `Y3FullThreeRepZ30` (y3-route-a, L473-477) | bridge |
|---|---|---|---|
| base | `ℤ_(p)` for each `p > 324` | `ℤ[1/30]` | `z30ToLocal`: `ℤ[1/30] → O` when some prime `p ∤ 30` is not a unit of `O` (proved). Every `p > 324` satisfies `p ∤ 30` (`not_dvd_thirty_of_lt`, proved). |
| objects | `QMAbScheme`: kernel-form level structure, injective on field fibres | `QMAbSchemeP`: printed form, a bijection `𝒪/3𝒪 ≅ A_s[3]` at geometric points | Over a `ℚ`-scheme, `Y3Fix.ofKer` turns kernel form into printed form, using `mumfordTorsionAlgClosed_proof` (already proved in the tree). `Y3Fix.toKer` goes back on any base (already proved; same `QMFamily`). A6 needs the first only at `Spec K`, which is a `ℚ`-scheme. |
| universal property | on locally noetherian `ℤ_(p)`-schemes | on locally noetherian `ℤ[1/30]`-schemes | `Spec K` is a `ℤ[1/30]`-scheme through `z30To K` |
| properness, family | proper and smooth; family proper, smooth, geometrically connected, a group | the same | none |
| maps to the base unique | `Spec ℤ_(p)` | `Spec ℤ[1/30]` | `spec_to_Z30_ext` (proved) |
| polarization | none (relative Lemma P pending) | none (the same relative-Lemma-P point) | none: A6 needs no polarization |

The lead asked whether the `ℤ[1/30]` model "gives more than stated". It does, in two ways:
- **More primes.** It gives good reduction at every `p ∤ 30`, while L529-530 claims it only outside `S`. Since
  `S ⊇ {p ≤ 324} ⊇ {2, 3, 5}` (L383-384), the manuscript's `S` is covered.
- **One model.** It is a single model, where sgr-split had a separate model for each `p`.

### 2.2 The proofs (`ZInQKernel/Contrib/OneProof/A6Z30.lean`, new)

- **`D2A6.hasGoodReduction_of_z30`.** It takes `Y3FullThreeRepZ30`, an object `PK : QML3 K` with `K ⊇ ℚ`, a
  valuation subring `O ⊆ K`, and a prime `p ∤ 30` that is not a unit of `O`. It concludes
  `PkgI2.HasGoodReduction (toGrp PK.A) O`. This is d2a6-reroute's proof with the bridge of §2.1:
  1. The classifying point `g : Spec K → 𝒴` comes from the fine moduli property, applied to the object made printed
     by `ofKer`.
  2. The lift `ℓ : Spec O → 𝒴` comes from Mathlib's valuative criterion (`IsProper.eq_valuativeCriterion`), using
     `z30ToLocal`. The square commutes by `spec_to_Z30_ext`.
  3. The abelian scheme is `ℓ^*𝒜`. Base change preserves proper, smooth and geometrically connected.
  4. Its generic fibre is `g^*𝒜 ≅ PK.A`, by pasting the pullback squares. The isomorphism is a homomorphism by the
     kernel's proved rigidity `MulRigidity.isMonHom_of_geometricallyIntegral`.
- **`HDec.D2A6.qmModelG3U_of_z30` and `HDec.D2A6.modelG3G6_of_leavesU_z30`** are the A6 readers. They are
  d2a6-reroute's `qmModelG3U_of` and `modelG3G6_of_leavesU`, with `p > 324 ⇒ p ∤ 30`.
- **Helpers:** `spec_to_Z30_ext`, `z30To`, `not_dvd_thirty_of_lt`, `z30ToLocal`.

**`D2A6Wrap.lean` (edited)** now sets `R6U := SZRaynaud.RaynaudWildNF ∧ Y3RouteA.Y3FullThreeRepZ30`.
`modelG3G6_of_leaves3U` and the kernel field's reader `good_of_QML3U` call the `z30` theorems.
`A6IntModel.lean` is kept: A6Z30 imports its helpers (`eta_pullback_fst`, `isUnit_of_not_dvd`, `goodRedTorsionT`,
`T324_subset_T`). Its `hasGoodReduction_of_intModel` is no longer on the live path.

**Provenance of the new steps:**
- **The bridge kernel form ↔ printed form** (`ofKer`/`toKer`) is not in the manuscript, which has only the printed
  notion (L449-453). It is a dictionary between two Lean encodings, already proved in the tree. It is on the spot
  (provenance (c)) and proved, so it adds no field.
- **The valuative criterion** (Mathlib) and **rigidity** (Mumford, *Abelian varieties*, §4 Cor. 1, locator
  UNVERIFIED; proved in the kernel) are textbook facts, proved.
- **`z30ToLocal` and `spec_to_Z30_ext`** are elementary and proved.

No uncited step was left unproved, so the stop condition of the task did not apply.

## 3. Chain and bypass, regenerated on f3402e89 (Step 2)

- **Taint** (`TaintD.lean`, `TaintD2.lean`, rerun on `sixContactMin_of_open76`; closure 274,529 constants):
  - IX 3.5: 101 tainted declarations; Cor. 3.3: 96.
  - 31 carriers. bost-gr9 had copied the research bundles from `OpenResearchLeaves53` down to `8EB` into
    `HDec.HSyn.GR9` under the same short names. These copies now carry the IX 3.5 field, so `gen_chain.py` matches a
    carrier's file by its namespace.
- **The chain's top is moved to TailZ80's `sixContactMin_of_open73`** (bundle `OpenResearchLeaves54`). TailZ81-83 are
  only field-by-field conversions:
  - `raynaudSemistableSHOr` comes from SZ 3.5;
  - `y3FineModuliAbP` comes from `y3FullThreeRepZ30`;
  - `carayolThmAIrr` comes from `carayolThmAFrob`.

  So the bypass maps the new bundle directly to `OpenResearchLeaves54U`, making those three conversions itself.
- **`ZInQKernel/Contrib/OneProof/D2A6Chain.lean`** (regenerated) has 103 declarations: 91 from TailZ80's GR9 chain,
  25 from EichlerBoundCopy, 9 from TailH and 7 from HomFree Consumers (scratch/d2a6b/gen/copied.txt). It also has 29
  structures. The edits are the same as d2a6-reroute's: R6 becomes `R6U`, the three IX 3.5 fields become `r6u`, the
  R6 producer becomes `r.r6u`, and the five terminal readers become the wrappers. The top is
  `sixContactMin_of_open73_u`.
- **`gen_bypass.py --mode post`** writes scratch/d2a6b/BypassFold.lean and kinds-rows.tsv:
  - **`OpenResearchLeaves58`** has 27 fields: `sga7_IX_3_5_ForwardGeom_Def34` is replaced by
    `elliotWildInertiaTrivial`.
  - **`openResearchLeaves54U_of_OpenResearchLeaves58`** sets
    `r6u := ⟨raynaudWildNF_of_leaves sz elliot (Néron from neronSchemeExtensionDedekind), n.y3FullThreeRepZ30⟩`,
    `raynaudSemistableSHOr := raynaudSemistableSHOr_of_sz35 n.silverbergZarhinThm35` (mapped, not replaced),
    `y3FineModuliAbP := y3FineModuliAbP_of_z30 n.y3FullThreeRepZ30` and
    `carayolThmAIrr := carayolThmAIrr_of_frob n.carayolThmAFrob`.
  - **`sixContactMin_of_open77`**.

**For the integrator:**
1. Copy BypassFold.lean to `ZInQKernel/OneProof/H/TailZ84.lean`.
2. Switch Main to `OpenResearchLeaves58` / `sixContactMin_of_open77`.
3. In kinds.tsv, replace the `sga7_IX_3_5_ForwardGeom_Def34` row with the row in scratch/d2a6b/kinds-rows.tsv, and
   drop the claims row of the removed field.

The generators write nothing under ZInQKernel/OneProof/ or docs/.

## 4. Checks (all VERIFIED in this worktree)

| check | outcome | file (scratch/d2a6b/) |
|---|---|---|
| `lake build` TailZ83, D2A6Wrap | success; `sixContactMin_of_open76` standard | (log) |
| `lake build ZInQKernel.Contrib.OneProof.D2A6Chain` | success; `sixContactMin_of_open73_u`: [propext, Classical.choice, Quot.sound] | build-chain.txt |
| `lake env lean BypassFold.lean` | 0 errors, 0 warnings; `sixContactMin_of_open77`: [propext, Classical.choice, Quot.sound] | bypass-out.txt |
| closure of `open77` (274,360 constants) | **absent:** `SGA7_IX_3_5_ForwardGeom_Def34`, `SGA7_IX_3_5_ForwardGeom`, all `RaynaudCriterionNF`, `QML3.goodReduction`, `raynaudPlace_of_R6`, `torsFix_of_descent`, `modelG3G6_of_leaves3`, `good_of_QML3`, **`SGRSplit.ShimuraIntegralModelRep`**, `sorryAx`. **Present:** `RaynaudWildNF`, `ElliotWildInertiaTrivial`, `SilverbergZarhinThm35`, `Y3FullThreeRepZ30`, `SGA7_IX_Cor3_3_Def34`. **Control (`open76`):** the old statements present | ClosureCheck.lean, closurecheck-out.txt |
| `#print axioms` of 34 theorems (D2WildNF 12, A6IntModel 10, D2A6Wrap 5, A6Z30 6, chain top 1) | all [propext, Classical.choice, Quot.sound] | Discharges.lean, discharges-output.txt |
| `#discharges` (Main of f3402e89 + D2A6Chain) | 150 lines. 135 are projections of the copied `…U` structures (noise). The other 15 are conditional discharges already on the base (`carayolThmAFrob`, `dsThm965Printed`, `deRhamVpAbVarDirect`, `pazukiCor13Upper`, `hodgeTateDecompOr`, …), none for this task's fields. The bypass cannot be written as a discharge | discharges-output.txt |
| PruneScan (Step 3) | see §5 | prunescan-out.txt, prunescan-summary.txt |
| strict dry run (Step 4) | see §6 | strict-dryrun-f3402e89.txt |

## 5. PruneScan (Step 3; d2a6-reroute's Known issue 7)

pi0-fold's scan, regenerated by gen/gen_prunescan.py as PruneScanBypass.lean, ran on two roots: the base top
`open76` and the bypass top `open77` (9 min 21 s).
- **Top-level fields.** Every field of the bundle (27 research + 0 textbook + 2 added) is USED in both, and the prune
  set is empty in both.
- **The live chain.** Each copied bundle (`…U`) has exactly the unused fields of its original in the base. Examples:
  `GR9.OpenResearchLeaves14GMEBU` has `[egaIV_8_10_5_openImm]`, `OpenResearchLeaves2EBU` has `[r1rec, r5]`, and
  `ResearchLeaves3EBU` has `[r1rec, r4, r5, r5count, r6, r7a]`. **No field lost its last reader through the
  reroute.**
- **`mulEtaleAbelianScheme`** is a field only of the old textbook generations `OpenTextbookLeaves7`-`10`. It is unused
  in the base and in the bypass alike. On this base the live textbook bundle `OpenTextbookLeaves18` has no fields:
  the dropped R6 producer's input is supplied by a Contrib proof, not by a field. Nothing to prune.

## 6. Strict dry run (Step 4)

**No field is discharged outright on f3402e89.** On TailZ79 the fold had two outright discharges:
`raynaudSemistableSHOr` from `silverbergZarhinThm35`, and y3-route-a's `y3FineModuliAbP`. Both are folded on this
base (TailZ81, TailZ82). This base's strict `scripts/one_proof/autofold.py` (line 202 calls
`render_open.must_be_glue`) now refuses the old spec with "not a field of the current bundles: [raynaudSemistableSHOr,
y3FineModuliAbP]" (strict-dryrun-f3402e89.txt).

The removal of `sga7_IX_3_5_ForwardGeom_Def34` is a bypass, not an autofold. Its count comes from `gen_bypass.py`,
which imports autofold.py and uses its `counts`, `flag_class` and `render_open.must_be_glue`, as well as
`render_open.kinds_row_problems` (no problem reported): 5/24 on 29 → 5/24 on 29 under both strict and strictest.

The TailZ79 dry runs from this task's first pass are archived in scratch/d2a6b/tailz79/ (5/24 → 5/24, compiled
then).

## 7. Leaves and kinds rows

| field | status | provenance | kind / strict / strictest | flag |
|---|---|---|---|---|
| `elliotWildInertiaTrivial` (`SZRaynaud.ElliotWildInertiaTrivial`) | new in the bundle; the statement is sz-raynaud's | (a) ELLIOT: the uncited sentence of diophantine_zq.tex L817-818 | consequence / GLUE / GLUE | ELLIOT (tex 817-818); true and standard (SGA 7 I Exp. IX Prop. 3.5, number UNVERIFIED, with wild inertia pro-p) |
| `y3FullThreeRepZ30` | already a field (TailZ82); now also read by A6 and the kernel field | (a) ELLIOT: the manuscript's own conclusion L473-477 | consequence / GLUE / GLUE (unchanged) | unchanged (y3-route-a's row) |
| `silverbergZarhinThm35` | already a field (TailZ81); now also read by D2 through `RaynaudWildNF` | (b) cited print: Silverberg–Zarhin Thm 3.5, cited at L816; bibliography L11077 | published / LEAF / LEAF (unchanged) | unchanged |

The kinds row is scratch/d2a6b/kinds-rows.tsv, one row: `elliotWildInertiaTrivial`, taking the bundle, packet and
area of the removed row. No leaf was added on the spot.

## 8. Manuscript check

One line per manuscript step that this work formalizes or relies on (diophantine_zq.tex).

- **L383-384** (`S` contains every prime `≤ 324`): **OK**. Used as `T324 ⊆ T(u)`, and `S ⊇ {2, 3, 5}`, so the
  `ℤ[1/30]` model covers every place outside `S`.
- **L443-446** (Buzzard Thm 2.1 / Cor. 2.3 applied to `V₁(5)` over `ℤ[1/30]`): **unverified**. Buzzard is in the
  bibliography (L11031), but the print was not read (locator UNVERIFIED). It enters only inside the ELLIOT leaf `y3FullThreeRepZ30`.
- **L447-453** (full five-marking; the finite étale sheaf `Isom_𝒪(𝒪/3𝒪, A[3])`): **unverified**. Not formalized; part
  of the leaf.
- **L453-462** (`𝒪₃`-stable lattices in a rank-one `B₃`-module are principal, so the sheaf is nonempty): **OK**,
  checked by hand. Take `x` of least valuation. For `y` in the lattice, `y x⁻¹ ∈ 𝒪₃`, so `y ∈ 𝒪₃ x`, and "divide on
  the right" is correct for a left module. Hence `T₃/3T₃ ≅ 𝒪/3𝒪`.
- **L464-472** (`G₅` acts freely because `1 + 3M₄(ℤ₃)` is torsion-free): **unverified**.
  - The torsion-freeness is **OK**, checked by hand: for `g = 1 + 3^k X` with `X ≢ 0 mod 3` and `k ≥ 1`, we get
    `g^q ≡ 1 + q·3^k X (mod 3^{k+1})` for `q ≠ 3`, and `g³ ≡ 1 + 3^{k+1} X (mod 3^{k+2})`.
  - Unverified is "a polarized automorphism": the polarization's source in Buzzard's unpolarized problem is
    y3-route-a's issue 2 (relative Lemma P, a gap of exposition).
- **L472-477** (the quotient `X₃₅/G₅` represents the full-three problem, and its generic fibre is `Y₃`):
  **unverified**. Stated as the ELLIOT leaf `y3FullThreeRepZ30`, without polarization. The identification with the
  Shimura curve uses the canonical-model leaf (y3-route-a's issue 3).
- **L529-530** ("The proper model and its universal abelian scheme give good reduction outside the places over `S`"):
  **gap filled**. The manuscript gives no argument. A6Z30.lean proves it from the model: the classifying point, the
  valuative criterion, base change of the universal abelian scheme, and the generic fibre identified by rigidity. It
  also needs the bridge from the kernel's level structure to the printed one (`ofKer`, which uses the
  proved `mumfordTorsionAlgClosed`), on the spot and proved.
- **L557-558** ("every conjugate has good reduction" outside `T`): **OK**. It is the same theorem applied to each
  conjugate (`good_of_QML3U`).
- **L752-753, L781** (`A` has good reduction away from `T ∪ {ℓ}`, and at `p`): **OK**, as uses of L529-530.
- **L814-816** (`F = L_v(A[3])`, with `A[5]` if `p = 3`; Raynaud's criterion as Silverberg–Zarhin Thm 3.5):
  **OK**. The citation was read by sz-raynaud. `n = 3` or `5` is prime to `p` in each case.
- **L817-818** ("Its wild inertia acts trivially on each `V_ℓ(A)` with `ℓ ≠ p`"): **gap filled (citation)**. The
  sentence is uncited. It is true and standard (SGA 7 IX Prop. 3.5, number UNVERIFIED, with wild inertia pro-`p`;
  sz-raynaud proved it from those, `SZRaynaud.elliot_of_semistableUnipotent`). It is the ELLIOT leaf
  `elliotWildInertiaTrivial`.

**No manuscript error was found.**

## 9. Known issues

1. **`ReductSplit.SemistableUnipotent._proof_2`**, an elaborator auxiliary proof term, is still in the closure of
   `open77`. The statement `SemistableUnipotent` itself is absent. This is harmless; it is d2a6-reroute's issue 6.
2. **`#discharges` noise.** The 135 projection lines of the copied structures are noise, as in d2a6-reroute.
3. **Cor. 3.3 stays** (`sga7_IX_Cor3_3_Def34`). Its readers are the semistable persistence steps behind the height
   rows (d2a6-reroute §4). This task does not touch them.
4. **The relative Lemma P (polarization)** is still the open reading point shared by `y3FullThreeRepZ30`. A6 does not
   need a polarization.
5. **The chain is a verbatim copy.** If another fold changes a carrier below TailZ80 or the GR9 copies, rerun
   TaintD.lean, TaintD2.lean, gen_chain.py and gen_bypass.py, in that order. The generators stop at a missing edit
   target. gen_bypass's `absorb`/`add` modes were for the TailZ79 base and no longer apply.
6. **Large text outputs** (taintD-out.txt, taintD2-out.txt, unused-all-*.txt) are committed for review, as by the
   predecessor. The build logs were trimmed to their result lines.

## 10. Files

- **`ZInQKernel/Contrib/OneProof/`**:
  - `A6Z30.lean` (new);
  - `D2A6Wrap.lean` (edited: `R6U` on `Y3FullThreeRepZ30`);
  - `D2A6Chain.lean` (regenerated on TailZ80);
  - `D2WildNF.lean` and `A6IntModel.lean` (d2a6-reroute's, unchanged).

  None imports `ZInQKernel.OneProof.Main`.
- **`scratch/d2a6b/`**:
  - log.md;
  - gen/ (copylib.py, gen_chain.py, header.lean, gen_bypass.py, gen_goodred.py, gen_prunescan.py,
    prunescan_tail.lean, copied.txt);
  - TaintD.lean, TaintD2.lean and their outputs;
  - BypassFold.lean, bypass-out.txt, kinds-rows.tsv;
  - ClosureCheck.lean, closurecheck-out.txt;
  - Discharges.lean, discharges-output.txt;
  - PruneScanBypass.lean, prunescan-out.txt, prunescan-summary.txt, used-fields-*.txt, unused-all-*.txt,
    prune-set-*.txt;
  - strict-dryrun-f3402e89.txt;
  - build-a6z30.txt, build-chain.txt;
  - tailz79/ (the first pass, on TailZ79).
