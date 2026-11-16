# r6-nf: `neronSchemeModelExistsDVR` (BLR 1.4/3 over every DVR) removed from `ZInQ.OneProof.frozenTarget`; r6 restricted to number fields, dead r8 pruned

Task r6-nf, 2026-11-15. Base 9a100aa7 (origin/wip/leaf-fold22b; `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open28`, 56 bundle fields), merged with origin/wip/neron-dvr 998fa5b5 (contributor file
`ZInQKernel/Contrib/OneProof/NeronDVR.lean`, docs/research/neron-dvr.md). The consumer list applied here is
neron-dvr.md §3.3. Results log: scratch/r6-nf/log.md. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement.

## 1. Main result

**`frozenTarget` loses `OpenResearchLeaves21.neronSchemeModelExistsDVR : ReductSplit.NeronSchemeModelExistsDVR`
(BLR, *Néron models*, §1.4 Thm 3 over an arbitrary DVR, scheme form) and gains nothing.** VERIFIED:
* `lake build +ZInQKernel.OneProof.Main` succeeds (12985 jobs);
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
* the type of `frozenTarget` prints identically before and after (scratch/r6-nf/frozenTarget_before.txt,
  frozenTarget_after.txt); only `OpenResearchLeaves21` has one field fewer;
* PruneScan finds 0 unused fields among the remaining 55.

| | H fields | strict (kinds.tsv, H rows) | strictest | all rows of kinds.tsv (with the 7 `frozenTarget` Props) |
|---|---|---|---|---|
| before (9a100aa7) | 56 | 46 LEAF / 10 GLUE | 45 / 11 | strict 49 / 14, strictest 48 / 15 |
| after | **55** | **45 / 10** | **44 / 11** | strict 48 / 14, strictest 47 / 15 |

The field was LEAF in both readings, so only the LEAF counts drop (fields −1, LEAF −1, as expected). claims.tsv has
no row for it, so it is unchanged. Only its kinds.tsv row was deleted.

**Why the field is not needed** (VERIFIED by the compiled chain). It had three uses (neron-dvr.md §3.1):
1. SS1/SS3 (`ss1_ss3_of14`);
2. r6, through `ReductGlue.raynaudCriterion_leaves`;
3. r8, through `ReductSplit.grothendieckMonodromy_final'`.

What replaced each use:
* **r8 was dead.** `PkgI2.GrothendieckMonodromy` was only copied between bundles. It is pruned from every generation
  (§1.2, step 1).
* **r6 is applied only at number fields.** It now has the type `PkgI2.RaynaudCriterionNF` in the old bundles, and its
  consumers are restated at number fields.
* **SS1/SS3 use the field only at number fields.** Both r6 and SS1/SS3 now come from neron-dvr's
  `GapNeron.neronSchemeModelExistsNF`. That theorem proves the number-field form of the Néron field from the
  textbook field N1 (`neronSchemeExtensionExists`, BLR 1.4/3 over the Dedekind ring 𝓞_L), which the bundle keeps.

So BLR's existence theorem is used only over rings of integers of number fields, through N1 and gt-blr's proved
localization (`GapBLR.neronLocalizesDVR_proved`).

### 1.1 The plumbing (compiled before the deletion of the top field)

The rules followed:
* a consumer's signature changes only by replacing `PkgI2.RaynaudCriterion.{0}` (or `ObjBridge.RaynaudCriterion`,
  the same statement by `Iff.rfl`) with `PkgI2.RaynaudCriterionNF.{0}`, and by adding `[NumberField K]` where R6 is
  applied at `K`;
* bundle fields `r6` are retyped in the same way;
* new binders carry r6 and SS1/SS3 up to the first module that can import NeronDVR.

No other field statement changes. Restricting R6 to number fields weakens a hypothesis, which is allowed;
`frozenTarget` and its binders are unchanged.

* **The definition.** `HDec.PkgI2.RaynaudCriterionNF.{u}` (LPrefix, before `goodReduction_of_QM_rational3_of_alg`):
  `PkgI2.RaynaudCriterion` (HDecomp/Objects.lean L1436) verbatim, with `[NumberField K]` added. Universe-polymorphic,
  so the polymorphic A6 theorems keep their universe. At `.{0}` it is the statement of neron-dvr's
  `GapNeron.RaynaudCriterionNF`, and the elaborator accepts `GapNeron.raynaudCriterion_leavesNF …` at this type with
  no conversion (VERIFIED, TailZ26 compiles). The definition had to live in LPrefix: the bundles in TailD–TailZ9
  carry it, and NeronDVR comes after TailZ24. A helper `PkgI2.raynaudCriterionNF_of_general :
  RaynaudCriterion.{u} → RaynaudCriterionNF.{u}` is used only off the chain (TailD `researchLeaves3_of`, TailZ15
  `researchLeaves9_of_open10`).
* **Application sites** (`[NumberField K]` added):
  * LPrefix `PkgI2.goodReduction_of_QM_rational3_of_alg` (`hRay K O w hw A 3 …`, where R6 is applied),
    `goodReduction_of_QM_rational3` and `goodReduction_of_QM_rational3'`;
  * `LeafQM.AV.QML3.goodReduction`, where `[CharZero K]` is replaced by `[NumberField K]` (`CharZero` follows).
  * Its two callers:
    * TailC `good_of_QML3` already had `haveI : NumberField K`;
    * TailF `LinkedTate.qmModelG3_of` now builds the instance. `K ≤ L ≤ L'` with `L'/ℚ` finite, so
      `FiniteDimensional ℚ K` follows from `Module.Finite.of_injective` along `IntermediateField.inclusion`, and then
      `NumberField K := ⟨⟩`.
  * TailH `G15Ram.raynaudPlace_of_R6` (`hR6 F O₁ …`, `haveI : NumberField F` was in scope) and
    `G15Ram.raynaudPlace_rational` (the section variable `[NumberField K]`).
* **Binder retyped only (pass-through):**
  * TailC: `kernelFieldExists_of_{pieces, leaves, leaves_FS5, split, split', split'', final, final', rigidity}`;
  * TailF: `kernelFieldExists_of_{five, semilinear, twist, descent, kerUnitOpen, kerUnitOpen', mulIsogeny}`;
  * TailI: `modelG3G6_of_leaves3`, and `linkedTateLocal_of_leaves3`, where `ObjBridge.raynaudCriterion_iff.mpr hR6`
    became `hR6`;
  * TailH: `G15Ram.{tateWildK_of_R6, localGlue_of_leaves, torsFix_of_descent, torsFixWildOdd_of_descent,
    torsFixWildE_of_twist, tateWildKE_of_descent, localGlue_of_descent, localGlue_of_unramRoots,
    localGlue_of_baseChange}`, `G0ModNewform.{g7LocalPackK_of_R, g15RamG_of_packR, g8LocalPack_of_D,
    g15RamG_of_packD, g8LocalPack_of_U, g15RamG_of_packU, g8LocalPack_of_BC, g15RamG_of_packBC}`,
    `LGKerWild.{localGlue_of_transport, localGlue_of_tateBridge35, localGlue_of_kerWild,
    exists_localGlue_of_tateBridgeK, exists_localGlue_of_tateModuleFree}` and `LTLocal.{localGlue_at,
    linkedTateLocalD_of_tateBridge35, linkedTateLocalD_of_tateBridge35', linkedTateLocal_of_tateBridge35,
    linkedTateLocal_of_algFrobRed}`;
  * TailM: `raynaudCriterion_ofK5`, now `RaynaudCriterionNF → RaynaudCriterionNF`.

  Some of these are off the chain. They pass `hR6` to retyped theorems, so they were retyped too, rather than given
  coercions.
* **Bundles.** `r6 : PkgI2.RaynaudCriterionNF.{0}` in `ResearchLeaves3` (TailD), `OpenResearchLeaves2` (TailE), `5`
  (TailN), `7` (TailX), `8` (TailZ4) and `9` (TailZ9). The bundle maps between them are unchanged in text (`r6 :=
  r.r6`, `r6 := raynaudCriterion_ofK5 r.r6`). The older off-chain bundles `ResearchLeaves`, `OpenResearchLeaves`
  (LPrefix) and `OpenResearchLeaves10`–`13` keep the general form; their maps into the retyped bundles use
  `raynaudCriterionNF_of_general`. TailK `gluePieces_of_open4` reads `OpenResearchLeaves2.r6` with its text unchanged.
* **Supply and threading.** NeronDVR imports BLRLocalizes, which imports TailZ24, so its theorems cannot be called in
  TailZ23. That is where r6 and SS1/SS3 were produced (`researchLeaves9_of_open14`).
  * TailZ26 already imported BLRLocalizes. It now also imports `ZInQKernel.Contrib.OneProof.NeronDVR`, which brings no
    other new module.
  * `researchLeaves9_of_open14` takes `(h6 : PkgI2.RaynaudCriterionNF.{0}) (hSS : SemistableReductionThm ∧
    SemistablePersists)` and sets `r6 := h6`, `semistableReductionThm := hSS.1`, `semistablePersists := hSS.2`.
  * `sixContactMin_of_open17` (TailZ23), `_open18` (TailZ24) and `_open19` (TailZ25) take the same two binders after
    `hYu` and pass them down.
  * `sixContactMin_of_open20` (TailZ26) supplies them from its own bundles, converted down to generation 14
    (`openResearchLeaves14_of_OpenResearchLeaves15 ∘ openResearchLeaves15_of_OpenResearchLeaves16`,
    `addedLeaves12_of_open13 ∘ openAddedLeaves13_of_OpenAddedLeaves14`), through two new helpers in TailZ26:
    * `HSyn.raynaudCriterionNF_of14 r t := GapNeron.raynaudCriterion_leavesNF (raynaudSemistable_of14 r t)
      r.semistableUnipotent (GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
      t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme`;
    * `HSyn.ss1_ss3_of14NF r t l`, the §3.2 reroute verbatim: `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp
      r.strictHenselizationPair (semistableReductionDVR_of14 r t) (GapNeron.neronSchemeModelExistsNF
      t.neronSchemeExtensionExists) (semistableLocalGlobal_leaf (neronLocalizesDVR_of_printed r.blr_1_2_4))
      (semistableAlmostAll_of10 (addedLeaves9_of_open14 r t l))`.

    `open20`'s type is unchanged, and so are `open21`–`open28` and `frozenTarget`. Folds that build on `open28`
    therefore merge without signature conflicts.

After steps 1 and 2, the build succeeded on the first try. PruneScan then reported exactly
`OpenResearchLeaves21.neronSchemeModelExistsDVR` UNUSED. Its prune set is the same field in `OpenResearchLeaves14`–`21`
(8 FIELD lines, no constants; scratch/r6-nf/prune-set-step2.txt). DeadCascade reports `ss1_ss3_of14` (TailZ23) as the
only dead reader, plus the generated `casesOn`/`recOn`.

### 1.2 The prune (deletions only; every deleted line in scratch/r6-nf/prune_r8_out.txt and prune_neron_out.txt)

**Step 1, r8** (scratch/r6-nf/prune_r8.py). Already marked unused by the base PruneScan (unused-all-base.txt):
* the field `r8 : PkgI2.GrothendieckMonodromy.{0}` in `ResearchLeaves3`, `OpenResearchLeaves2`, `5`, `7` and `8`;
* the three `OpenResearchLeaves9` fields that fed only r8: `semistableReductionDVR`, `semistableUnipotent` and
  `neronSchemeModelExistsDVR`;
* their 12 assignments:
  * `r8 :=` in `researchLeaves3_of`, `researchLeaves3_of_open2`, `researchLeaves2_of_open5`,
    `researchLeaves5_of_open7` and `researchLeaves7_of_open8`;
  * the two-line `r8 := grothendieckMonodromy_final' …` in `researchLeaves8_of_open9`;
  * the three fields' assignments in `researchLeaves9_of_open10` (off-chain) and `researchLeaves9_of_open14`.

**Step 3, the Néron field** (scratch/r6-nf/prune_neron.py):
* `neronSchemeModelExistsDVR` in `OpenResearchLeaves14` (TailZ23), `15` (TailZ25), `16` (TailZ26), `17` (TailZ27), `18`
  (TailZ28), `19` (TailZ29), `20` (TailZ33) and `21` (TailZ34);
* its 7 assignments in `openResearchLeaves14_of_…15` … `openResearchLeaves20_of_…21`;
* the dead reader `ss1_ss3_of14`.

**Kept** (as in earlier prunes, only the scan's set is removed):
* the off-chain generations `OpenResearchLeaves10`–`13` (TailZ15/17/19/22) keep their `neronSchemeModelExistsDVR`;
* LPrefix's `ResearchLeaves`/`OpenResearchLeaves` keep `r6`/`r8`;
* `r1rec` and `r5` stay unused in the old generations (pre-existing, not in this task's scope);
* the general producers `ReductGlue.raynaudCriterion_leaves`, `ReductSplit.grothendieckMonodromy_final'`,
  `HSyn.grothendieckMonodromy_ofK5` and the definition `ReductSplit.NeronSchemeModelExistsDVR` are still declared,
  off the closure.

## 2. Every hypothesis after the prune

The full statements are in docs/one-proof/OPEN.md (regenerated); the kinds are in docs/one-proof/kinds.tsv, given
as strict/strictest.

* **OpenResearchLeaves21 (28 fields)**, one fewer:
  * `babaGranathRationalAb` L/L
  * `bostLowerBound` L/L
  * `deRhamH1AbVarT` L/L
  * `dsThm965` L/L
  * `dsThm966` L/L
  * `eigenformHTNew` G/G
  * `elkiesX6StarPrinted` G/G
  * `faltingsLemma5Printed` L/L
  * `gaudronRemondThm14` L/L
  * `gonzalezRotgerProp56X6` L/L
  * `gonzalezRotgerX6Ab` L/L
  * `hodgeTateDecompAbVar` L/L
  * `javanpeykarBound` L/L
  * `mumfordRigidityCore` L/L
  * `neronBaseChangeStrictHenselization` L/L
  * `pazukiCor13Upper` L/L
  * `r11r12` G/G
  * `r16` G/G
  * `r17` G/G
  * `r7a` L/L
  * `r9a` L/L
  * `r9b` L/L
  * `raynaudSemistableSH` L/L
  * `semistablePersistsSHcp` L/L
  * `sga3_VIB_3_10` L/L
  * `sga7_IX_3_3_SH` L/L
  * `sga7_IX_3_5_ForwardGeom` L/L
  * `shimuraMainThmIDeligneY3AbU` G/G
* **OpenTextbookLeaves11 (12)**, all L/L and unchanged:
  * `cartierSmooth`
  * `charPolyIndepOfEllAlgClosed`
  * `gagaMorphism`
  * `geomConnOfRationalPoint`
  * `groupSchemeEquidim`
  * `homFreeFiniteAlgClosed`
  * `igusaGL2`
  * `mumfordTorsionAlgClosed`
  * `neronSchemeExtensionExists`
  * `poincareComplement`
  * `regularSmoothPerfect`
  * `uniformizationLeafAll`
* **OpenAddedLeaves17 (14)** and **OpenGlue7 (1)**: unchanged.
* The 7 non-bundle hypotheses of `frozenTarget` (`h11`, `h29`, `hCM`, `hX`, `h33`, `hL2`, `hL3`): unchanged.

## 3. The remaining leaves by the theory they come from

Unchanged from leaf-fold22, except the Néron-model group, which loses BLR §1.4 Thm 3 over an arbitrary DVR. The
existence of Néron models is now used only in the form N1 (over 𝓞_L, L a number field), together with the proved
localization BLR §1.2 Prop. 4 (gt-blr). STANDARD: N1 plus localization gives the Néron model over every DVR of a
number field. Neron-dvr formalized this, VERIFIED.

**Which SGA 7 strictly henselian leaves could now take their cp forms** (char 0, perfect residue field; not switched
here, per the task):
* **`raynaudSemistableSH`, likely (SPECULATIVE; the use sites are VERIFIED by reading).** It feeds
  `raynaudSemistable_of14`. That has two consumers:
  * r6, via `GapNeron.raynaudCriterion_of_leavesNF`, which applies `hR K O B m …` only at the number field `K`;
  * SS1, via `semistableReductionDVR_of14`. neron-dvr already compiled the cp variant of SS1/SS3,
    `GapNeron.ss1_ss3_of_cp_fullNF`, which takes `RaynaudSemistableSHcp`.

  A switch would need r6 restated over `RaynaudSemistableCP`/`SHcp`. Residue fields of number-field DVRs are finite,
  hence perfect.
* **`sga7_IX_3_5_ForwardGeom`, possible (SPECULATIVE).** It feeds `semistableUnipotent` (TailZ33,
  `UnipotentForward.semistableUnipotent_of_forwardGeom`). After the r8 prune, its only live consumer is r6, at
  `hU K O (AlgebraicClosure K) w …` with `K` a number field. Before this task, r8 also used it at every field.
* **`neronBaseChangeStrictHenselization`, partly.** It feeds `semistableUnipotent` (above) and `sga7_IX_3_3`. The
  latter goes to `semistableNeronBaseChange`, whose generality this task does not change.
* **`sga7_IX_3_3_SH`: not affected** by r6/r8. It feeds `sga7_IX_3_3` → `semistableNeronBaseChange` only.

## 4. Checks (all VERIFIED; one Lean process at a time)

* **Base (2a6b6c4b = 9a100aa7 + neron-dvr):**
  * `lake build +ZInQKernel.OneProof.Main` OK;
  * DumpCompact (scratch/r6-nf/DumpCompact.lean: every constant of a `ZInQKernel.OneProof` or
    `ZInQKernel.Contrib.OneProof` module in Main's environment) found 15646 constants (hashes_before.txt);
  * PruneScan: 0 unused of 56 (prunescan-base-out.txt).
* **After steps 1–2:** the build succeeded on the first try; the PruneScan result is in §1.1.
* **After step 3:**
  * `lake build +ZInQKernel.OneProof.Main` OK (12985 jobs);
  * `frozenTarget` has the standard axioms, and its type is identical to the base;
  * PruneScan: OpenResearchLeaves21 28, OpenTextbookLeaves11 12, OpenAddedLeaves17 14, OpenGlue7 1 = 55 fields,
    0 unused, prune set empty (prunescan-after-out.txt, used-fields.txt).
* **DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt): base 15646, after 15668.
  * **Removed 18:**
    * the 16 pruned projections: r8 ×5, `OpenResearchLeaves9.{semistableReductionDVR, semistableUnipotent,
      neronSchemeModelExistsDVR}`, and `OpenResearchLeaves14`–`21.neronSchemeModelExistsDVR` ×8;
    * the dead reader `ss1_ss3_of14`;
    * `HDec.LeafPush.R08_GrothendieckMonodromy._proof_3`. This is auxiliary-proof sharing: the new
      `HDec.PkgI2.RaynaudCriterionNF._proof_1`, earlier in LPrefix, has exactly the old `_proof_3`'s type hash
      (2207783599) and value hash (2490168942). `R08_GrothendieckMonodromy` now points to it, so it changes in value
      only.
  * **New 40:**
    * NeronDVR's 35 constants (the contributor module, now in Main's closure through the TailZ26 import);
    * LPrefix 3: `PkgI2.RaynaudCriterionNF`, its `_proof_1`, `PkgI2.raynaudCriterionNF_of_general`;
    * TailZ26 2: `HSyn.raynaudCriterionNF_of14`, `HSyn.ss1_ss3_of14NF`.
  * **Changed 327**, every one of the allowed kinds:
    * generated auxiliaries and projections of the edited bundle structures `ResearchLeaves3`,
      `OpenResearchLeaves2/5/7/8/9` and `OpenResearchLeaves14`–`21` (`mk`, `mk._flat_ctor`, `rec`, `recOn`,
      `casesOn`: type; projections after a deleted field: value). The `r6` projections of the six old bundles change
      in type, which is the retyping.
    * conversions, value only, by one deleted assignment:
      * `researchLeaves3_of`, `researchLeaves3_of_open2`, `researchLeaves2_of_open5`, `researchLeaves5_of_open7`,
        `researchLeaves7_of_open8`, `researchLeaves8_of_open9`, `researchLeaves9_of_open10`;
      * `openResearchLeaves14_of_…15` through `openResearchLeaves20_of_…21`.
    * `researchLeaves9_of_open14`: type, the new binders `h6` and `hSS`;
    * stack theorems:
      * `sixContactMin_of_open17`, `_open18`, `_open19`: type, the new binders;
      * `sixContactMin_of_open20`: value only;
      * `_open21`–`_open28` and `frozenTarget`: unchanged hashes.
    * edited consumers, all type changes:
      * LPrefix: `PkgI2.goodReduction_of_QM_rational3_of_alg`, `goodReduction_of_QM_rational3`,
        `goodReduction_of_QM_rational3'`, `LeafQM.AV.QML3.goodReduction`;
      * TailC: `good_of_QML3`, `kernelFieldExists_of_{pieces, leaves, leaves_FS5, split, split', split'', final,
        final', rigidity}`;
      * TailF: `kernelFieldExists_of_{five, semilinear, twist, descent, kerUnitOpen, kerUnitOpen', mulIsogeny}`,
        `LinkedTate.qmModelG3_of`;
      * TailI: `modelG3G6_of_leaves3`, `linkedTateLocal_of_leaves3`;
      * TailM: `raynaudCriterion_ofK5`;
      * TailH: the 29 `G15Ram`/`G0ModNewform`/`LGKerWild`/`LTLocal` theorems of §1.1.
    * `HDec.LeafPush.R08_GrothendieckMonodromy`: value only, the auxiliary-proof sharing above.

    No other constant changed.
* **scratch/contrib-kit/DischargesTest.lean** (output in DischargesTest-output.txt): the same 7 discharges and controls
  as before (t1 still assumes `QuotientP1Coordinate`; t3 on `cartierSmooth` is flagged for `sorry`). The count is now
  62 open hypotheses (was 63).
* **Docs:**
  * `lake env lean scripts/one_proof/OpenStatements.lean` wrote 62 open hypotheses;
  * `render_open.py` reported "55 H hypotheses, strictest 44/11, 7 others";
  * `render_open.py --check` reported "ok".

  open-statements.json, OPEN.md, CONTRIBUTING.md and STATUS.md were regenerated and committed.
* FaithCheck was not needed: no HDec copy was deleted.

## 5. Not done, and why

* **Two places where the edit goes slightly beyond the letter of "How to edit"** (flagged for the integrator):
  * an import line added to TailZ26. It is needed because NeronDVR comes after TailZ24. NeronDVR's only import,
    BLRLocalizes, was already imported there, so no other module enters TailZ26's environment;
  * the definition `HDec.PkgI2.RaynaudCriterionNF` in LPrefix duplicates neron-dvr's `GapNeron.RaynaudCriterionNF`.
    The two are definitionally equal at `.{0}`, and the chain uses them interchangeably. The Contrib definition cannot
    be moved before TailD without editing NeronDVR.lean (a Contrib file). A later one-line change could make
    `GapNeron.RaynaudCriterionNF` an abbreviation of the HDec one.
* The SGA 7 SH leaves were not switched to cp forms (§3 lists the candidates).
* `neronSchemeModelExistsDVR` for DVRs of fields that are not number fields is not proved. The chain no longer needs
  it.
* `docs/one-proof/frontier-crosswalk.tsv` still has a row `H-148 neronSchemeModelExistsDVR`. That file is outside
  this task's allowed edits and is not touched by the regeneration scripts.

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:** `OpenResearchLeaves21.neronSchemeModelExistsDVR : ReductSplit.NeronSchemeModelExistsDVR`. This is BLR,
  *Néron models* §1.4 Thm 3 over a DVR, scheme form, without the group law (LEAF/LEAF; locator as in kinds.tsv,
  UNVERIFIED).
* **Added:** none. The binders of `frozenTarget` are the same four bundle types and seven Props; `OpenResearchLeaves21`
  has one field fewer.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/leaf-fold22b 9a100aa7 | base | — |
| origin/wip/neron-dvr 998fa5b5 | merged (2a6b6c4b) | NeronDVR.lean (`neronSchemeModelExistsNF`, `raynaudCriterion_leavesNF`, `ss1_ss3_of_cpNF`); the consumer list of §3.3 |
| yu-prune / sem-prune tools | copied to scratch/r6-nf/ | PruneScan.lean, DeadCascade.lean, DumpCompact.lean, cmp_hashes.py, the prune_edit helpers (prune_lib.py) |
