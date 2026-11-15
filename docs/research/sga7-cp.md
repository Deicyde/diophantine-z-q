# sga7-cp: neither SGA 7 IX strictly henselian leaf can be removed; both are weakened to characteristic 0 with a perfect residue field, and the hand fold compiles

Task sga7-cp, 2026-11-15. Base: wip/r6-nf 0bc2446d (`frozenTarget` through `sixContactMin_of_open28`, 55 H fields).
Results log: scratch/sga7-cp/log.md. Model work, no human review.

Marks:
* **VERIFIED**: compiled, or read in a named file on this host;
* **STANDARD**: published mathematics with an exact reference;
* **SPECULATIVE**: judgement;
* **UNVERIFIED**: a theorem number given from memory (this host has no network).

## 1. Verdict

**Neither field can be removed** by rerouting through fields already in the bundles (SPECULATIVE, argued in §3).
Both are therefore **weakened to the instance the chain actually uses**: a strictly henselian DVR whose fraction
field has characteristic 0 and whose residue field is perfect (hence algebraically closed). Both weakened forms
are printed statements: each is a specialization of the print under every reading considered.

| field (OpenResearchLeaves21) | replaced by (OpenResearchLeaves22) | relation |
|---|---|---|
| `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` (SGA 7 IX 4.7, every strictly henselian DVR) | `raynaudSemistableSHcp : ReductB.RaynaudSemistableSHcp` (TailZ23 L303, already in the tree) | specialization (`SGA7CP.raynaudSemistableSHcp_of_SH`) |
| `sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` (SGA 7 IX 3.5 forward, every strictly henselian DVR) | `sga7_IX_3_5_ForwardGeomCP : SGA7CP.SGA7_IX_3_5_ForwardGeomCP` (new) | specialization (`SGA7CP.forwardGeomCP_of_forwardGeom`); also a consequence of the reading-robust `SGA7_IX_3_5_Forward` with **no glue** (`SGA7CP.forwardGeomCP_of_forward`) |

Counts:
* H fields stay 55; strict 45 LEAF / 10 GLUE and strictest 44 / 11 are unchanged. Both new leaves are LEAF/LEAF,
  as the old ones were.
* The hypotheses get strictly weaker: `openResearchLeaves22_of_OpenResearchLeaves21` compiles, so the old
  `frozenTarget` follows from the new one.
* Two reading risks recorded in kinds.tsv disappear:
  * 4.7: "the print may assume an algebraically closed residue field". The restricted form has one.
  * 3.5: "semistability over k(s) versus the geometric fibre". The two readings agree for perfect residue fields
    (`UnipotentForward.isSemistableRes_iff`), so the CP form follows from the reading-robust form outright.

All of the following is VERIFIED (compiled; outputs in scratch/sga7-cp/):
* `ZInQKernel/Contrib/OneProof/SGA7CP.lean` (the contributor file: the new leaf, and r6 and SS1/SS3 from the two
  restricted leaves) builds;
* `ZInQKernel/Contrib/OneProof/SGA7CPFold.lean` (the generation module: `HDec.HSyn.OpenResearchLeaves22`,
  `HDec.HSyn.sixContactMin_of_open29`) builds;
* `SGA7CPCheck.frozenTarget'` (scratch/sga7-cp/Check.lean: Main's `frozenTarget` with `r : OpenResearchLeaves22` and
  `sixContactMin_of_open29`) has axioms `[propext, Classical.choice, Quot.sound]`. Its type is `frozenTarget`'s with
  `OpenResearchLeaves21` replaced by `OpenResearchLeaves22`; the conclusion and the other ten binders are identical
  (Check-output.txt);
* DumpCompact (Main, then Main plus the two new modules) and cmp_hashes.py: base 15668, after 15726, **removed 0,
  changed 0**, new 58 (cmp_hashes_out.txt);
* PruneScan rooted at `frozenTarget'`: 28 + 12 + 14 + 1 = 55 fields, **0 unused**, prune set empty
  (prunescan-out.txt).

## 2. Where the two fields were used (VERIFIED by reading TailZ23–TailZ34 and NeronDVR.lean)

* **`raynaudSemistableSH`** has one reader, `HSyn.raynaudSemistable_of14` (TailZ23), via
  `ReductB.raynaudSemistable_of_SH_pair`. It is applied at the strict henselization `E ⊇ K` that
  `StrictHenselizationPair` provides. It feeds:
  * `HSyn.raynaudCriterionNF_of14` (TailZ26): r6, applied only at number fields `K`;
  * `semistableReductionDVR_of14` → `HSyn.ss1_ss3_of14NF` (TailZ26): SS1/SS3, used only at number fields
    (`reductionNF_of_general`).
* **`sga7_IX_3_5_ForwardGeom`** has one reader, the conversion `openResearchLeaves19_of_OpenResearchLeaves20`
  (TailZ33). It fills `semistableUnipotent` by `UnipotentForward.semistableUnipotent_of_forwardGeom`, which applies
  the leaf at the inertia field `E` of a place `w` of `K̄` (`StrictHenselizationInside`). Its only reader is
  `raynaudCriterionNF_of14`: r6 at `hU K O (AlgebraicClosure K) w …`, where `K` is a number field.

In every case `E` is an algebraic extension of a number field, so it has characteristic 0. Its residue field is
algebraic over the finite residue field of `O`:
* `ReductB.perfectField_residue_nf`;
* `ReductB.perfectField_of_isSHNeronExt`.

Hence that residue field is perfect.

The composite conversions from generation 21 down to generation 14 were computed by scratch/sga7-cp/compose.py
(output in compose-out.txt).

## 3. Why neither field can be removed (SPECULATIVE; mathematical judgement)

* **4.7 is the only source of semistability.** SS1 (Grothendieck's semistable reduction theorem,
  `SemistableReductionThm`) is derived in the chain from Raynaud's criterion by reduct-b's K1: after `K(A[m])`,
  `m ≥ 3`. No other field yields semistability:
  * 3.3 and 3.3-second (persistence, `semistablePersistsSHcp`, `sga7_IX_3_3_SH`) presuppose it;
  * the forward half of 3.5 presupposes it;
  * neither the converse of 3.5 nor 3.6 is a field.
* **The forward half of 3.5 is the only source of unipotence of inertia.** r6 is consumed in Galois form:
  * `PkgI2.goodReduction_of_QM_rational3_of_alg` combines `(σ - 1)² = 0` on `A[3^{2k}]` with `QuatUnipotentTrivial`
    and Néron–Ogg–Shafarevich;
  * `G15Ram.raynaudPlace_of_R6` uses it too.

  A route avoiding 3.5 would go "semistable plus potentially good implies good", using the toric part and the
  quaternion action on its character group. It needs character groups of tori over the special fibre, which are
  not in the tree.

## 4. The new leaf and the proofs (all compiled, VERIFIED)

`ZInQKernel/Contrib/OneProof/SGA7CP.lean`, namespace `SGA7CP`, 14 KB:
* **`SGA7_IX_3_5_ForwardGeomCP`** (LEAF): `UnipotentForward.SGA7_IX_3_5_ForwardGeom`, verbatim, with
  `[CharZero K] [PerfectField (IsLocalRing.ResidueField O)]` added.
* `forwardGeomCP_of_forwardGeom`, `raynaudSemistableSHcp_of_SH`: each restriction is a specialization of the field
  it replaces.
* `forwardGeomCP_of_forward : SGA7_IX_3_5_Forward → SGA7_IX_3_5_ForwardGeomCP`: no glue, by
  `UnipotentForward.semiAbelianDescends_of_perfect`.
* `semistableUnipotentSHcp_of_forwardGeomCP`, `semistableUnipotentNF_of_SHcp`,
  `semistableUnipotentNF_of_forwardGeomCP`: the CP analogues of `semistableUnipotentSH_of_forwardGeom` and
  `ReductGlue.unipotentFromSH_of`. The proofs are copied; the only additions are the two instances at the inertia
  field. The conclusion `SemistableUnipotentNF` is `ReductSplit.SemistableUnipotent` with `[NumberField K]`.
* `raynaudCriterionNF_of_cp`: `GapNeron.raynaudCriterion_of_leavesNF` with `hR : ReductB.RaynaudSemistableCP` and
  `hU : SemistableUnipotentNF`. The only addition is `perfectField_residue_nf`.
* **`raynaudCriterionNF_of_cpLeaves`** (replaces `raynaudCriterionNF_of14`): r6 at number fields from
  `RaynaudSemistableSHcp` and `SGA7_IX_3_5_ForwardGeomCP`, using fields already in the bundles:
  * `neronBaseChangeStrictHenselization`, which gives `StrictHenselizationPair` and `StrictHenselizationInside`;
  * N1 `neronSchemeExtensionExists`;
  * `mumfordTorsionAlgClosed`;
  * the proved `MulEtaleAbelianScheme`.
* **`ss1_ss3_of_cpLeaves`** (replaces `ss1_ss3_of14NF`): neron-dvr's `GapNeron.ss1_ss3_of_cp_fullNF` with the same
  inputs, plus `semistablePersistsSHcp`, `SemistableLocalGlobal` and `SemistableAlmostAll`.

`ZInQKernel/Contrib/OneProof/SGA7CPFold.lean`, namespace `HDec.HSyn`, 17 KB, the generation module:
* **`OpenResearchLeaves22`**: `OpenResearchLeaves21` with the two fields replaced in place, docstrings updated.
* **Bypass.** A weaker bundle cannot map to generation 21: a Prop bundle must be built in full. So
  `sixContactMin_of_open29` maps the bundles straight to the inputs of `sixContactMin_of_open11` (TailZ13), as
  leaf-fold14 did:
  * `researchLeaves9_of_open22`, `x6Rows_of_open22`, `mumfordRigidity_of22` and `addedLeaves9_of_open22` are the
    TailZ23 terms, with the gen-21 → gen-14 composites substituted;
  * `addedLeaves12_of_open17` composes the existing added-leaf conversions;
  * `hYu` and `faltingsLemma5BCLower` are as in `_open24` and `_open17`;
  * r6 and SS1/SS3 come from `raynaudCriterionNF_of22` and `ss1_ss3_of22`.
* `openResearchLeaves22_of_OpenResearchLeaves21` (off the chain): the new bundle follows from the old.

## 5. The new leaves, rated

* **`raynaudSemistableSHcp`: printed form (restricted).** It is SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED)
  restricted to characteristic 0 and a perfect residue field. That is a specialization under each reading:
  * if 4.7 is printed over strictly henselian traits, possibly with an algebraically closed residue field, the
    restricted form is that statement at such bases;
  * if it is printed over general traits, the restricted form is a specialization of it.

  Unchanged caveats:
  * the `m = 3` boundary, docs/research/locators.md row R6 (Silverberg–Zarhin Thm 3.5's extraction looked like
    `> 3`; the chain uses `m = 3` in A6);
  * a possible Galois-form conclusion in the print.
* **`sga7_IX_3_5_ForwardGeomCP`: printed form (restricted).** SGA 7 I Exp. IX Prop. 3.5, forward direction, at
  `σ = τ` (number UNVERIFIED). It is a consequence of the print under both semistability readings: it follows from
  `SGA7_IX_3_5_Forward`, which assumes both readings, with no glue. The echelon caveat is unchanged: if 3.5's
  display lacks the clause, the square-zero bound comes from IX 2.4.

Proposed kinds.tsv rows: scratch/sga7-cp/kinds-rows-proposed.tsv. Both rows are LEAF/LEAF with flag_class
`restricted,unverified-locator`. The rows of the two old fields would be deleted at the fold.

**A narrower alternative, not taken.** The literal "number-field instance" of 4.7 would be the DVR form at number
fields:
* it is `RaynaudSemistableCP` at number fields;
* it would make `StrictHenselizationPair` unnecessary for 4.7;
* it is printed only if 4.7 (or Silverberg–Zarhin Thm 3.5, which states it over a general discretely valued field;
  UNVERIFIED) is read over general traits.

The strictly henselian CP form is the specialization that is safe under every reading, so it was chosen.

## 6. Deliverables and integration

* **Contributor file:** `ZInQKernel/Contrib/OneProof/SGA7CP.lean`, importing `ZInQKernel.OneProof.H.TailZ34`
  (where `OpenResearchLeaves21` is declared), not Main.
* **Generation module:** `ZInQKernel/Contrib/OneProof/SGA7CPFold.lean`, written to be moved verbatim to
  `ZInQKernel/OneProof/H/TailZ35.lean`. `autofold.py`'s `find_struct` reads only `OneProof/H/`, so the next autofold
  needs the module there.
* **Main.lean switch** (two tokens):
  * `(r : HDec.HSyn.OpenResearchLeaves22)`;
  * `HDec.HSyn.sixContactMin_of_open29 r t l g`.

  The switched theorem compiled as `SGA7CPCheck.frozenTarget'` (scratch/sga7-cp/frozenTarget_cp.lean.inc).
* **`#discharges`** (scratch/sga7-cp/Check-output.txt): "62 open hypotheses, 1694 theorems checked, 31 discharge
  one".
  * The SGA7CP theorems discharge nothing. This is a weakening, not a proof of either field's statement.
  * The 24 new lines are the projections `OpenResearchLeaves22.<f>`, which "discharge" generation-21 fields by
    assuming the new bundle. This is an artefact of a bundle living under `Contrib/OneProof`, and it disappears once
    the module moves to `OneProof/H`.
  * The other 7 lines are DischargesTest's, unchanged.
* **scratch/sga7-cp/autofold.json:** autofold.py cannot express this fold. It fills each discharged field with a
  proof, and a weaker leaf cannot prove the field. The JSON records the replacement, the leaves (kind, flag,
  source), the new bundle and top theorem, and the move/switch instructions above.
* **Name collision risk:** if another fold lands first and generates `OpenResearchLeaves22`/`TailZ35`/`_open29`,
  rename this module's three names (a mechanical edit).

## 7. Not done

* Neither field is removed (§3). The H field count stays 55.
* Main.lean, kinds.tsv and OPEN.md are not switched: editing under `ZInQKernel/` outside `Contrib/OneProof/` is
  outside this task's rules. The switched theorem is compiled in scratch.
* The `m = 3` boundary of 4.7 and the echelon clause of 3.5 remain open reading items. They are unchanged by this
  task.
