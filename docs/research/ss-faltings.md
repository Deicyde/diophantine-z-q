# ss-faltings: the last SGA 7 row off the bundle, through the stable Faltings height

Task ss-faltings, 2026-11-17. Base: fork main d435851d, then merged with fork main f3402e89 (fold-b112: sz-raynaud TailZ81,
y3-route-a TailZ82, bost-gr9 TailZ80, carirr-refold TailZ83; top `sixContactMin_of_open76`). Everything below is on
f3402e89. Results log: scratch/ss-faltings/log.md.

Marks: **VERIFIED** means compiled, or read in a named file of the repository. **STANDARD** means published, with an exact
reference. **SPECULATIVE** means judgement. Theorem numbers and page locators recalled from memory are **UNVERIFIED**
(no network). Model work, no human review.

## 1. Result

**The last SGA 7 row's reroute is done and compiles; the stop rule was not triggered.** The bundle field
`sga7_IX_Cor3_3_Def34` (SGA 7 IX Cor. 3.3, which is not in the manuscript's bibliography) reaches the proof only through
height-split's SS1, SS2 and SS3. The height rows read them for two things only:

1. the height of a semistable Néron model does not change under finite extension. That is Faltings 1983 §1, which the
   bibliography has and which the manuscript uses uncited at L596-598;
2. one number field over which an abelian variety (or two of them, for R20) is semistable.

They never need the semistability of a base change of a given semistable model.

- **New leaf:** `faltingsSemistableHeightBC : ZInQ.SSFaltings.FaltingsSemistableHeightBC` (Faltings 1983 §1, provenance
  (b), kind published). It counts GLUE, flagged "pending reading", because the print was not read. It replaces the
  field outright, and it is a consequence of SS2 (`faltingsSemistableHeightBC_of_ss2`, proved).
- **Item 2 is proved in Lean** (`semistableReductionThmIF_of_raynaud`): `A` is semistable over every number field
  containing `K(A[15])`. The proof uses Raynaud's criterion with the manuscript's `A[3]`/`A[5]` choice (L814-817,
  Silverberg–Zarhin Thm 3.5, now the folded leaf `silverbergZarhinThm35`) and textbook fields already in the bundle.
  No persistence statement is needed.
- **The bypass:** `HDec.HSyn.sixContactMin_of_open77sf`, on the bundle `OpenResearchLeaves58SF` (TailZ83's
  `OpenResearchLeaves57` with the field swapped). It compiles with only `[propext, Classical.choice, Quot.sound]`. The
  SGA 7 IX Cor. 3.3 statement, Cor. 3.3's derived forms (IX 3.3, `SemistablePersistsSHcp`) and SS2/SS3 are all absent
  from its closure. The only SGA 7 statement left there is IX 3.5 (`sga7_IX_3_5_ForwardGeom_Def34`), which is d2a6b's
  row; once d2a6b is folded, no SGA 7 row is left.
- **Count on f3402e89** (strict, H fields as OPEN.md counts them): 29 fields, 5 LEAF / 24 GLUE before and after;
  strictest 5/24 → 5/24. The GLUE row `sga7_IX_Cor3_3_Def34` (kind consequence, pending review) is replaced by the GLUE
  row `faltingsSemistableHeightBC` (kind published, pending reading). It becomes LEAF (6/23) once a reader checks
  Faltings §1 against the statement. SGA 7 rows in the bundle: 2 → 1 (0 with d2a6b).

## 2. What SS2 and SS3 are used for (traced, VERIFIED)

Sources: d2a6-reroute's trace (read from origin/wip/d2a6-reroute without merging: docs/research/d2a6-reroute.md §4,
scratch/d2a6-reroute/taintD-out.txt section COR33) and this task's declaration-level taint
(scratch/ss-faltings/TaintS.lean → taintS-out.txt, on the closure of `sixContactMin_of_open76`, TailZ83: 274529
constants, 28 carriers, 110 tainted declarations).

- **The field's path.** `sga7_IX_Cor3_3_Def34` (top bundle OpenResearchLeaves57, and 54-56) → `sga7_IX_3_3_SHpre` (36EBCF) → `sga7_IX_3_3_SH`
  → `sga7_IX_3_3` and `semistablePersistsSHcp` (OpenResearchLeaves14GMEB).
- **Its two readers** (first in EichlerBoundCopy.lean; on f3402e89 the live copies are in TailZ80, `HDec.HSyn.GR9`):
  - `ss1_ss3_of14NF_hf_gm_pz_eb`: SS1 (`SemistableReductionThm`) **and** SS3 (`SemistablePersists`), by
    `GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp …`. SS1 is tainted too: its global proof
    (`semistableReductionThm_of_leaves_nfNF`) uses persistence at the bad places (through `F O ≤ L₀`) and at the
    semistable places of `A`.
  - `researchLeaves9_of_open14_hf_gm_pz_eb`: SS2 := `semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 …`.
- **Downstream.** SS1-SS3 become fields of OpenResearchLeaves9EB and 8EB and are read only by
  - `heightRowsNo20_of8_hf_eb` (on f3402e89 the live copy is bost-gr9's, TailZ80, namespace `HDec.HSyn.GR9`): R18
    (Javanpeykar), R19 (Gaudron–Rémond), R21 (Gaudron–Rémond §9, since bost-gr9), R22 (Pazuki) and
    `StableHeightFinite`, through TailY's `r18_of_leaves`, `r19_of_leaves`, `r22_of_upper`, `stableHeightFinite_of'`
    and bost-gr9's `ZInQ.BostGR9.r21_of_grBost'`;
  - `r20Lower_of8_hf_eb`: the lower half of R20 (Faltings' Lemma 5), through `r20Lower_of_leaves'`.
- **What the readers use.**
  - SS2 only through TailY's `stableFaltingsHeight_eq_of_semistable` (also inside `r21_of_grBost'`): the kernel's stable height (an infimum over all
    number fields and all metrized group models) equals the height of any semistable Néron model. Its proof needs, for
    `L'/L` finite, `h(𝒩_{L'}) ≥ h(𝒩_L)` when `𝒩_L` is semistable (the other inequality is the Néron mapping property).
    That is **invariance of the height of a semistable abelian variety under finite extension**, Faltings' statement.
    The semistability of the base change itself, or the identity-component comparison of SS2, is never used.
  - SS3 only in `r20Lower_of_leaves'`, to make the Néron models of `A` and `B` over the compositum of their two
    semistable fields semistable, so that Faltings' Lemma 5 (semistable form) applies over one field. One common
    semistable field suffices.
  - SS1 (existence of a semistable field) in the identification (`exists_semistable_neron`) and in R20.
- **Answer to the lead's question.** The readers need invariance of the stable height under finite extension and one
  common field of semistable reduction for two abelian varieties; they do not need semistability of a base change of a
  given semistable model. Invariance under isogeny (L621) is R20, which is unchanged (its leaf is still Faltings'
  Lemma 5, `FaltingsLemma5BCLower`).

## 3. The reroute (Lean)

- `ZInQKernel/Contrib/OneProof/SSFaltings.lean` (297 lines, imports `NeronDVR` only, never `OneProof.Main`):
  - §1, the leaf `FaltingsSemistableHeightBC`, which is weaker than SS2 (`faltingsSemistableHeightBC_of_ss2`);
  - §2, `SemistableReductionThmIF` (∃ finite `K₀ ⊆ K̄`, every Néron model over every number field `K₀ ⊆ L ⊆ K̄` is
    semistable), `semistableReductionThm_of_IF` (gives SS1), `exists_three_or_five_isUnit` (`3·2 − 5 = 1` in a local
    ring) and `semistableReductionThmIF_of_raynaud` (from `RaynaudSemistable`, `MumfordTorsionAlgClosed`,
    `MulEtaleAbelianScheme`, `NeronSchemeModelExistsDVRNF`, `SemistableLocalGlobal`);
  - §3, the identification `stableFaltingsHeight_eq_of_semistableF` (the kernel's infimum height = the height of any
    semistable Néron model, from N1 and the leaf) and its corollaries `isStableFaltingsHeight_iffF`,
    `exists_semistable_neronF`, `stableFaltingsHeight_ne_botF`, then the rows `stableHeightFinite_ofF`,
    `r18_of_leavesF`, `r19_of_leavesF`, `r21_of_leavesF`, `r22_of_upperF` and `r20Lower_of_leavesF`. R20 is computed
    over the compositum `K_A ⊔ K_B` inside `K̄`, where both varieties are semistable by §2.
- `ZInQKernel/Contrib/OneProof/SSFaltingsGR9.lean` (34 lines): `r21_of_grBostF`, `r21_of_grBostF'`. These are
  bost-gr9's R21 proofs with the leaf in place of SS2.
- `ZInQKernel/Contrib/OneProof/SSFChain.lean` (3294 lines, generated by `scratch/ss-faltings/gen/gen_chain.py` from
  taintS-out.txt): the chain of `sixContactMin_of_open76` rerouted. It has 100 blocks, 72 declarations and 28
  structures, each copied verbatim with the renaming `X ↦ X_sf` / `XSF`. The edits:
  - 38 Cor. 3.3 field declarations become one field `faltingsSemistableHeightBC` per structure;
  - SS1 becomes `semistableReductionThmIF`, SS2 becomes `faltingsSemistableHeightBC`, and SS3 is dropped (6 field
    edits, 43 assignments, 4 binders);
  - `ss1_ss3_of14NF_hf_gm_pz_eb` becomes `semistableReductionThmIF_of_raynaud`;
  - the two readers move onto the §3 rows.

  sz-raynaud's conversion (`raynaudSemistableSHOr` from `silverbergZarhinThm35`) is copied verbatim, so the Raynaud
  leaf reaches §2 with no hand edit. The top is `HDec.HSyn.sixContactMin_of_open76_sf`.
- `scratch/ss-faltings/BypassFold.lean` (generated by `gen/gen_bypass.py`; the lead's next `TailZ<j>.lean`):
  - `OpenResearchLeaves58SF` (27 fields: `OpenResearchLeaves57` with `sga7_IX_Cor3_3_Def34` replaced by
    `faltingsSemistableHeightBC`);
  - the conversion `openResearchLeaves57SF_of_OpenResearchLeaves58SF`;
  - `sixContactMin_of_open77sf (r : OpenResearchLeaves58SF) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27)`.

  It is a bypass, not an autofold: the old field does not follow from the new leaf. The kinds row is
  scratch/ss-faltings/kinds-rows.tsv.
- **Order with d2a6b.** Both generators stop with an error when an edit target is missing (a structure or field, the
  readers, `ss1_ss3_of14NF_hf_gm_pz_eb`, `raynaudSemistable_of14_hf_gm_eb`, the reader calls, or any leftover mention
  of a Cor. 3.3 or SS name). If d2a6b folds first, set the import and `topName` in `TaintS.lean` (two lines) to the
  new top, rerun it, then run `gen_chain.py OUT TOPMOD TOP` and `gen_bypass.py TOPMOD R0 OLD_TOP NEWR NEW_TOP TB AD`.

## 4. Checks

All runs: `lake env lean` or `lake build`, one Lean process at a time, on f3402e89 plus this task's files.

| check | outcome (VERIFIED) |
|---|---|
| `lake build ZInQKernel.OneProof.H.TailZ83` | EXIT 0 (build-tailz83.txt, truncated) |
| `TaintS.lean` on `sixContactMin_of_open76` | taintS-out.txt: closure 274529, 28 carriers (with module lines), 110 tainted |
| `lake build ZInQKernel.Contrib.OneProof.SSFChain` (builds SSFaltings, SSFaltingsGR9) | EXIT 0; `sixContactMin_of_open76_sf`: [propext, Classical.choice, Quot.sound] |
| `BypassCheck.lean` (= BypassFold.lean + closure check + dead-field probe + `#print axioms`) | EXIT 0 (bypass-check-out.txt): `sixContactMin_of_open77sf` and all 18 new SSFaltings theorems: [propext, Classical.choice, Quot.sound] |
| closure of `sixContactMin_of_open77sf` | absent: `SGA7_IX_Cor3_3_Def34`, `SGA7_IX_Cor3_3`, `CToPrinted.SGA7_IX_3_3`, `SemistablePersistsSHcp`, `SemistableNeronBaseChange`, `SemistablePersists`, `sorryAx`; present: `FaltingsSemistableHeightBC`, `SemistableReductionThmIF`, `SilverbergZarhinThm35`, `SGA7_IX_3_5_ForwardGeom_Def34` (d2a6b's row). `SemistableReductionThm` occurs only as the statement SS1 (type of `semistableReductionThm_of_IF`). Control, `sixContactMin_of_open76`: all Cor. 3.3 names present |
| dead-field probe | no field of `OpenResearchLeaves58SF`, `OpenTextbookLeaves18`, `OpenAddedLeaves27` becomes unread |
| `#discharges` (`scratch/ss-faltings/Discharges.lean`, imports Main, Discharges, SSFChain) | EXIT 0, discharges-out.txt: no field is discharged outright by this task (the only SSFChain matches are self-matches of the copied bundles' projections). So there is no autofold spec or dry run: nothing qualifies |
| `gen_bypass.py` | 27 → 27 fields; strict 5/24 on 29 → 5/24 on 29; strictest 5/24 → 5/24 |

## 5. The new leaf, rated

| field | rating | provenance line |
|---|---|---|
| `faltingsSemistableHeightBC` (`ZInQ.SSFaltings.FaltingsSemistableHeightBC`) | kind published, **GLUE** (flag "pending reading: Faltings 1983 §1 not read by this task") | (b) Faltings, Invent. Math. 73 (1983), 349-366, §1 (locator UNVERIFIED): the height of an abelian variety with semistable reduction does not change under finite extension. The bibliography cites the paper (bibitem `faltings1983`, L11084-11086; cited at L621 and L733); at L596-598, where the statement is used, the manuscript cites nothing. Stated over the kernel's `GroupModel.height` and height-split's `IsSemistable`; not stronger than the row it replaces (`faltingsSemistableHeightBC_of_ss2`: SS2 implies it with the kernel's proved height lemmas) |

No other leaf is added. `SemistableReductionThmIF` is GLUE, proved in Lean (`semistableReductionThmIF_of_raynaud`).
The proof uses only fields already in the bundle and already used for SS1:
- the Raynaud leaf: on f3402e89, `silverbergZarhinThm35` (Silverberg–Zarhin Thm 3.5, as the manuscript cites it at
  L816), through sz-raynaud's `raynaudSemistableSHOr_of_sz35`, `raynaudSemistableSH` and
  `ReductB.raynaudSemistable_of_SH_pair`;
- `strictHenselizationPair`;
- the textbook fields `mumfordTorsionAlgClosed`, `mulEtaleAbelianScheme` and `neronSchemeExtensionExists`;
- `blr_1_2_4` (BLR 1.2/4, proved by gt-blr).

**Stop rule.** Not triggered. The reroute needs nothing uncited beyond Faltings 1983: the one new statement is
Faltings' invariance. The semistable field comes from Raynaud's criterion (cited at L816) and textbook facts:
- the field of definition of `A[15]` and `[m]`-étale descent, from the textbook fields `mumfordTorsionAlgClosed` and
  `mulEtaleAbelianScheme`;
- `3` or `5` is a unit in a local ring (proved here);
- Néron models over DVRs and their localization (existing bundle fields, BLR 1.4/3 and 1.2/4).

No on-the-spot leaf.

## 6. Manuscript check

One line per manuscript step this work formalizes or relies on.

| tex lines | step | verdict |
|---|---|---|
| L596-597 | "After a finite extension `E` has everywhere good reduction, since its `j`-invariant is integral." | **OK** (relied on only as the special case of semistable reduction; standard: CM `j` integral ⇒ potentially good reduction, Serre–Tate 1968 §2, UNVERIFIED locator). Not formalized here |
| L597-598 | "This extension does not change its stable Faltings height." | **gap filled**: uncited. It is Faltings 1983 §1 (invariance of the height of a semistable abelian variety under finite extension; locator UNVERIFIED), which the bibliography has; formalized as the leaf `faltingsSemistableHeightBC` (provenance (b), pending reading) in the general form the kernel's height rows need. Flag for the ledger: ELLIOT-type sentence at L597-598, now carried by a cited print |
| L598, L876 (and L611-623, L870-903, L939-945) | `h_F` is "the stable Faltings height" (L876: "the original stable Faltings height") of an abelian variety over a number field, used as a field-independent invariant | **gap filled**: the manuscript never defines it nor says why it is well defined. Well-definedness = (i) a field of semistable reduction exists, (ii) the height is the same over every larger field. (i): Raynaud's criterion (L816's citation) over `K(A[15])`, proved in Lean (`semistableReductionThmIF_of_raynaud`); (ii): Faltings 1983 (the new leaf). The kernel's identification `stableFaltingsHeight A = h(𝒩_L)` for any semistable `L` is proved from these (`stableFaltingsHeight_eq_of_semistableF`) |
| L621 | "Height variation under isogeny [faltings1983]" (R20, lower half) | **gap filled**: Faltings' Lemma 5 is for an isogeny of abelian varieties semistable over one field; applied to stable heights it needs a common field of semistable reduction for source and target, not mentioned. Supplied by `SemistableReductionThmIF` at `K(A[15])·K(B[15])` (`r20Lower_of_leavesF`); the leaf itself (`FaltingsLemma5BCLower`) is unchanged and not re-read here |
| L814-817 | `F = L_v(A[3])` (`A[5]` if `p = 3`); Raynaud's criterion [SZ Thm 3.5] gives semistable reduction there | **OK** for the use made here: the same criterion with the same torsion choice (`m = 3`, or `5` where `3` is not a unit, `3·2 − 5 = 1`) gives semistable reduction at every place of every number field containing `K(A[15])` |
| L870-876 | Javanpeykar Thm 1.1.1 + §2.3 over the stable height (R18) | **unverified** here (not this task's step; read by the locator audit): the row's proof now goes through the new identification, the leaf is unchanged |
| L879-885 | Gaudron–Rémond Thm 1.4 (R19) | **unverified** here (same remark) |
| L894-895 | `h_F(Z) ≥ −(3/2) dim Z` [GR §9] (R21, Bost) | **unverified** here (same remark) |
| L937-945 | Pazuki Cor. 1.3(2) (R22) | **unverified** here (same remark) |
| L11084-11086 | bibitem `faltings1983` (Invent. Math. 73 (1983) 349-366; erratum 75 (1984) 381) | **OK** as a reference for the new leaf. The paper is cited at L621 (isogeny) and L733 (semisimplicity/Tate) but not at L596-598, where its §1 invariance is used. The §1 locator is UNVERIFIED (not read) |

## 7. Known issues

1. **The leaf's print was not read.** Faltings 1983 §1 was not read (no network access). The statement (the height
   of an abelian variety with semistable reduction everywhere is unchanged under finite extension), its locator and
   its normalization are recalled, so all three are UNVERIFIED. For that reason the row counts GLUE with a "pending
   reading" flag. The reading desk should check three things:
   - (a) that the print states the invariance and not only uses it;
   - (b) that Faltings' height (the Néron model's `ω`, metric `(i/2)^g ∫ η ∧ η̄`, degree divided by `[K:ℚ]`) is the
     kernel's `GroupModel.height`. The erratum (Invent. Math. 75, 1984) concerns a different point, recalled and
     UNVERIFIED;
   - (c) that Faltings' "semistable" is height-split's `IsSemistable` (identity component of the geometric special
     fibre semi-abelian).
2. **The mathematics still rests on SGA 7.** Faltings gives SGA 7 IX 3.3 as the reason for the invariance, as recalled
   (UNVERIFIED). The reroute moves the citation from SGA 7, which the bibliography lacks, to Faltings 1983, which it
   has, and states only what the readers use. The dependence on Grothendieck's theorem is now inside a cited print.
3. **The leaf is stated over all Néron models.** It is stated for every Néron model `𝒩'` over `L'`, with no
   semistability assumed for `𝒩'`. That is what "the height does not change" means for the kernel's height. It is a
   consequence of SS2 (proved), so it is not stronger than the row it replaces.
4. **Fold order.** The bypass was generated on TailZ83. d2a6b also bypasses TailZ83. Whichever is folded second must
   be regenerated on the new top (see §3), and the generators stop with an error if an edit target moved.
5. **What gets replaced.** SS1's old proof (`GapNeron.ss1_ss3_of_cpNF`) also used the strict-henselization and
   semistable-almost-everywhere glue. The new proof does not, but those fields stay read elsewhere (dead-field probe),
   so no field is pruned.

## 8. Files

- `ZInQKernel/Contrib/OneProof/SSFaltings.lean`, `SSFaltingsGR9.lean`, `SSFChain.lean` (generated): new, never import
  `OneProof.Main`.
- `scratch/ss-faltings/`:
  - log.md (results log);
  - TaintS.lean → taintS-out.txt (trace);
  - gen/gen_chain.py, gen/copylib.py, gen/header.lean (chain generator; copied.txt lists the copied declarations);
  - gen/gen_bypass.py → BypassFold.lean, kinds-rows.tsv, bypass-gen-out.txt;
  - gen/make_check.sh → BypassCheck.lean → bypass-check-out.txt (with closure_check_tail.lean, dead_probe_tail.lean);
  - Discharges.lean → discharges-out.txt;
  - build-*.txt (truncated build logs);
  - ref-d2a6-* (read-only reference copies of d2a6-reroute's scripts).
