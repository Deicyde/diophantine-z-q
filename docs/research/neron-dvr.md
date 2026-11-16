# neron-dvr: Néron models over the discrete valuation rings of a number field (gap-triage A8)

Base: `3782dac8e` (wip/leaf-fold18 head; newest generation `sixContactMin_of_open25`, TailZ31). The field
`neronSchemeModelExistsDVR` is in `OpenResearchLeaves19` (TailZ29 L41).

## 1. Result

**What is proved (VERIFIED, compiled).** The number-field form of the field follows from the textbook field N1
alone. BLR 1.2/4 is not needed as a hypothesis, because gt-blr's `GapBLR.neronLocalizesDVR_proved` takes no
hypotheses.

**What blocks dropping the field (VERIFIED).** The lead cannot drop the field by rerouting consumers. Two of its
three live consumers, r6 and r8, fill fields of the old bundles (`OpenResearchLeaves9` down to `ResearchLeaves3`)
whose statements cover every field. Section 3 gives the details and what would be needed.

File: `ZInQKernel/Contrib/OneProof/NeronDVR.lean`, 22 KB. It imports only `ZInQKernel.Contrib.OneProof.BLRLocalizes`.

* `lake build ZInQKernel.Contrib.OneProof.NeronDVR` succeeds.
* `lake env lean` on the file prints no errors and no warnings.

### 1.1 Statements (verbatim)

```lean
/-- the research field `ReductSplit.NeronSchemeModelExistsDVR` (TailZ7 L238, verbatim) with `[NumberField K]` -/
def GapNeron.NeronSchemeModelExistsDVRNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of O))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (e : (Over.pullback (jO O)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
        Function.Bijective fun f : Y ⟶ N => (Over.pullback (jO O)).map f ≫ e.hom

theorem GapNeron.neronSchemeModelExistsDVRNF_of_field (h : ReductSplit.NeronSchemeModelExistsDVR) :
    GapNeron.NeronSchemeModelExistsDVRNF
theorem GapNeron.neronSchemeModelExistsNF (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists) :
    GapNeron.NeronSchemeModelExistsDVRNF
theorem GapNeron.neronSchemeModelExistsNF' (hN1 : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists)
    (_hB : CToPrinted.BLR_1_2_4) : GapNeron.NeronSchemeModelExistsDVRNF   -- the A8 signature; hB unused
```

Restated consumers. Each has the hypotheses of the original, with `hN : NeronSchemeModelExistsDVR` replaced by
`hN : GapNeron.NeronSchemeModelExistsDVRNF`. The proofs are copied unchanged, except for one added `NumberField K'`
instance in the r8 proof.

```lean
-- SS1/SS3 (originals in TailZ23, namespace ReductB)
theorem GapNeron.semistablePersists_of_leaves_nfNF (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistablePersists                                         -- TailZ23 L441
theorem GapNeron.semistableReductionThm_of_leaves_nfNF (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) (hDown : DVRComapFinite) : ZInQ.HeightSplit.SemistableReductionThm  -- L509
theorem GapNeron.semistablePersists_final_nfNF (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal) :
    ZInQ.HeightSplit.SemistablePersists                                         -- L566
theorem GapNeron.semistableReductionThm_final_nfNF (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) : ZInQ.HeightSplit.SemistableReductionThm       -- L573
theorem GapNeron.ss1_ss3_of_cpNF (hSH : SemistablePersistsSHcp) (hPair : StrictHenselizationPair)
    (h36 : SemistableReductionDVR) (hN : NeronSchemeModelExistsDVRNF) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists   -- L580
theorem GapNeron.ss1_ss3_of_cp_fullNF (hR : RaynaudSemistableSHcp) (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronSchemeModelExistsDVRNF)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists   -- L591
-- common lemmas (TailZ7 L315, L333)
theorem GapNeron.exists_neron_groupModelNF  {K} [Field K] [NumberField K] (hN : NeronSchemeModelExistsDVRNF) (O) [IsDiscreteValuationRing O] (A) :
    ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel
theorem GapNeron.hasSemistableReduction_ofNF {K} [Field K] [NumberField K] (hN : NeronSchemeModelExistsDVRNF) (O) [IsDiscreteValuationRing O] (A)
    (h : SemistableNeronModels A O) : HasSemistableReduction A O
-- r6, r8: the conclusion is weakened to the number-field restriction
def GapNeron.RaynaudCriterionNF : Prop       -- PkgI2.RaynaudCriterion (Objects.lean L1436) with [NumberField K]
def GapNeron.GrothendieckMonodromyNF : Prop  -- PkgI2.GrothendieckMonodromy (Objects.lean L1416) with [NumberField K]
theorem GapNeron.raynaudCriterionNF_of_general (h : PkgI2.RaynaudCriterion.{0}) : RaynaudCriterionNF
theorem GapNeron.grothendieckMonodromyNF_of_general (h : PkgI2.GrothendieckMonodromy.{0}) : GrothendieckMonodromyNF
theorem GapNeron.raynaudCriterion_leavesNF (hR : RaynaudSemistable) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNF               -- TailZ14 L243
theorem GapNeron.grothendieckMonodromy_final'NF (hS : SemistableReductionDVR) (hU : SemistableUnipotent)
    (hN : NeronSchemeModelExistsDVRNF) (hM : AvSplit.MumfordTorsionAlgClosed) :
    GrothendieckMonodromyNF                                                    -- TailZ7 L1496
theorem GapNeron.r6_r8_NF_of_N1 (hN1 : NeronSchemeExtensionExists) (hR : RaynaudSemistable)
    (hU : SemistableUnipotent) (hS : SemistableReductionDVR) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudCriterionNF ∧ GrothendieckMonodromyNF
```

`raynaudSemistable`, `semistableReductionDVR`, `semistableUnipotent` and `semistablePersistsDVR` (through its
`nf`/`SHcp` forms) appear only as hypotheses. No `semistableNeronBaseChange_of_printed*` theorem (gt-sga7's area)
is restated or needed.

### 1.2 Axioms (`scratch/neron-dvr/Discharges.lean`, VERIFIED)

Every theorem listed above prints `depends on axioms: [propext, Classical.choice, Quot.sound]`:
`neronSchemeModelExistsNF`, `neronSchemeModelExistsNF'`, `neronSchemeModelExistsDVRNF_of_field`,
`ss1_ss3_of_cpNF`, `ss1_ss3_of_cp_fullNF`, `semistablePersists_final_nfNF`, `semistableReductionThm_final_nfNF`,
`raynaudCriterion_leavesNF`, `grothendieckMonodromy_final'NF`, `raynaudCriterionNF_of_general`,
`grothendieckMonodromyNF_of_general` and `r6_r8_NF_of_N1`.

## 2. `#discharges` (scratch/neron-dvr/discharges.txt)

```
DISCHARGES [OpenResearchLeaves19.gonzalezRotgerProp56X6] by GRCountX6.prop56X6_of_r5fpCount
  still assumes: [LeafQM.AV.R5fpCount]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves19.neronBaseChangeStrictHenselization] by GapSHPair.neronBaseChangeStrictHenselization_of_unramified
  still assumes: [ReductGlue.NeronBaseChangeUnramifiedDVR]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves19.elkiesX6StarPrinted] by HDec.QMSplit.Moduli.ElkiesX6Star.elkiesX6StarPrinted_of_ab
  still assumes: [HDec.QMSplit.Moduli.ElkiesEquationsX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 66 open hypotheses, 1228 theorems checked, 3 discharge one
```

All three lines come from contributions already in the tree; none comes from `GapNeron`. This is expected:
`NeronSchemeModelExistsDVRNF` is weaker than the field, so no `GapNeron` theorem matches an open hypothesis by type.
**No autofold spec**, since no field is discharged. A manual fold follows.

## 3. The fold

### 3.1 Every consumer of the field in the live proof (VERIFIED)

`scratch/neron-dvr/Reach.lean` (output: `reach.txt`) lists every constant reachable from
`ZInQ.OneProof.frozenTarget` whose type or value mentions `ReductSplit.NeronSchemeModelExistsDVR`.

* **Field passing only.** The bundle projections and constructors of `OpenResearchLeaves19 … 14` (TailZ29 L105,
  TailZ28 L108, TailZ27 L109, TailZ26 L115, TailZ25 L119) and `OpenResearchLeaves9` (TailZ9).
* **Not in the live proof.** The generations of TailZ15, TailZ17, TailZ19 and TailZ22 (`OpenResearchLeaves10–13`)
  are not reachable, because `researchLeaves9_of_open14` goes from 14 straight to 9.
* **Real uses**, at three sites:

| site (base 3782dac8e) | term | consumer reached | NF suffices? |
| --- | --- | --- | --- |
| TailZ23 L763-768 `ss1_ss3_of14` | `ReductB.ss1_ss3_of_cp … r.neronSchemeModelExistsDVR …` | `ss1_ss3_of_cp` → `*_final_nf` → `*_of_leaves_nf` → `hasSemistableReduction_of` at the number fields `L`, `L'`, `F O`, `L₀` | **yes** |
| TailZ23 L780-781 `researchLeaves9_of_open14`, field `r6` | `ReductGlue.raynaudCriterion_leaves (raynaudSemistable_of14 r t) r.semistableUnipotent r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme` | conclusion `PkgI2.RaynaudCriterion.{0}`, every field | **no**: `OpenResearchLeaves9.r6` needs every field |
| TailZ23 L803 `researchLeaves9_of_open14`, field `neronSchemeModelExistsDVR`, read at TailZ9 L100-101 | `r8 := ReductSplit.grothendieckMonodromy_final' r.semistableReductionDVR r.semistableUnipotent r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed` | conclusion `PkgI2.GrothendieckMonodromy.{0}`, every field | **no**: `OpenResearchLeaves8.r8` needs every field |

### 3.2 Replacement terms

For SS1 and SS3 (TailZ23 L763), `ss1_ss3_of14` becomes:

```lean
  GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14 r t)
    (GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10 (addedLeaves9_of_open14 r t l))
```

This term compiles over `OpenResearchLeaves14` (the `example` at the end of `scratch/neron-dvr/Discharges.lean`,
VERIFIED). N1 is the field `neronSchemeExtensionExists` of `OpenTextbookLeaves10` (TailZ11 L31).

For r6 (L781) and for L803 → r8 there is **no replacement term**. With the NF field they give only
`GapNeron.raynaudCriterion_leavesNF … : RaynaudCriterionNF` and
`GapNeron.grothendieckMonodromy_final'NF … : GrothendieckMonodromyNF`.

### 3.3 What dropping the field would take (VERIFIED by `Reach.lean` unless marked otherwise)

**r8 is dead.** In the live proof, `PkgI2.GrothendieckMonodromy` occurs only in three places:

* the bundles `OpenResearchLeaves8, 7, 5, 2` and `ResearchLeaves3`;
* the transport `grothendieckMonodromy_ofK5` (TailM L463);
* the producers in TailZ7.

The projections `.r8` are read only by the bundle maps `researchLeaves7_of_open8`, `…5_of_open7`, `…2_of_open5`
and `…3_of_open2`. `ResearchLeaves3.r8` is never read. `ObjBridge.GrothendieckMonodromy` is not reachable.

**r6 is applied only at number fields.** `PkgI2.RaynaudCriterion` (and `ObjBridge.RaynaudCriterion` through
`raynaudCriterion_iff`) is applied to a concrete field at exactly two sites. All the other reachable consumers only
pass it on. The two sites:

* **LPrefix L833** (`HDec.PkgI2.goodReduction_of_QM_rational3_of_alg`, `hRay K O w hw A 3 …`), at the field of a
  `QML3` object. It is reached through `LeafQM.AV.QML3.goodReduction` (LPrefix) from two callers:
  * TailC L5947 `good_of_QML3`, where `K : IF`, `[FiniteDimensional ℚ K]` and `haveI : NumberField K` is at L5954;
  * TailF L2293 `qmModelG3_of`, where `K : IF` with `K ≤ L ≤ L'` and `[FiniteDimensional ℚ L']` (TailF L2263). This
    `K` is finite over ℚ, but no instance is in scope.
* **TailH L2659** (`G15Ram.raynaudPlace_of_R6`, `hR6 F O₁ w₁ …`), with `haveI : NumberField F` at L2601. It is
  reached from `localGlue_of_leaves`, `tateWildK_of_R6`, `torsFix_of_descent` and the `LTLocal.*` chain of
  `linkedTateLocal_of_leaves3`.

The reachable r6 consumers are:

* TailC: `good_of_QML3`, `kernelFieldExists_of_{pieces, leaves, leaves_FS5, split, split', split''}`;
* TailF: `qmModelG3_of`;
* TailI: `modelG3G6_of_leaves3`, `linkedTateLocal_of_leaves3`;
* TailM: `raynaudCriterion_ofK5`;
* LPrefix: `QML3.goodReduction`, `goodReduction_of_QM_rational3{,',_of_alg}`;
* TailH: `G15Ram.{raynaudPlace_of_R6, tateWildK_of_R6, localGlue_of_leaves, localGlue_of_descent,
  tateWildKE_of_descent, torsFixWildE_of_twist, torsFixWildOdd_of_descent, torsFix_of_descent}` and
  `LTLocal.{localGlue_at, linkedTateLocalD_of_tateBridge35, linkedTateLocalD_of_tateBridge35',
  linkedTateLocal_of_tateBridge35}`;
* TailK: `gluePieces_of_open4`, which reads `OpenResearchLeaves2.r6`.

**So the restriction is mathematically enough, but not as a fold.** Dropping the field takes three changes:

1. Give `r6 : RaynaudCriterionNF` and `r8 : GrothendieckMonodromyNF` (or drop r8) in new copies of
   `OpenResearchLeaves9, 8, 7, 5, 2` and `ResearchLeaves3`, and of every bundle map between them.
2. Restate the r6 consumers listed above at number fields. `qmModelG3_of` also needs a local `NumberField K`
   instance, built from `K ≤ L'`.
3. Use `GapNeron.r6_r8_NF_of_N1` (or `raynaudCriterion_leavesNF` and `grothendieckMonodromy_final'NF`) for r6 and
   r8, and `ss1_ss3_of_cpNF` as in §3.2.

Under the rule "no existing constant changes", this means copying all of these old generations. That is a
chain-wide refactor, not a fold, and it is the lead's call. Until then, `neronSchemeModelExistsDVR` stays a field.
The reroute of §3.2 alone removes one of its three uses and drops nothing.

**Remark (SPECULATIVE, not checked).** r6 used to be a leaf in printed Galois form ("Leaf I2-Ray",
Objects.lean L1428). A number-field r6 leaf would face the same old-bundle typing problem.

## 4. Method

1. **N1 to a group model.** `ZInQ.Contrib.NeronC.neronModelExists_of_extension hN1 K A K` gives a group model `𝒩`
   of `A_K` over `𝓞_K` with the Néron property (neron-c: group law from the mapping property; uniqueness is
   automatic).
2. **Localize.** `GapBLR.neronLocalizesDVR_proved K A K 𝒩 h𝒩 O` makes `ReductGlue.toO 𝒩 O = 𝒩 ×_{𝓞_K} O` Néron
   over `O`. This step uses `O = (𝓞_K)_{center O}`, which is c-to-printed's `isLocalization_center`.
3. **Change the generic fibre.** Compose the generic-fibre identification with
   `bcSelfIso A : (A.baseChange K).X ≅ A.X`, which is `eqToIso` followed by `Over.pullbackId`. Bijectivity
   survives postcomposition with an isomorphism (`bijective_trans`).
4. **Kernel pitfall (VERIFIED).**
   * With `bcSelfIso` a plain `def`, the kernel times out (deterministic timeout) when checking the bijectivity
     step. `noncomputable irreducible_def` fixes this.
   * `CToPrinted.bijective_comp_iso` needs the source and target Hom types in one category, so the file adds a
     two-category version `bijective_comp_iso'`.
5. **Consumers.** The consumers were copied with `hN` retyped. The trace of the field, r6 and r8 consumers is a
   dependency-closure metaprogram, `scratch/neron-dvr/Reach.lean`, modelled on gt-qm's.

## 5. Files

* `ZInQKernel/Contrib/OneProof/NeronDVR.lean`: the contributor file.
* `scratch/neron-dvr/Draft.lean`: the first scratch proof.
* `scratch/neron-dvr/Discharges.lean`, `discharges.txt`: the `#discharges` run, axioms, and the replacement check.
* `scratch/neron-dvr/Reach.lean`, `reach.txt`: the consumer closure.
* `scratch/neron-dvr/log.md`: the results log.

Locators: BLR, *Néron models* §1.4 Thm. 3, §1.2 Def. 1 and Prop. 4, as in the chain's docstrings (UNVERIFIED, no
network). The proof does not depend on them.
