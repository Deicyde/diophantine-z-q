# sga33-shpre: the field `sga7_IX_3_3_SHpre` restricted to what its consumers use (SGA 7 IX 3.3 over traits with algebraically closed residue fields)

Task sga33-shpre, 2026-11-16. Base `wip/sga33-shpre` = 5e235a40 (origin/main and origin/wip/integrate-w82 were
already merged). This is model work with no human review. Marks: **VERIFIED** = compiled, or read in a file;
**STANDARD** = published, with an exact reference; **SPECULATIVE** = a judgement; **UNVERIFIED** = a theorem number
recalled without a source (no network on this host).

## 1. Verdict

Route (c) of the task. **Every use the chain makes of `sga7_IX_3_3_SHpre` is at characteristic 0 with a perfect
residue field.** Strictly henselian, that means an algebraically closed residue field. So the field can be replaced by
its restriction to traits with algebraically closed residue fields, `DictModels.SGA7PreAC.SGA7_IX_3_3_SHpreAC`. That
restriction is a specialization of SGA 7 IX 3.3 under every reading of the print's residue-field hypothesis, and that
hypothesis was the only reason the row was rated GLUE (VERIFIED, kinds.tsv row and OPEN.md entry).

* New leaf (printed form, restricted; §3): `SGA7_IX_3_3_SHpreAC` is the field word for word, with
  `[IsAlgClosed κ(O)]` and `[IsAlgClosed κ(O')]` added.
* Both consumers are proved from it in Lean (VERIFIED, compiled, standard axioms only), in
  `ZInQKernel/Contrib/OneProof/SGA7IX33SHPreAC.lean`.
* The fold is checked in `scratch/sga33-shpre/Bypass.lean` (§4). Since the leaf is weaker than the field,
  `autofold.py` cannot write this fold. With the new leaf rated LEAF, the fold takes the strict GLUE count down by 1
  (the target). The field `sga7_IX_3_3_SHpre` itself is **not** proved, and cannot be proved from the new leaf.

## 2. Statement and consumers (VERIFIED, read in files)

Field `HDec.HSyn.OpenResearchLeaves28.sga7_IX_3_3_SHpre : DictModels.SGA7Pre.SGA7_IX_3_3_SHpre`
(`ZInQKernel/Contrib/OneProof/SGA7IX33SHPre.lean`). It covers all strictly henselian `O ⊆ O'` with `K'/K` finite,
`A` semistable, `𝒩`, `𝒩'` Néron models, `c : 𝒩 ×_O O' → 𝒩'` a homomorphism with generic fibre an isomorphism, and
`U = pullback.fst ⁻¹' 𝒩⁰`. The conclusion: `U → 𝒩'` is an open immersion with image `𝒩'⁰`. kinds.tsv rates it
published, strict GLUE, with the flag "SGA 7 IX 3.3 may assume an algebraically closed residue field".

The field reaches the chain through `sga7_IX_3_3_SH` (TailZ45). That is read at two places, and only the
pass-through maps of TailZ34/35/37/38 handle it in between:

| site | term | where the statement is used |
| --- | --- | --- |
| TailZ41 (R26 → R25) | `semistablePersistsSHcp := GapPersists.semistablePersistsSHcp_of_SH …` | `ReductB.SemistablePersistsSHcp`: `[CharZero K]`, `[PerfectField κ(O)]`, `O` strictly henselian |
| TailZ33 (R20 → R19), then TailZ23 | `sga7_IX_3_3 := sga7_IX_3_3_of_SH …`, read only by `researchLeaves9_of_open14`: `semistableNeronBaseChange := semistableNeronBaseChange_of_printed_full …` | `K = L` a number field, residue fields finite (gt-sga7's docstring; the cp reroute `semistableNeronBaseChange_of_printed_cp` already exists in SGA7PersistsNF.lean) |

## 3. The new leaf and its rating

```lean
def DictModels.SGA7PreAC.SGA7_IX_3_3_SHpreAC : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAlgClosed (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] [IsAlgClosed (IsLocalRing.ResidueField O')], IsStrictlyHenselianDVR O' →
    -- the rest exactly as SGA7_IX_3_3_SHpre
```

**Rating: printed form (restricted). It counts LEAF.** Proposed flag: "restricted: algebraically closed residue fields
(k(s) and k(s')), a specialization of the print under every reading of its residue-field hypothesis; locator
UNVERIFIED". The reasons:

* The print may be stated over arbitrary or strictly henselian traits. Then the leaf is a specialization
  (`preAC_of_pre`, VERIFIED, from the field).
* The print may assume an algebraically closed residue field, on `S` or on both traits. Then the leaf has exactly
  that hypothesis. The second instance is redundant: `κ(O')` is algebraic over `κ(O)`. It is stated so that the leaf
  is a specialization even under the "both traits" convention.
* The residue field is algebraically closed, so the two readings of "semistable" coincide mathematically: over
  `k(s)`, and on the geometric fibre `κ̄`, which is the kernel's `GroupModelO.IsSemistable`. This is the
  `SemiAbelianDescendsSepClosed` axis with `k = k̄`, which is trivial in mathematics but not proved in Lean.
  SPECULATIVE judgement that this is dictionary, not a reading risk.
* The other dictionary items are unchanged from dict-models §2: `U` is the print's `N⁰ ×_S S'`; the conclusion
  restates "isomorphism onto `N'⁰`", `N'⁰` being open; `c` is any homomorphism with generic fibre an isomorphism;
  `K'/K` is finite (a specialization).

## 4. Lean (all VERIFIED: compiled with `lake env lean`, standard axioms)

`ZInQKernel/Contrib/OneProof/SGA7IX33SHPreAC.lean` (imports `SGA7IX33SHPre`, `PersistsDVR`):

* `DictModels.SGA7PreAC.preAC_of_pre : SGA7_IX_3_3_SHpre → SGA7_IX_3_3_SHpreAC` (never stronger than the field).
* `SGA7_IX_3_3_SHcp_of_preAC : SGA7_IX_3_3_SHpreAC → SGA3_VIB_3_10 → GeomConnOfRationalPoint →
  SGA7PersistsNF.SGA7_IX_3_3_SHcp`. `κ(O)` is perfect and separably closed. `κ(O')` is algebraic over `κ(O)`
  (`GapPersists.isAlgebraic_resMap`), hence perfect, and it is separably closed. The two opens agree by
  `SGA7Pre.preimage_eq` (SGA 3 VI_B 3.3, proved in the chain).
* `sga7_IX_3_3cp_of_preAC`: the DVR form at characteristic 0 with perfect residue field, by gt-sga7's descent
  `sga7_IX_3_3cp_of_SHcp` (needs `NeronBaseChangeStrictHenselization`, which the bundle gets from `blr_7_2_1`).
* `GapPersists.semistablePersistsDVRcp_of_cp`, `semistablePersistsSHcp_of_cp`: persists-dvr's proof of
  `semistablePersistsDVR_of_printed`, with `SGA7_IX_3_3cp` and `identityComponentBaseChangeDVRRangeCP_of`.
* **Consumer 1** `semistablePersistsSHcp_of_preAC : SGA3_VIB_3_10 → SGA7_IX_3_3_SHpreAC →
  NeronBaseChangeStrictHenselization → GeomConnOfRationalPoint → ReductB.SemistablePersistsSHcp`.
* **Consumer 2** `semistableNeronBaseChange_of_preAC : BLR_1_2_4 → SGA3_VIB_3_10 → SGA7_IX_3_3_SHpreAC →
  NeronBaseChangeStrictHenselization → EGAIV_8_10_5_openImm → GeomConnOfRationalPoint → SemistableNeronBaseChange`.

**The fold** (`scratch/sga33-shpre/Bypass.lean`, 1719 lines, generated by `gen_bypass.py`; VERIFIED: `lake env lean` with no errors in 81 s, and `'HDec.HSyn.sixContactMin_of_open39' depends on axioms: [propext, Classical.choice, Quot.sound]`):

* a new bundle `OpenResearchLeaves29` (R28 with `sga7_IX_3_3_SHpre` replaced by `sga7_IX_3_3_SHpreAC`);
* in the namespace `HDec.HSyn.SHpreBypass`, copies of the research generations 14..27. Their field is weakened: in
  generations 20..27 `sga7_IX_3_3_SH` becomes `SGA7_IX_3_3_SHpreAC`, and in generations 14..19 `sga7_IX_3_3` becomes
  `SGA7_IX_3_3cp`;
* copies of every theorem on the route that takes one of those bundles: the maps, `x6Rows_of_open14`,
  `ss1_ss3_of14NF`, `raynaudCriterionNF_of14`, `researchLeaves9_of_open14`, `addedLeaves9_of_open14`, SGRFold's
  three, `openGlue7_of_OpenGlue8` and the stack theorems 17..37. Name resolution inside the namespace picks up the
  copies.
* Four lines are edited: TailZ45's conversion (`sga7_IX_3_3_SH := n.sga7_IX_3_3_SHpreAC`), TailZ41
  (`semistablePersistsSHcp_of_preAC`), TailZ33 (`sga7_IX_3_3cp_of_preAC`) and TailZ23 (`semistableNeronBaseChange_of_printed_cp`).
* `HDec.HSyn.sixContactMin_of_open39 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19) :
  ZInQ.SixContactMin`.

This is the leaf-fold14 bypass pattern. It is larger here because the field threads through 14 generations. The fold
adds new constants only, so no existing constant changes.

### `#discharges` and axioms (VERIFIED)

`scratch/sga33-shpre/Discharges.lean` (imports Main, Discharges, the new file; output in `discharges.txt`) prints 13
DISCHARGES lines. **None comes from the new file.** That is expected: the new leaf is weaker than the field, so no
theorem has the field's type. The only line on `sga7_IX_3_3_SHpre` is dict-models' existing `pre_of_SH`, which assumes
the old field `sga7_IX_3_3_SH`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `preAC_of_pre`,
`SGA7_IX_3_3_SHcp_of_preAC`, `sga7_IX_3_3cp_of_preAC`, `semistablePersistsSHcp_of_preAC` and
`semistableNeronBaseChange_of_preAC` (`axioms.txt`).

### Effect on the counts

The fold removes one strict-GLUE row (`sga7_IX_3_3_SHpre`, GLUE/GLUE) and adds one row that is proposed LEAF/LEAF
(`scratch/sga33-shpre/kinds-row-proposed.tsv`; the flag class is `restricted,unverified-locator`, like the
`restricted` rows hL29, hP23 and hfx). Strict GLUE goes down by 1, and so does strictest GLUE. The total field count is
unchanged.

## 5. What remains

* `sga7_IX_3_3_SHpre` itself (any residue field) is not proved. SGA 7 IX 3.3 from first principles needs a lemma like
  this one: a homomorphism of smooth group schemes over a trait, generic iso, source with connected semi-abelian
  special fibre, is an open immersion. The proof uses ℓ-torsion of semi-abelian varieties, étale lifting over
  strictly henselian bases and ZMT. None of that is in the kernel (SPECULATIVE estimate: weeks).
* The integrator has to run the fold (copy Bypass.lean to TailZ46, switch Main, add the kinds.tsv row from
  `scratch/sga33-shpre/autofold.json`, remove the old row), then regenerate OPEN.md.
* locators.md row for the new leaf: same locator as `sga7_IX_3_3_SHpre`, UNVERIFIED.
