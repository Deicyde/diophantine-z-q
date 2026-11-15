# gt-sga7: the field `sga7_IX_3_3` from its strictly henselian form

Task gt-sga7, 2026-11-15. Base ef2f6915 (`wip/leaf-fold18`; top module `TailZ29`, `sixContactMin_of_open23`,
61 fields). Lean: `ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean` (the contribution) and `scratch/gt-sga7/`.
This is model work with no human review.

Marks: **VERIFIED** means compiled or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means my own argument. **UNVERIFIED** means a theorem number recalled without a source. There is
no network, so every SGA and BLR locator here is UNVERIFIED.

## 1. Main result

**The field `sga7_IX_3_3` (`CToPrinted.SGA7_IX_3_3`) is discharged exactly as stated (VERIFIED).** It follows from
one new printed-form leaf and three leaves already in the bundles:

```
SGA7PersistsNF.sga7_IX_3_3_of_SH :
  SGA7_IX_3_3_SH → GapSHPair.NeronBaseChangeStrictHenselization → CToPrinted.SGA3_VIB_3_10 →
  AVGlue.GeomConnOfRationalPoint → CToPrinted.SGA7_IX_3_3
```

`#discharges` output (`scratch/gt-sga7/discharges-output.txt`, run over the built `Main`, `Discharges` and the new
module):

```
DISCHARGES [OpenResearchLeaves19.sga7_IX_3_3] by SGA7PersistsNF.sga7_IX_3_3_of_SH
  still assumes: [SGA7PersistsNF.SGA7_IX_3_3_SH,
 GapSHPair.NeronBaseChangeStrictHenselization,
 CToPrinted.SGA3_VIB_3_10,
 AVGlue.GeomConnOfRationalPoint]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 68 open hypotheses, 982 theorems checked, 4 discharge one
```

The other three DISCHARGES lines in that output are contributions already in the tree. Of the four hypotheses
still assumed, only `SGA7_IX_3_3_SH` is new. `neronBaseChangeStrictHenselization` and `sga3_VIB_3_10` are fields of
the research bundle. `geomConnOfRationalPoint` is a field of the textbook bundle.

**The fold compiles (VERIFIED).** `scratch/gt-sga7/fold-spec.json` is the spec. `autofold.py --dry-run` writes
nothing to the tree and reports `strict count: 49/12 on 61 -> 50/11 on 61; strictest 48/13 -> 49/12`. Its output,
with the count line stripped (`scratch/gt-sga7/FoldDryRun.lean`), compiles in 6 s. In that output
`HDec.HSyn.sixContactMin_of_open24` depends only on the standard axioms. The spec fills the field with
`sga7_IX_3_3_of_SH {n}.sga7_IX_3_3_SH {n}.neronBaseChangeStrictHenselization {n}.sga3_VIB_3_10
{t}.geomConnOfRationalPoint`.

**The task's premise needed one correction (VERIFIED).** The field is the **second** assertion of SGA 7 IX 3.3
(`N⁰ ×_R R' ≅ N'⁰`). The chain's leaf `ReductB.SemistablePersistsSHcp` (TailZ23 L315) is the **first** assertion:
semistable reduction persists. The first assertion does not imply the second, so the chain's current leaves cannot
discharge the field. Two things are required:
- a strictly henselian form of the second assertion, which enters as a new leaf;
- strict henselization with descent, which is what the task suggested.

Task sh-printed2 (`origin/wip/sh-printed2`, 11-14, never folded) did the same reduction in characteristic 0, on
the older base b5ff0474, from sh-route's char-0 Néron leaf. This file ports that argument to the current chain.
- **Commutative algebra.** It now comes from gt-shpair's `GapSHPair.strictHenselizationPair_of_neron`, which works
  in every characteristic and for every residue field.
- **Effect on the leaf.** The SH leaf needs no characteristic hypothesis, and the conclusion is the field itself,
  not a char-0 variant.

## 2. The statements (`SGA7PersistsNF.lean`)

**LEAF `SGA7_IX_3_3_SH`** (SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly henselian traits; number
UNVERIFIED). It is `CToPrinted.SGA7_IX_3_3` word for word, with two hypotheses added: `IsStrictlyHenselianDVR O`
and `IsStrictlyHenselianDVR O'` (reduct-glue's predicate: a DVR, henselian, with separably closed residue field).
- The conclusion is the field's: for `U = (𝒩 ×_O O')⁰` and the comparison homomorphism `c` (an isomorphism on the
  generic fibre), `U → 𝒩'` is an open immersion with image `𝒩'⁰`.
- `sga7_IX_3_3_SH_of_field` checks in Lean that it is a specialization of the field.

**LEAF (restricted) `SGA7_IX_3_3_SHcp`.** It is `SGA7_IX_3_3_SH` with `[CharZero K]` and `[PerfectField κ(O)]`
added. The residue field is then separably closed and perfect, hence algebraically closed. This is the same
restriction the chain uses for the first assertion (`SemistablePersistsSHcp`). `sga7_IX_3_3_SHcp_of_SH` checks in
Lean that it is a specialization.

**`SGA7_IX_3_3cp`** is the field with `[CharZero K]` and `[PerfectField κ(O)]` added. It is the form the one
consumer actually needs.

## 3. The proofs (all VERIFIED by compilation; 10 s, 8.5 GB; standard axioms)

The core lemma is `body_of_SH`. Its hypotheses are:
- DVRs `O ⊆ O'`;
- strict henselizations `P ⊇ O` and `P' ⊇ O'` in the sense of `ReductGlue.IsSHNeronExt` (Néron models base change);
- the condition `P' ∩ E = P`;
- the statement at `(P, P')`.

Its conclusion is the statement at `(O, O')`. The proof is sh-printed2's `sga7_IX_3_3_0_of_SH`, unchanged except
for its inputs:
1. **Néron models.** `𝒩 ×_O P` and `𝒩' ×_{O'} P'` are Néron models (`IsSHNeronExt`). Semistability passes to `P`
   through reduct-glue's `isSemistable_bcDVR_iff`. The model over `P'` is transported along `bcbcIso`.
2. **The comparison map over `P'`.** It is `c₁ = e ≫ (c ×_{O'} P')`, where `e` is built from two `pbCompIso`.
   - `c₁` is a homomorphism.
   - Its generic fibre is an isomorphism (`pbCompIso_natural'` twice).
   - `U₁ = (𝒩₁ ×_P P')⁰` is open by SGA 3 VI_B 3.10.

   The SH statement makes `U₁ → 𝒩'₁` an open immersion with image `𝒩'₁⁰`.
3. **Descent along `Spec P' → Spec O'`.**
   - **The base map is faithfully flat** (`flat_surjective_gD`): torsion-free over the Bezout domain `O'`, and a
     local homomorphism.
   - **The open immersion descends** (`descend_openImm`), by Mathlib's
     `IsOpenImmersion.DescendsAlong (Surjective ⊓ Flat ⊓ QuasiCompact)`.
   - **The image descends.** This uses `CToPrinted.idComp_baseChange`, which comes from SGA 3 VI_B 3.10 and
     Stacks 04KV.

The two main theorems apply `GapSHPair.strictHenselizationPair_of_neron hN` and then `body_of_SH`:
- `sga7_IX_3_3_of_SH` applies them directly.
- `sga7_IX_3_3cp_of_SHcp` first transfers `CharZero` to `E` (`ReductB.charZero_of_algebra`) and perfectness to
  `κ(P)` (`ReductB.perfectField_of_isSHNeronExt`).

The helpers `pbCompIso_fst`, `pbCompIso_inv_fst`, `comapHom_injective`, `flat_surjective_gD`, `isPullback_bc`,
`isPullback_bc_iso` and `descend_openImm` are sh-printed2's. None of them is in the chain; I checked by searching
for the names and the Mathlib lemmas they use. `pbCompIso_fst` now uses the vendored
`CategoryTheory.Over.pullbackComp_hom_app_left_fst_fst` by import instead of a copy.

**The consumer, rerouted** (for the restricted route, §4 option B).
- `identityComponentBaseChangeDVRRangeCP_of` and `semistableNeronBaseChange_of_printed_cp` restate
  `CToPrinted.identityComponentBaseChangeDVRRange_of` and `CToPrinted.semistableNeronBaseChange_of_printed_full`
  with `h7 : SGA7_IX_3_3cp`.
- The only changes are the hypothesis, the restricted Prop `IdentityComponentBaseChangeDVRRangeCP` and one
  `haveI` for `PerfectField κ(O)`, which comes from the chain's `ReductB.perfectField_residue_nf`.
- `semistableNeronBaseChange_of_SHcp hB h3 h7cp hN hE hG` is the term to use at the consumer sites.

## 4. Fold options

| option | new leaf | kind and flag | fold | count |
|---|---|---|---|---|
| A (recommended) | `sga7_IX_3_3_SH : SGA7PersistsNF.SGA7_IX_3_3_SH` | published; reading risk, as for the chain's `raynaudSemistableSH`: the print may assume an algebraically closed residue field | automatic: `scratch/gt-sga7/fold-spec.json`, compiled as a dry run | strict 49/12 → 50/11; strictest 48/13 → 49/12 |
| B | `sga7_IX_3_3_SHcp : SGA7PersistsNF.SGA7_IX_3_3_SHcp` | published; restricted, a specialization of every reading | manual bypass (below) | the same, with no reading risk |

**Option B cannot be folded automatically.** Every bundle generation since leaf-fold12 carries the field with the
full type `CToPrinted.SGA7_IX_3_3`, and the restricted leaf cannot fill that type. A fold has to replace the one
consumer term, `CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4 r.sga3_VIB_3_10 r.sga7_IX_3_3
r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint`, with
`SGA7PersistsNF.semistableNeronBaseChange_of_SHcp r.blr_1_2_4 r.sga3_VIB_3_10 r.sga7_IX_3_3_SHcp
<neronBaseChangeStrictHenselization> r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint`. The consumer sites are:
- `ZInQKernel/OneProof/H/TailZ23.lean` L794, in `HDec.HSyn.researchLeaves9_of_open14`. This is the live path: Main
  goes TailZ29 → … → TailZ23 → `sixContactMin_of_open11`.
- `ZInQKernel/OneProof/H/TailZ19.lean` L1894, in `researchLeaves11_of_open12`, an older conversion.
- `ZInQKernel/OneProof/H/TailZ19.lean` L1775, in `fields_of_leaves`, the `CToPrintedLeaves` bundle (not on
  Main's path).

The fold would then map new generations of TailZ23…TailZ29 to `OpenResearchLeaves14`, with the field replaced (the
bypass of memory note "fold with a weaker leaf"). That is integrator work. The Lean terms it needs are all in the
file.

**Why A is acceptable** (SPECULATIVE argument; the inputs are STANDARD, numbers UNVERIFIED). The reading risk
concerns only an imperfect separably closed residue field `k`. There the chain's `HasSemistableReduction` asks for
semi-abelian `N⁰` on the geometric special fibre, while a print over `k` would ask for `N⁰_k` semi-abelian over
`k`. The two agree:
- a smooth connected commutative `k`-group `G` has a maximal torus `T` over `k` that stays maximal over `k̄` (SGA 3
  XIV 1.1, UNVERIFIED);
- `G/T` is smooth and connected, and `(G/T)_{k̄}` is an abelian variety;
- properness descends, so `G/T` is an abelian variety over `k`.

So option A is no stronger than an SH print that defines semistability over `k`. If the print assumes an
algebraically closed residue field outright, option B is the print, and option A would be stronger only at
imperfect residue fields. That is the same risk the chain already accepts for `raynaudSemistableSH`.

## 5. Statement review

- **No statement was changed.** `CToPrinted.SGA7_IX_3_3` is proved with its own type: `#discharges` matched it.
- **The field is not false, vacuous or inert.** Its use at number fields is live (§4), and its hypotheses are
  satisfiable.
- **The new leaves are not vacuous.** Their strictly henselian hypotheses hold at every use, by
  `GapSHPair.shPair`: the inertia-field valuation rings are strictly henselian DVRs.
- **Neither new leaf is stronger than the field.** `sga7_IX_3_3_SH_of_field` and `sga7_IX_3_3_SHcp_of_SH` check
  this in Lean.

## 6. What remains

1. **Locator.** SGA 7 I, Exp. IX, Prop. 3.3 has not been read. Still open: its number, whether it is stated over
   strictly henselian traits or any traits, and whether it assumes an algebraically closed residue field. A
   reading decides between options A and B (and whether the original field was already a leaf, if 3.3 is printed
   over any trait).
2. **Integration.** For option A, run the automatic fold with `scratch/gt-sga7/fold-spec.json`. Then add a row
   for `sga7_IX_3_3_SH` in `docs/research/locators.md`; the kinds row is written by `autofold.py`.

## 7. Files

- `ZInQKernel/Contrib/OneProof/SGA7PersistsNF.lean`: the contribution. It imports
  `ZInQKernel.OneProof.H.TailZ23` (which brings in TailZ19, where the statement is defined, and gives `ReductB`'s
  lemmas), `ZInQKernel.Contrib.OneProof.StrictHenselizationPair` and the vendored `…Comma.Over.Pullback`.
- `scratch/gt-sga7/Discharges.lean`, `discharges-output.txt`: the check and its output (with `#print axioms` of the
  four main theorems: all `[propext, Classical.choice, Quot.sound]`).
- `scratch/gt-sga7/fold-spec.json`, `FoldDryRun.lean`: the option A fold, compiled.
- `scratch/gt-sga7/ref/`: sh-printed2's `PartS`, `PartU` and `Head`, for reference only (not compiled here).
- `scratch/gt-sga7/log.md`: the results log.
