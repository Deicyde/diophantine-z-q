# sh-printed2: `blr_1_2_4` and `sga7_IX_3_3` from their strictly henselian forms

Task sh-printed2, 2026-11-14. Base b5ff0474 (w63, leaf-fold12: `sixContactMin_of_open15`, 61 fields).
Lean: `scratch/sh-printed2/`. `chk.sh` assembles `ShPrinted2.lean` and checks it with one Lean process. The file
is made of:
- `Head.lean` (`import ZInQKernel.OneProof.H.TailZ19`);
- sh-route's `Top`, `CA1`, `CA2`, `CA3`, `Final` (`SR_*.lean`, byte-identical to `origin/wip/sh-route`);
- this task's `PartB`, `PartS`, `PartU`, `PartF`.

Result of the check:
- `lake env lean` runs in 30 s, 8.7 GB, with 0 errors (VERIFIED);
- all 22 `#print axioms` report `[propext, Classical.choice, Quot.sound]` (`axioms.txt`);
- there is no `sorry` and no `axiom`;
- nothing under `ZInQKernel/` or `blueprint/` was edited.

Results log: `scratch/sh-printed2/log.md`. This is model work with no human review.

Marks: **VERIFIED** means compiled or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means my own argument. **UNVERIFIED** means a theorem number recalled without a source. There is
no network, so every BLR and SGA locator here is UNVERIFIED.

## 1. Main result

**Both fields are now Lean theorems from their strictly henselian forms (VERIFIED).** The setting is fields of
characteristic 0, plus a perfect residue field for the SGA 7 statement. The only inputs are:
- sh-route's Néron leaf `NeronBaseChangeSH`;
- leaves already in the bundles;
- commutative algebra and descent, proved here or in Mathlib.

No glue is left.

```
blr_1_2_4_0_of_SH    : BLR_1_2_4_SH → BLR_1_2_4_0
sga7_IX_3_3_0_of_SH  : SGA7_IX_3_3_SH → ShRoute.NeronBaseChangeSH → SGA3_VIB_3_10 →
                         AVGlue.GeomConnOfRationalPoint → SGA7_IX_3_3_0
HDec.HSyn.sixContactMin_of_open15SH :
  OpenResearchLeaves12SH → OpenTextbookLeaves10 → OpenAddedLeaves11 → OpenGlue7 → ZInQ.SixContactMin
```

- **`BLR_1_2_4_0` and `SGA7_IX_3_3_0`.** These are c-to-printed's `CToPrinted.BLR_1_2_4` and
  `CToPrinted.SGA7_IX_3_3` word for word, with hypotheses added:
  - `BLR_1_2_4_0` adds `[CharZero K]`;
  - `SGA7_IX_3_3_0` adds `[CharZero K]` and `[PerfectField (IsLocalRing.ResidueField O)]`.

  `blr_1_2_4_0_of_field` and `sga7_IX_3_3_0_of_field` check in Lean that each is a specialization of the field
  statement.
- **The uses still type-check.** Every use of the two fields is at a number field and a DVR of it (§4). The
  residue field there is finite, so it is perfect (`perfectField_residueField`, proved).
- **The new bundle.** `OpenResearchLeaves12SH` is leaf-fold12's `OpenResearchLeaves12` with three changes:
  - `blr_1_2_4` becomes `blr_1_2_4_SH`;
  - `sga7_IX_3_3` becomes `sga7_IX_3_3_SH`;
  - sh-route's `neronBaseChangeSH` is added.

  A Python diff against TailZ19 confirms that only these lines change. `sixContactMin_of_open15SH` is
  `sixContactMin_of_open15` with this bundle.

## 2. The statements (Lean, `PartB.lean`, `PartS.lean`)

**LEAF `BLR_1_2_4_SH`** (BLR, *Néron models*, §1.2 Prop. 4, strict-henselization reading; UNVERIFIED).
- **Setting.** `R` is a Dedekind domain whose fraction field `K` has characteristic 0. `X` is a smooth,
  separated, quasi-compact `R`-scheme.
- **Statement.** `IsNeronModelOver R K X` holds if and only if the following holds for every maximal `𝔭`, every
  valuation subring `O ⊆ K` with `IsLocalization.AtPrime O 𝔭`, and every `O₁ ⊆ K₁` with
  `ShRoute.IsSHUnram O O₁ hO`: the pullback `X ⊗_R O₁` along `R → O → O₁` satisfies
  `IsNeronModelOver O₁ K₁ (X ⊗_R O₁)`.
- **What `IsSHUnram` says.** `O₁` is a strictly henselian DVR, `K₁/K` is algebraic, the ramification index is 1,
  and the residue extension is separable.
- **Why this stands for the strict henselization.** In characteristic 0 these conditions force `O → O₁` to be
  `O → O^sh`, up to isomorphism over `O` (sh-route §3).

**LEAF `SGA7_IX_3_3_SH`** (SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly henselian traits;
UNVERIFIED).
- It is c-to-printed's `SGA7_IX_3_3` with three hypotheses added: `IsStrictlyHenselianDVR O`,
  `IsStrictlyHenselianDVR O'` (reduct-glue's predicate: henselian, with separably closed residue field) and
  `[CharZero K]`.
- The conclusion is unchanged: for `U = (𝒩 ×_O O')⁰`, the map `U → 𝒩'` is an open immersion with image `𝒩'⁰`.

**LEAF `ShRoute.NeronBaseChangeSH`** (sh-route; BLR §7.2 Thm. 1 / §1.2 Prop. 2; UNVERIFIED). It says that Néron
models of abelian varieties base change along `IsSHUnram` extensions, for `K` of characteristic 0.

Neither strictly henselian form carries `[NumberField K]`, as the task required.

## 3. The proofs (all VERIFIED by compilation)

### `blr_1_2_4_0_of_SH` (`PartB.lean`)

Over `R` the localization form is the strict-henselization form applied twice: once over `R` and once over the
Dedekind domain `R_𝔭`, whose only closed point has the same strict henselizations. No other leaf is used.
- **(⟹)** Apply the SH form over `R_𝔭`, which is Dedekind by `IsLocalization.isDedekindDomain`. Its
  localization `O` at its maximal ideal is also a localization of `R` at `𝔭`
  (`isLocalization_isLocalization_atPrime_isLocalization`, `AtPrime.under_maximalIdeal`). So the SH form over
  `R` gives the Néron property over each `O₁`.
- **(⟸)** Take `R_𝔭 := O` in the localization hypothesis. Then apply the SH form over the DVR `O`, with
  `O = O_{max}` by `IsLocalization.of_le_isUnit`.
- **Transport.** Two tools carry the property between the forms:
  - `isNeronModelOver_of_iso`: the Néron property is invariant under isomorphism;
  - `pb_comp_iso`: pullback along a composite is the composite of pullbacks (`Over.pullbackComp`).
- **The use.** `neronLocalizesDVR_of_printed0` is c-to-printed's proof verbatim, with hypothesis `BLR_1_2_4_0`.

### `sga7_IX_3_3_0_of_SH` (`PartS.lean`)

Given `O ⊆ O'`, `𝒩`, `𝒩'`, `c` and `U = idCompSet (𝒩 ×_O O')`:

1. **Strict henselizations.** sh-route's `strictHenselizationPair0_final` (from `NeronBaseChangeSH` and the
   proved `shPair0`) gives `P ⊇ O` and `P' ⊇ O'`. Both satisfy `IsSHNeronExt`, `E'/E` is finite, and
   `P' ∩ E = P`.
2. **Néron models over `P` and `P'`.**
   - Over `P`: `𝒩₁ = 𝒩 ×_O P` is a Néron model. Semistability passes to it through reduct-glue's
     `isSemistable_bcDVR_iff`.
   - Over `P'`: `𝒩'₁ = 𝒩' ×_{O'} P'` is a Néron model. It is transported to `((A_E)_{E'})` along
     `bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm`.
3. **The comparison map over `P'`.** It is `c₁ = e ≫ (c ×_{O'} P')`, where
   `e : (𝒩₁ ×_P P') ≅ (𝒩 ×_O O') ×_{O'} P'` is built from two `pbCompIso`.
   - `c₁` is a homomorphism.
   - Its generic fibre is an isomorphism, by `pbCompIso_natural'` applied twice, starting from `hciso`.
   - Its source opens are `U₁ = idCompSet`, which is open by `SGA3_VIB_3_10`.

   The SH leaf then makes `U₁ → 𝒩'₁` an open immersion with image `𝒩'₁⁰`.
4. **Descent along `p : 𝒩'₁ → 𝒩'`.** `p` is the base change of `Spec P' → Spec O'`.
   - **`Spec P' → Spec O'` is faithfully flat** (`flat_surjective_gD`). `P'` is torsion-free over the Bezout
     domain `O'`, and a local flat map is faithfully flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`,
     `flat_and_surjective_SpecMap_iff`).
   - **The square is a pullback.** `U₁ → 𝒩'₁` over `U → 𝒩'` pastes from `isPullback_morphismRestrict` and the
     base-change square (`isPullback_bc_iso`).
   - **`U₁ = q⁻¹U`.** This needs `idComp_baseChange` (c-to-printed, from SGA 3 VI_B 3.10 and Stacks 04KV) three
     times, plus `pbCompIso_fst`.
   - **The open immersion descends** by Mathlib's fpqc descent
     (`MorphismProperty.of_isPullback_of_descendsAlong`, with
     `IsOpenImmersion.DescendsAlong (Surjective ⊓ Flat ⊓ QuasiCompact)`).
   - **The image descends.** `range(top) = p⁻¹(range)` (`Scheme.Pullback.range_fst`),
     `p⁻¹(𝒩'⁰) = 𝒩'₁⁰` (`idComp_baseChange`), and `p` is surjective.

   All of step 4 is the generic lemma `descend_openImm`.

## 4. The uses (checked in TailZ19)

| field | use in TailZ19 | where it is applied | `…0` hypotheses there |
|---|---|---|---|
| `blr_1_2_4` | `neronLocalizesDVR_of_printed`, field `neronLocalizesDVR` | `R = 𝓞_L`, `K = L` a number field | `CharZero L`: instance |
| `sga7_IX_3_3` | `identityComponentBaseChangeDVRRange_of`, used once, in `semistableNeronBaseChange_of_printed_full` (field `semistableNeronBaseChange`) | `(L, O, L', O')`, with `L, L'` number fields and `O = O' ∩ L` a DVR | `CharZero L`: instance; `PerfectField κ(O)`: `perfectField_residueField` (κ(O) ≅ 𝓞_L/𝔭 is finite) |

`identityComponentBaseChangeDVRRange0_of` and `semistableNeronBaseChange_of_printed_full0` (`PartU.lean`) are
verbatim copies of these two proofs. Only four things change:
- the hypotheses become `…0`;
- the intro pattern of the restricted Prop changes;
- one `haveI` supplies the perfect residue field;
- `neronLocalizesDVR_of_printed0` is called in place of c-to-printed's version.

## 5. Field table (research bundle; the other 59 fields of `sixContactMin_of_open15` unchanged)

| before (`OpenResearchLeaves12`, 32) | kind before (strict convention) | after (`OpenResearchLeaves12SH`, 33) | kind after |
|---|---|---|---|
| `blr_1_2_4 : CToPrinted.BLR_1_2_4` | LEAF, consequence (print may be over `𝒪^{sh}`) | `blr_1_2_4_SH : SHPrinted2.BLR_1_2_4_SH` | LEAF, printed form if BLR 1.2/4 is printed with `𝒪^{sh}_{S,s}` (char 0; see §6) |
| `sga7_IX_3_3 : CToPrinted.SGA7_IX_3_3` | LEAF, consequence (print may be over strictly henselian traits) | `sga7_IX_3_3_SH : SHPrinted2.SGA7_IX_3_3_SH` | LEAF, printed form if SGA 7 IX is printed over strictly henselian traits; a specialization of the general-trait form otherwise (`sga7_IX_3_3_SH_of_field`) |
| (none) | | `neronBaseChangeSH : ShRoute.NeronBaseChangeSH` | LEAF, printed form (BLR 7.2/1 / 1.2/2; in char 0 the strict-henselization statement up to isomorphism, sh-route §3); shared with sh-route's route for `raynaudSemistable`, `semistablePersistsDVR`, `semistableUnipotent` |
| | | GLUE | none: `blr_1_2_4_0_of_SH`, `sga7_IX_3_3_0_of_SH`, `finite_residueField`, the descent lemmas, the uses and the bundle conversion are all proved |

The leaves already in the bundles stay unchanged: `sga3_VIB_3_10` and `egaIV_8_10_5_openImm` (research), and
`geomConnOfRationalPoint` (textbook). sh-route's commutative algebra (`shPair0`, `shExists0`) is proved.

## 6. Review of the statements

**`SGA7_IX_3_3_SH` is never stronger than the print** under either reading of SGA 7 IX:
- if SGA 7 IX is printed over strictly henselian traits, `SGA7_IX_3_3_SH` is the print;
- if it is printed over any trait, `SGA7_IX_3_3_SH` is a specialization of the print (Lean:
  `sga7_IX_3_3_SH_of_field`).

**`BLR_1_2_4_SH` depends on the reading** (SPECULATIVE):
- **Strict-henselization reading** (what the task asks for). `BLR_1_2_4_SH` is the print, transported along
  `O₁ ≅ O^sh`, which holds in characteristic 0 by sh-route §3. That argument is SPECULATIVE; its inputs are
  STANDARD (EGA IV₄ §18.8).
  - (⟸): `O^sh` itself (a valuation subring of `K^sh`) is among the `O₁`.
  - (⟹): every `O₁` is isomorphic to `O^sh`.
- **Localization reading.** If BLR 1.2/4 is printed with `𝒪_{S,s}`, then `BLR_1_2_4_SH` is not a single printed
  statement. It would follow from the print together with:
  - BLR 1.2/2 (Néron models commute with strict henselization);
  - descent of the Néron property from `O^sh` to `O`.

  In that case the bundle should keep c-to-printed's `BLR_1_2_4`. Both routes compile:
  `blr_1_2_4_0_of_field : BLR_1_2_4 → BLR_1_2_4_0` and `blr_1_2_4_0_of_SH : BLR_1_2_4_SH → BLR_1_2_4_0` feed the
  same `neronLocalizesDVR_of_printed0`.

  Recommendation: whoever opens BLR picks the field matching §1.2 Prop. 4 as printed.

**Neither form is vacuous.**
- `shUnram_exists_numberField` (proved) shows that every DVR of a number field has an `IsSHUnram` extension. So
  the right side of `BLR_1_2_4_SH` ranges over a nonempty set.
- The SH hypotheses of `SGA7_IX_3_3_SH` hold at every use, by `shPair0`.
- For a field `R`, no `IsSHUnram` extension exists: an algebraic extension cannot carry a DVR containing `K`.
  The right side of `BLR_1_2_4_SH` then holds vacuously. The left side also holds (SPECULATIVE, not
  formalized): pullback along the isomorphism `Spec K → Spec R` is an equivalence. So the leaf is true there.

**Hypotheses added.**
- `[CharZero K]` appears on all four new statements. It is needed to identify `IsSHUnram` with `O^sh` (sh-route
  §3) and in `shPair0`.
- `[PerfectField κ(O)]` appears only on `SGA7_IX_3_3_0`, because `shPair0` uses it (Mathlib's
  `card_inertia_eq_ramificationIdxIn`).

## 7. What remains

1. **Locators.** All BLR and SGA 7 locators are UNVERIFIED (no network): BLR §1.2 Prop. 4 and its base reading,
   BLR §7.2 Thm. 1 / §1.2 Prop. 2, and SGA 7 IX Prop. 3.3.
2. **The `IsSHUnram ≅ O^sh` identification.** sh-route §3 argues it on paper; it is not formalized. It matters
   only for judging that the two `…SH` leaves are printed forms. Every Lean implication above is unconditional.
3. **Integration.** `OpenResearchLeaves12SH`, `researchLeaves11_of_open12SH` and `sixContactMin_of_open15SH`
   are ready to fold in after the announcement. They need sh-route's `Top`/`CA1–3`/`Final` and this task's
   parts as kernel files.
