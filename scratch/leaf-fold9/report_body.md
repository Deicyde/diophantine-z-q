
## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves9) (t : HDec.HSyn.OpenTextbookLeaves9) (l : HDec.HSyn.OpenAddedLeaves8)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

The H half goes through the new top of the H assembly (`OneProof/H/TailZ8.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9)
    (l : OpenAddedLeaves8) (g : OpenGlue7) : ZInQ.SixContactMin
```

Four folds were taken. Seven fields went, and four published-form leaves came in.

1. **`r1rec` and `r5` are theorems of `r1r2`. This is new Lean from this task.**
   - The research field `r1r2` (`LeafAdopt.R1R2fpRep`) provides one fine witness `Y₃` and one coarse witness
     `X₆`. They carry Shimura reciprocity and González–Rotger's Thm 5.12 as statements about the **residue fields
     of points**: the clauses `R1recProps` and `R5ptProps`.
   - The fields `r1rec` (`LeafQM.AV.R1rec`) and `r5` (`LeafQM.AV.R5fp`) state the same results for **fields of
     moduli** of objects and of pairs.
   - `TailZ5` proves the bridge on the witnesses. On `Y₃`, the field of moduli of an object lies in the residue
     field of its point. On `X₆`, the residue field of a point equals the field of moduli of its pair.
   - So `r1rec_of_rep : R1R2fpRep → R1rec` and `r5fp_of_rep : R1R2fpRep → R5fp` are compiled. Both fields are
     dropped.
2. **Cloud PR #11.**
   - `ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof` proves the textbook field `t33`
     (`LeafModCurves.JacobianExists ℚ`).
   - `NormalModelOfFunctionFieldQ_proof` proves `normalModelOfFunctionFieldQ`.
   - Both fields are dropped.
3. **modular-split (fold (4)).** `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`
   proves the research field `r15` (a composite) from the existing published-form field `dsThm966` (Deligne–Serre
   Thm 4.1). `r15` is dropped.
4. **reduct-split (fold (4)).** The research fields `r7b` and `r8`, both consequences, are replaced by four
   published-form leaves. No glue is involved: reduct-split proved its own glue. The leaves are:
   - `SerreTateThm2`, Serre–Tate 1968 Thm 2 as printed;
   - `SemistableReductionDVR`, SGA 7 IX 3.6 over a DVR;
   - `SemistableUnipotent`, SGA 7 IX 3.5;
   - `NeronSchemeModelExistsDVR`, BLR 1.4/3 over a DVR.

   `MumfordTorsionAlgClosed` is used too; it is already a textbook field.

The following are **VERIFIED** (`scratch/leaf-fold9/log.md`):
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **No existing constant changed.** op-compact's `DumpCompact` with `cmp_hashes.py` (copies in `scratch/leaf-fold9/`)
  compares 10831 OneProof constants before and 11119 after (`cmp_hashes_out.txt`):
  - the before-file is identical to leaf-fold8's after-file;
  - no constant was removed;
  - the only changed constant is `ZInQ.OneProof.frozenTarget`, the intended statement change;
  - all 288 new constants are in `TailZ5`–`TailZ8`.
- `Check9.lean` (`check9_result.txt`):
  - it compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open9`;
  - the closure has 212 238 constants and no `sorryAx`;
  - there are 63 fields: 30 + 18 + 14 + 1;
  - the two CloudW07 proofs, the bridge theorems, `deligneSerreConseq_of_ds`, `serreTatePotentialGood_final`
    and `grothendieckMonodromy_final'` have standard axioms.
- Sizes: `TailZ5` 14.6 KB, `TailZ6` 8.5 KB, `TailZ7` 92 KB, `TailZ8` 8.5 KB.
- `verbatim_check9.py` (`verbatim_check9_out.txt`) checks three things:
  - `TailZ6` contains `R15.lean` after its imports as one block, with only `#print` dropped;
  - `TailZ7` contains `Reduction.lean` the same way, with the same imports;
  - `TailZ5` contains the compiled lemma file minus its imports.

**Counts.** The forms are leaf-fold8's, i.e. frontier r3's. A removed field takes its form with it. The table is
printed by `mk_fields9.py` (`counts9.md`).

| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| leaf-fold8 (`sixContactMin_of_open8`) | 66 | 39 | 16 | 10 | 1 | 39 / 27 | 55 / 11 |
| (1) mcr-quot | not taken (§5) | | | | | | |
| (2) coarse-factor | not taken (§5) | | | | | | |
| r1r2-bridge (`r1rec`, `r5` from `r1r2`) | 64 | 39 | 14 | 10 | 1 | 39 / 25 | 53 / 11 |
| (3) cloud PR #11 (`t33`, `normalModelOfFunctionFieldQ`) | 62 | 37 | 14 | 10 | 1 | 37 / 25 | 51 / 11 |
| (4) modular-split (`r15` from `dsThm966`) | 61 | 37 | 14 | 9 | 1 | 37 / 24 | 51 / 10 |
| (4) reduct-split (`r7b`, `r8` from four published-form leaves) | **63** | **41** | **12** | **9** | **1** | **41 / 22** | **53 / 10** |
| (4) shimura-split | see §7 | | | | | | |

**Bundles.**
- `OpenResearchLeaves9`: 30 fields (31 in leaf-fold8).
- `OpenTextbookLeaves9`: 18 fields (20).
- `OpenAddedLeaves8` (14) and `OpenGlue7` (1, `QuotientP1Coordinate`) are leaf-fold8's, unchanged.

**TYZ side.** Unchanged: `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3`.

**Module layout.**
- `TailZ6` imports `TailZ5` and holds modular-split's `R15.lean` verbatim, after its two import lines (`TailT` and
  `LPrefix`, both below `TailZ5`).
- `TailZ7` is reduct-split's `Reduction.lean` verbatim, with its own imports: kernel modules, `TailQ` and `TailY`. It
  could move to `ZInQKernel/Contrib/` once the two chain imports are kernel modules.
- `TailZ8` imports `TailZ6` and `TailZ7` and holds the bundles.
- `TailZ5` imports `TailZ4`, the kernel's `Contrib/FrobChain/Rigidity`, the two CloudW07 modules
  (`JacobianExists`, `NormalModel`) and two Mathlib files (`FieldTheory.Galois.Infinite`,
  `NumberTheory.NumberField.Discriminant.Different`).
- `TailZ5`–`TailZ8` are generated by `scratch/leaf-fold9/mk_tailz5.py`:
  - from the lemma part `Lemmas.lean.part`, which is `test/R1recT.lean` minus its imports, compiled alone first;
  - and from `TailZ4.lean`'s field blocks, copied as text, so every kept field keeps its text and docstring.
- `Main` imports `TailZ8` in place of `TailZ4`. The chain from LPrefix to TailZ4 is untouched.
- The vendored CloudW07 library (711 files) now sits under `Main`'s import closure. On this host it took about
  18 min to build, one `lake build`.

### 1.1 What changed

**r1r2-bridge** (`TailZ5`, namespace `ZInQ.LeafFold9`, kernel constants only; then `HDec.HSyn`).

| theorem | statement | proof |
|---|---|---|
| `specMap_comp_eq_self_iff` | for a `ℚ̄`-point `y` of a scheme and `σ ∈ Aut(ℚ̄/ℚ)`: `Spec σ ≫ y = y` iff `σ` fixes `residueImage y` pointwise | Mathlib's `Scheme.SpecToEquivOfField` and the kernel's `specToEquivOfField_comp`; `adjoin` against `fixedField (zpowers σ)` |
| `fixedField_le_of_le` | `E.fixingSubgroup ≤ H → fixedField H ≤ E` for `E ≤ ℚ̄` | Mathlib's `InfiniteGalois.fixedField_fixingSubgroup` (`ℚ̄/ℚ` is Galois) |
| `unramifiedAbove5_mono` | `F ≤ E → UnramifiedAbove5 E → UnramifiedAbove5 F` | Mathlib's `NumberField.discr_dvd_discr` |
| `isBaseChangeOf_of_iso`, `isBaseChangeOfPair_of_iso` | a base change `IsBaseChangeOf f P Q` (or of pairs) transports along an isomorphism `Q' ≅ Q` | paste the pullback with an isomorphism square (`IsPullback.of_horiz_isIso`, `paste_horiz`); `MonObj.one_comp` for the identity section |
| `qmIso_of_isBaseChangeOfPair` | two base changes of one QM pair along one `f` are isomorphic as QM pairs | the comparison isomorphism of the two pullbacks (`IsPullback.isoIsPullback`) preserves the identity (pullback uniqueness) and so is a homomorphism by the kernel's rigidity `G0FibreSimple.rigidityHom`; it commutes with `ι` by pullback uniqueness |
| `fieldOfModuli3_le` | on a fine witness (`R1fpProps Y Φ`), `Φ y = [P] → fieldOfModuli3 P ≤ residueImage y` | `σ` fixing `ℚ(y)` fixes `y`; naturality of `Φ` gives a base change `Q` of `P` along `σ` with `[Q] = [P]`; transport (no rigidity needed) |
| `residueImage_eq_fieldOfModuliPair` | on a coarse witness (`X6Props`), `Ψ x = [P] → residueImage x = fieldOfModuliPair P` | `≥` as above, with the Galois equivariance of `Ψ`; `≤`: `σ` in the stabilizer of `P` gives two base changes, which are isomorphic (`qmIso_of_isBaseChangeOfPair`), so `σ` fixes `x` because `Ψ` is injective |
| `HDec.HSyn.r1rec_of_rep` | `LeafAdopt.R1R2fpRep → LeafQM.AV.R1rec` | `P` is the object at `y = Φ⁻¹[P]`; the witness's `R1recProps` gives `ℚ(y)` unramified above 5; `fieldOfModuli3_le` and `unramifiedAbove5_mono` |
| `HDec.HSyn.r5fp_of_rep` | `LeafAdopt.R1R2fpRep → LeafQM.AV.R5fp` | `P` is the pair at `x = Ψ⁻¹[P]`; `R5ptProps` at `x`, transported along `IntermediateField.equivOfEq` |

Notes on the bridge.
- `LeafQM`'s own docstrings said that "the bridge from `fieldOfModuliPair` to residue fields needs rigidity", and so
  the residue-field forms were carried in the bundle beside the field-of-moduli forms.
  - Rigidity is now a kernel theorem (`rigidityHom`, task mul-rigidity).
  - On `Y₃`, only the easy inclusion is needed, together with the discriminant of a subfield.
- **No statement changed.** `R1rec`, `R5fp` and `R1R2fpRep` are the kernel's and the chain's constants, unchanged.
- The proof of `R5fp` uses all of `X6Props`' Galois-equivariance clause and the bijectivity of `Ψ`.
  - It does not use `X6Surj`, `R1heckeProps` or `R1pi0Props`.
  - The proof of `R1rec` uses only the naturality clause of `R1fpProps`, the bijectivity of `Φ` and
    `R1recProps`.

**Cloud PR #11.**

| field | proof | check |
|---|---|---|
| `t33` (H-36) | `ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof` | kernel Prop `LeafModCurves.JacobianExists ℚ`, filled directly |
| `normalModelOfFunctionFieldQ` (H-80) | `ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof` | kernel Prop, filled directly |

**modular-split** (`TailZ6` = `scratch/modular-split/R15.lean` l. 3-end).
- `artinTransport_finite` is hodge-split's `artinTransport_proof`, keeping the finiteness of the image.
- `deligneSerreConseq_of_ds`: a semisimple `ρ` attached to a weight-one eigenform agrees at Frobenius, outside
  `Nℓ`, with the `ℓ`-adic realization of Deligne–Serre's representation. The two are conjugate by the kernel's
  `attachedConj_proof` (T18 Chebotarev with T19 Brauer–Nesbitt), so `ρ` has finite image.
- The field `r15 : DeligneSerreConseq` is `HDec.HSyn.DeligneSerreConseq` (LPrefix); the proof's type is exactly that
  constant.

**reduct-split** (`TailZ7` = `scratch/reduct-split/Reduction.lean`; reduct-split §§1-5).
- `ReductSplit.serreTatePotentialGood_final : SerreTateThm2 → AvSplit.MumfordTorsionAlgClosed →
  PkgI2.SerreTatePotentialGood.{0}` gives `r7b`. reduct-split proves `TorsionFieldOfDefinition` and the equivalence
  between a finite image of inertia and an open subgroup acting trivially.
- `ReductSplit.grothendieckMonodromy_final' : SemistableReductionDVR → SemistableUnipotent → NeronSchemeModelExistsDVR →
  AvSplit.MumfordTorsionAlgClosed → PkgI2.GrothendieckMonodromy.{0}` gives `r8`. reduct-split proves
  `dvrFiniteExtension`: a valuation ring of a finite extension over a DVR is a DVR.
- Readings, from reduct-split §5:
  - SGA 7 IX 3.6 asks only for `K'` finite; the print has finite separable, so the leaf is weaker.
  - SGA 7 IX 3.5 takes the weakest reading, one `σ` at a time.
  - BLR 1.4/3 is in scheme form.
  - **RISK:** if Serre–Tate Thm 2 is printed for complete (or henselian) `K`, the leaf over a general discrete
    valuation is a consequence. Locators are UNVERIFIED.

### 1.2 Which constants the fields are (VERIFIED, `Check9.lean`, `check9_result.txt`)

- 18 of the 63 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant
  (leaf-fold8: 24 of 66).
- Four of the five that went are kernel constants: `LeafQM.AV.R1rec`, `LeafQM.AV.R5fp`,
  `LeafModCurves.JacobianExists`, `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ`. The fifth,
  `HDec.HSyn.DeligneSerreConseq`, is a chain constant (LPrefix).
- `r7b` and `r8` (`PkgI2.*`) were kernel constants. The four new leaves `ReductSplit.*` are declared in `TailZ7`,
  which imports only kernel modules besides `TailQ` and `TailY`.
