# leaf-fold9: `r1rec` and `r5` proved from `r1r2`, cloud PR #11 and modular-split's `r15` folded into the single proof; 61 fields, strict GLUE 24 (was 27 of 66)

Task leaf-fold9, 2026-11-14. Base 5da857b0 (wip/w59: fork main e9240be8 (w58) with leaf-fold8 inside OneProof,
mcr-quot, coarse-factor and cloud PR #11). Merged: `origin/wip/modular-split` (fold (4)). New Lean:
- `ZInQKernel/OneProof/H/TailZ5.lean` (the proofs) and `TailZ6.lean` (modular-split's `R15.lean` and the bundles);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold9/`; the results log is `log.md`. No
existing OneProof module was edited. No other file under `ZInQKernel/`, `blueprint/`, or another task's files was
edited either. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.

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

The H half goes through the new top of the H assembly (`OneProof/H/TailZ6.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9)
    (l : OpenAddedLeaves8) (g : OpenGlue7) : ZInQ.SixContactMin
```

Three folds were taken, and five fields went. No field was added.

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

The following are **VERIFIED** (`scratch/leaf-fold9/log.md`):
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **No existing constant changed.** op-compact's `DumpCompact` with `cmp_hashes.py` (copies in `scratch/leaf-fold9/`)
  compares 10831 OneProof constants before and 10917 after (`cmp_hashes_out.txt`):
  - the before-file is identical to leaf-fold8's after-file;
  - no constant was removed;
  - the only changed constant is `ZInQ.OneProof.frozenTarget`, the intended statement change;
  - all 86 new constants are in `TailZ5` and `TailZ6`.
- `Check9.lean` (`check9_result.txt`):
  - it compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open9`;
  - the closure has 212 153 constants and no `sorryAx`;
  - there are 61 fields: 28 + 18 + 14 + 1;
  - the two CloudW07 proofs, the bridge theorems and `deligneSerreConseq_of_ds` have standard axioms.
- `TailZ5` is 14 KB and `TailZ6` is 15 KB.
- `verbatim_check9.py` (`verbatim_check9_out.txt`) checks two things:
  - `TailZ6` contains `R15.lean` after its imports as one block, with only `#print` dropped;
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
| (4) modular-split (`r15` from `dsThm966`) | **61** | **37** | **14** | **9** | **1** | **37 / 24** | **51 / 10** |
| (4) reduct-split, shimura-split | see §5, §7 | | | | | | |

**Bundles.**
- `OpenResearchLeaves9`: 28 fields (31 in leaf-fold8).
- `OpenTextbookLeaves9`: 18 fields (20).
- `OpenAddedLeaves8` (14) and `OpenGlue7` (1, `QuotientP1Coordinate`) are leaf-fold8's, unchanged.

**TYZ side.** Unchanged: `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3`.

**Module layout.**
- `TailZ6` imports `TailZ5` and holds modular-split's `R15.lean` verbatim (after its two import lines, `TailT` and
  `LPrefix`, both below `TailZ5`), then the bundles.
- `TailZ5` imports `TailZ4`, the kernel's `Contrib/FrobChain/Rigidity`, the two CloudW07 modules
  (`JacobianExists`, `NormalModel`) and two Mathlib files (`FieldTheory.Galois.Infinite`,
  `NumberTheory.NumberField.Discriminant.Different`).
- `TailZ5` and `TailZ6` are generated by `scratch/leaf-fold9/mk_tailz5.py`:
  - from the lemma part `Lemmas.lean.part`, which is `test/R1recT.lean` minus its imports, compiled alone first;
  - and from `TailZ4.lean`'s field blocks, copied as text, so every kept field keeps its text and docstring.
- `Main` imports `TailZ6` in place of `TailZ4`. The chain from LPrefix to TailZ4 is untouched.
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

### 1.2 Which constants the fields are (VERIFIED, `Check9.lean`, `check9_result.txt`)

- 20 of the 61 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant
  (leaf-fold8: 24 of 66).
- Four of the five that went are kernel constants: `LeafQM.AV.R1rec`, `LeafQM.AV.R5fp`,
  `LeafModCurves.JacobianExists`, `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ`. The fifth,
  `HDec.HSyn.DeligneSerreConseq`, is a chain constant (LPrefix).

## 2. Every hypothesis

"Strict kind": LEAF = published form; GLUE (c) = consequence of one theorem; GLUE (comp) = composite;
GLUE (pg) = project glue. The tables are generated from `scratch/leaf-fold9/fields9.tsv` by `mk_fields9.py`, which
starts from leaf-fold8's `fields8.tsv` and only removes rows. Lean types are written as in `TailZ4.lean`, inside
`namespace HDec.HSyn`.

Every field keeps leaf-fold8's type and form. The build checks the types, since `sixContactMin_of_open9` passes the
kept fields unchanged to `sixContactMin_of_open8`. The readings and the flags of leaf-fold8 §2 apply unchanged:
`pazukiCor13Upper` (Pazuki's level-2 coordinates), `bostLowerBound` (display unread), `faltingsLemma5BC` (operative
source Raynaud), `igusaCMValue24`, `valenceFormulaCocompactEq`.

### OpenResearchLeaves9 (28 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `r1r2` | `LeafAdopt.R1R2fpRep` | GLUE (comp) | composite | R1(a,c,d), R2, R5 on one Y3, X6: Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8; Baba-Granath 2008 Thm 2.1; Gonzalez-Rotger 2006 Prop. 5.6, Thm 5.12; Lemma QP | pin-apply |  |
| `shimuraFamily` | `QMSplit.Moduli.ShimuraFamily` | GLUE (c) | consequence of one theorem | Shimura 1967 Main Thm I (holomorphic family over the upper half plane) on one fine witness, composed with every algebraic pi : Y -> P1 (GAGA-level step, flagged by qm-split) | qm-split; folded by leaf-fold7 | r1b (project glue) |
| `r3` | `_root_.ZInQ.LeafPush2.R03_LinYang` | GLUE (comp) | composite | Lin-Yang 2020 Ex. 29; Baba-Granath Thm 2.1; Weil 1957; Lemma P | leaf-push2 |  |
| `igusaPsi4` | `QMSplit.Theta.IgusaPsi4` | LEAF | published form | Igusa, Amer. J. Math. 84 (1962), 86 (1964), 89 (1967): psi4 = 2^-2 sum theta_m^8 is a Siegel modular form of weight 4 (flag: Igusa defines psi4 as an Eisenstein series and prints the theta expression as a theorem) | qm-split; folded by leaf-fold7 | r4 (with igusaChi10) |
| `igusaChi10` | `QMSplit.Theta.IgusaChi10` | LEAF | published form | Igusa 1962, 1967: chi10 = -2^-14 prod theta_m^2 is a Siegel cusp form of weight 10 | qm-split; folded by leaf-fold7 | r4 (with igusaPsi4) |
| `r5count` | `LeafQM.AV.R5fpCount` | GLUE (c) | consequence of one theorem | Gonzalez-Rotger 2006 Prop. 5.6 (count 2^b(R) h(R)) | leaf-qm-fp |  |
| `r6` | `_root_.PkgI2.RaynaudCriterion.{0}` | GLUE (c) | consequence of one theorem | SGA 7 IX Prop. 4.7 (Silverberg-Zarhin Thm 3.5) | pkg-I2 |  |
| `r7a` | `_root_.PkgI2.NeronOggShafarevich.{0}` | LEAF | published form | Serre-Tate 1968 Thm 1 | pkg-I2 |  |
| `r7b` | `_root_.PkgI2.SerreTatePotentialGood.{0}` | GLUE (c) | consequence of one theorem | Serre-Tate 1968 Thm 2 / Cor. 2 | pkg-I2 |  |
| `r8` | `_root_.PkgI2.GrothendieckMonodromy.{0}` | GLUE (c) | consequence of one theorem | SGA 7 IX 3.6 | pkg-I2 |  |
| `r9a` | `_root_.PkgI3.FaltingsSemisimple` | LEAF | published form | Faltings 1983 Satz 3 | pkg-I3 |  |
| `r9b` | `_root_.PkgI3.FaltingsTate` | LEAF | published form | Faltings 1983 Satz 4, Kor. 1 | pkg-I3 |  |
| `hodgeTateDecompAbVar` | `_root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | LEAF | published form (specialization) | C_p (x) V_p(A) = C_p(1)^g + C_p^g, G_F-equivariant (Fontaine, Invent. Math. 65 (1982); Tate 1967 4; Faltings 1988), bases of the two g-dimensional spaces chosen | hodge-split; folded by leaf-fold7 | r10 (composite), with deRhamH1AbVarT and Tate's two theorems |
| `deRhamH1AbVarT` | `_root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | LEAF | published form (transported) | H^1_et(A_Fbar, Q_p), written Hom(V_p A, Q_p), is de Rham with the printed D_dR (Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, wording read by h-leaves) | hodge-split; folded by leaf-fold7 | r10 |
| `r11r12` | `PkgI4.PanBerger` | GLUE (comp) | composite | Pan 2022 Thm 1.0.4 with Berger 2002 Thm 0.7 (not splittable: no B_st in Mathlib, hodge-split) | pkg-I4 |  |
| `eigenformHTNew` | `_root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew` | GLUE (c) | consequence of one theorem | Kato 2004 9.2-9.4 for newforms, transported to any semisimple attached rho and dualized (Kato's V_f not definable in Mathlib) | hodge-split; folded by leaf-fold7 | r13 (the same for all normalized eigenforms: a strictly smaller statement of the same form) |
| `dsThm965` | `_root_.ZInQ.Contrib.HodgeSplit.DSThm965` | LEAF | published form | Diamond-Shurman, GTM 228, Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14 for k = 2), coefficients extended along iota_L o iota_C^-1 | hodge-split; folded by leaf-fold7 | r14 (composite), with dsThm966 |
| `dsThm966` | `_root_.ZInQ.Contrib.HodgeSplit.DSThm966` | LEAF | published form | Deligne-Serre 1974 Thm 4.1; Diamond-Shurman Thm 9.6.6 (k = 1, continuous, finite image) | hodge-split; folded by leaf-fold7 | r14 |
| `r16` | `_root_.LeafModCurves.R16_EichlerShimuraJ1'` | GLUE (comp) | composite | Shimura 1973 Thm 1; Shimura 1971 Thm 7.9; Diamond-Shurman | leaf-modcurves |  |
| `r17` | `_root_.LadicCond.CarayolR17'` | GLUE (c) | consequence of one theorem | Carayol 1986 Theoreme (A) (read by the audit) | g0-mod-newform |  |
| `semistableReductionThm` | `_root_.ZInQ.HeightSplit.SemistableReductionThm` | GLUE (c) | consequence of one theorem | SGA 7 I Exp. IX Thm 3.6 (Grothendieck semistable reduction) in global form: good reduction outside finitely many primes and SGA 7 IX 3.3 (height-split §1) | height-split; folded by leaf-fold8 | r18-r22, h5fin (the eight together, with N1 from neronSchemeExtensionExists and T35 from h38) |
| `semistableNeronBaseChange` | `_root_.ZInQ.HeightSplit.SemistableNeronBaseChange` | GLUE (c) | consequence of one theorem | SGA 7 I Exp. IX Prop. 3.3 / Cor. 3.3.1, in the open-subgroup form of the kernel's N2 (identity component: SGA 3 VI_B 3.10) | height-split; folded by leaf-fold8 | r18-r22, h5fin (the eight together, with N1 from neronSchemeExtensionExists and T35 from h38) |
| `semistablePersists` | `_root_.ZInQ.HeightSplit.SemistablePersists` | GLUE (c) | consequence of one theorem | SGA 7 I Exp. IX 3.3 (semistability persists under finite extension), global form | height-split; folded by leaf-fold8 | r20 (with faltingsLemma5BC) |
| `bostLowerBound` | `_root_.ZInQ.HeightSplit.BostLowerBound` | LEAF | published form | Bost, Sem. Bourbaki 795 (Asterisque 237, 1996): h_D(A) >= -(g/2) log 2pi, Deligne normalization (display UNVERIFIED, height-split §2) | height-split; folded by leaf-fold8 | r21 |
| `javanpeykarBound` | `_root_.ZInQ.HeightSplit.JavanpeykarBound` | LEAF | published form (specialization) | Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 (read by the audit), for curves over K with a K-rational Belyi function, over the published stable height | height-split; folded by leaf-fold8 | r18 |
| `faltingsLemma5BC` | `_root_.ZInQ.HeightSplit.FaltingsLemma5BC` | GLUE (c) | consequence of one theorem | Faltings 1983 Lemma 5 in the semistable inequality form (Pazuki 2012 Rem. 2.3; Raynaud, Asterisque 127 VII Cor. 2.1.3 is the operative source, height-split §8), applied over every number field L above K | height-split; folded by leaf-fold8 | r20 |
| `pazukiCor13Upper` | `_root_.ZInQ.HeightSplit.PazukiCor13Upper` | LEAF | published form (half) | Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), upper half (read by the audit; RISK: Pazuki's level-2 coordinates, height-split §8) | height-split; folded by leaf-fold8 | r22 |
| `gaudronRemondThm14` | `_root_.ZInQ.HeightSplit.GaudronRemondThm14` | LEAF | published form | Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the audit), over the published stable height | height-split; folded by leaf-fold8 | r19 (same statement over the kernel infimum) |

### OpenTextbookLeaves9 (18 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `mulEtaleAbelianScheme` | `_root_.AvSplit.T4.MulEtaleAbelianScheme` | LEAF | published form | [m] on an abelian scheme over Spec O is etale when m is a unit in O: BLR 7.3 Lemma 2; Mumford GIT 6 | av-split; folded by leaf-fold7 | t4 (consequence) |
| `mumfordTorsionAlgClosed` | `_root_.AvSplit.MumfordTorsionAlgClosed` | LEAF | published form | A(k)[n] = (Z/n)^{2g} over k algebraically closed, char k not dividing n: Mumford, Abelian varieties 4, Application 2 (iv) | av-split; folded by leaf-fold7 | t5 (consequence); with uniformizationLeafAll, t35 |
| `homFreeFiniteAlgClosed` | `_root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | LEAF | published form | Mumford 19 Thm 3 | av-b1 |  |
| `charPolyIndepOfEllAlgClosed` | `_root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | LEAF | published form | Mumford 19 Thm 4 (specialization) | av-b1 |  |
| `poincareComplement` | `_root_.ZInQ.Contrib.AVB1.PoincareComplement` | LEAF | published form | Poincare's complete reducibility, complement form: Milne 1986 Prop. 12.1; Mumford 19 Thm 1 | av-b1; folded back by leaf-fold7 | t8 (composite), with the next three |
| `cartierSmooth` | `_root_.AVGlue.CartierSmooth` | LEAF | published form | Cartier 1962; Oort 1966; Mumford 11 Thm 1; Milne, Algebraic Groups Thm 3.23; Stacks 047N | av-glue; folded by leaf-fold7 | t8 |
| `geomConnOfRationalPoint` | `_root_.AVGlue.GeomConnOfRationalPoint` | LEAF | published form (specialization) | Stacks 04KV (Varieties 33.7.14), with finite type and a rational point added | av-glue; folded by leaf-fold7 | t8 |
| `groupSchemeEquidim` | `_root_.AVGlue.GroupSchemeEquidim` | LEAF | published form (specialization) | Stacks, groupoid schemes, properties of group schemes over a field; SGA 3 VI_A 2.4 (finite type) | av-glue; folded by leaf-fold7 | t8 |
| `t10` | `_root_.T10Etale.T10_TateDuality` | GLUE (c) | consequence of one theorem | Milne 1986 Thm 15.1 | t10-etale |  |
| `uniformizationLeafAll` | `_root_.BPAnalytic.Uniformization.UniformizationLeafAll` | LEAF | published form (coordinate form) | Mumford, Abelian varieties 1 (A^an = C^g/Lambda), in bp-analytic's coordinate form (kernel leaf AN3) | bp-analytic; folded by leaf-fold7 (av-split) | t35 (with mumfordTorsionAlgClosed), homLatticeCorr (with gagaMorphism) |
| `gagaMorphism` | `_root_.ZInQ.HomLattice.GAGAMorphism` | LEAF | published form (coordinate form) | Serre, GAGA (1956), for homomorphisms of complex abelian varieties (homlattice 3.2) | homlattice, av-split; folded by leaf-fold7 | homLatticeCorr (composite) |
| `bdRInvariants` | `∀ p, _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p` | LEAF | published form | B_dR^{G_Q_p} = Q_p: Fontaine, Asterisque 223 (1994) Exp. II; Brinon-Conrad, CMI notes 4 | hodge-split; folded by leaf-fold7 | t23 (consequence) |
| `yuThm11` | `QMSplit.Yu.YuThm11` | LEAF | published form | Chia-Fu Yu, J. Pure Appl. Algebra 217 (2013) Thm 1.1 (with its splitting clause; case labels dropped) | qm-split; folded by leaf-fold7 | t27 (consequence) |
| `dimJacobianEqGenus` | `_root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE (comp) | composite | Milne, Jacobian varieties Prop. 2.1 with Serre duality (not splittable, av-split 4.2) | curves-g |  |
| `genusX1Field` | `_root_.ZInQ.Contrib.CurvesG.GenusX1Field` | GLUE (comp) | composite | Shimura 1971 6.7, Prop. 6.9, Prop. 1.40 (not statable in published form, curve-split 3.5) | curves-g |  |
| `regularSmoothPerfect` | `_root_.CurveSplit.RegularSmoothPerfect` | LEAF | published form (half) | Stacks 00TV (S_q regular implies S smooth at q over a perfect field) | curve-split; folded by leaf-fold7 | normalCurveSmoothQ (composite) |
| `igusaGL2` | `_root_.ZInQ.RLeaf.IgusaGL2` | LEAF | published form | Igusa's theorem: the Galois image on E_j[N] over Q(j) is GL_2(Z/N) (Igusa, Amer. J. Math. 81 (1959); Lang, Elliptic functions Ch. 6 3) | t40-igusa (kernel leaf); folded by leaf-fold7 (curve-split) | x0Transitive (consequence) |
| `neronSchemeExtensionExists` | `_root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | LEAF | published form (weakened) | BLR 1.4 Thm 3 | neron-c |  |

### OpenAddedLeaves8 (14 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `thetaRatiosAlgebraic` | `G0Split.ThetaPt.ThetaRatiosAlgebraic` | GLUE (comp) | composite | Shimura 1976; Mumford Tata II IIIa 8; Igusa (qm-split: ThetaNullNonvanishing + glue, not folded) | g0-thetapoint |  |
| `qmCentralizerCMC` | `QMSplit.Aut.QMCentralizerCMC` | LEAF | published form | End_O(A) of a QM surface over C is Z or an optimally embedded order Phi^-1(O) of an imaginary quadratic k: Shimura 1967 1-3; Jordan 1981 3; Gonzalez-Rotger 2006 5 | qm-split; folded by leaf-fold7 | cmOptimalEmbedding (consequence), qmAutCard (composite), alFixedPoints (composite) |
| `tateTwistInvariants` | `_root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | LEAF | published form | C_p(i)^{G_K} = 0 for i != 0, K finite over Q_p in Qbar_p: Tate, p-divisible groups (1967) 3.3 Thm 2 | hodge-split; folded by leaf-fold7 | senTwist (consequence), finiteImageHT (composite), with axSenTate; also used for r10 |
| `axSenTate` | `_root_.ZInQ.Contrib.HodgeSplit.AxSenTate` | LEAF | published form | C_p^{G_K} = K: Tate 1967 3.3 Thm 1; Sen 1969; Ax 1970 | hodge-split; folded by leaf-fold7 | senTwist, finiteImageHT, r10 |
| `t09SymmIsogenyExists` | `WeilPairing.T09_SymmIsogenyExists` | GLUE (c) | consequence of one theorem | Mumford 6, 8, 20, 23 (not splittable, av-split 4.1) | weil-pairing |  |
| `milneIsogenyQuasiInverse` | `_root_.AvSplit.MilneIsogenyQuasiInverse` | LEAF | published form (weakened) | fg = [d], gf = [d] as morphisms: Milne 1986 Rem. 8.4; Milne's notes Prop. 7.1; Mumford 7 | av-split; folded by leaf-fold7 | isogenyQuasiInverse (consequence) |
| `x6ConicModel` | `X6Kummer.X6ConicModel` | GLUE (c) | consequence of one theorem | Kurihara 1979; Elkies 1998 3 | x6-kummer |  |
| `y3Connected` | `TSHecke.Y3Connected` | GLUE (comp) | composite | Deligne, PSPM 33 2.1, 2.6.3, with an orbit computation | ts-hecke |  |
| `shimuraTaniyamaQbar` | `G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | LEAF | published form (specialization) | Shimura-Taniyama 1961 12.4 Prop. 26; Milne, CM notes 7 (model over Qbar) | qm-split; folded by leaf-fold7 | stQM (consequence) |
| `egaIV_8_10_5_xii` | `_root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | LEAF | published form | EGA IV_3 8.10.5 (xii) | spread-out |  |
| `shimuraGoodReductionNoGuard` | `CurveSplitGR.ShimuraGoodReductionNoGuard` | GLUE (comp) | composite | vert-witness's ShimuraGoodReduction without the Qbar-point guard (redundant given r1r2): Kottwitz 1992 5; Buzzard 1997; Morita 1981; Carayol 1986 (not statable in published form today, curve-split 3.6) | curve-split; folded by leaf-fold7 | shimuraGoodReduction (a strictly smaller statement of the same form) |
| `valenceFormulaCocompactEq` | `LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | LEAF | published form | valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4), over Mathlib's invariant measure on the upper half plane and a genuine fundamental domain | qm-split, qm-glue; folded by leaf-fold8 | valenceFormulaGammaStar (consequence), qmHauptmodulBase3 (composite), with the next two |
| `shimizuCovolumeO1` | `LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | LEAF | published form | iota(O^1) is cocompact Fuchsian with covolume 2pi/3 (Shimura 1971 Prop. 9.2; Shimizu 1965; Voight Thm 39.1.13) | qm-split, qm-glue; folded by leaf-fold8 | valenceFormulaGammaStar, qmHauptmodulBase3 (GammaStarFromO1 proved by qm-glue) |
| `igusaCMValue24` | `LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` | LEAF | published form | Lin-Yang 2020 eqs. (2), (14) at the Baba-Granath CM value j = -16/27 (discriminant -24; Baba-Granath 2008 Thm 2.1, Elkies 1998), Lauter-Naehrig-Yang 2015 §2.2 conventions; the manuscript's citation (l.908-923); equivalent to the old glue ThetaQuotientValue24 | qm-glue; folded by leaf-fold8 | qmHauptmodulBase3 (with igusaPsi4, igusaChi10 and the previous two) |

### OpenGlue7 (1 field)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `quotientP1Coordinate` | `MCRGlue.QuotientP1Coordinate` | GLUE (pg) | project glue | a finite q : Y -> Z over Z_(p) and Z = P^1_{Z_(p)} by charts with R2fp's fibre relation for the composite: the tame quotient Y/Gamma' = P^1 (SGA 1 Exp. V); no quotient schemes or P^1_{Z_(p)} in Mathlib 4.35 | mcr-glue; folded by leaf-fold7 | modelCoordinateResidue (the residue clause proved) |

Notes on the table.
- `r1r2` is now the only carrier of R1(d) and R5 in the bundles. Its docstring already lists both (Deligne 1971
  Cor. 5.7; González–Rotger 2006 Thm 5.12), so its form, a composite, does not change.
- `r5count` (González–Rotger Prop. 5.6, a count of classes) does not follow from `r1r2`: no clause of the witness
  counts points.

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields. `?` marks a field that is not in published form (c or comp). The grouping is
leaf-fold8's, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** | 12 (7) | `r1r2`?, `shimuraFamily`?, `r3`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** | 9 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** | 9 (6) | `r6`?, `r7a`, `r7b`?, `r8`?, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableReductionThm`?, `semistableNeronBaseChange`?, `semistablePersists`? |
| **C′. Schemes and group schemes over a field** | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** | 5 (3) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** | 3 (2) | `dimJacobianEqGenus`?, `genusX1Field`?, `igusaGL2` |
| total | **60 (23)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold8 §3:
- **Group A** lost R1(d) and R5 in field-of-moduli form, as consequences: they are now theorems of `r1r2`.
- **Group F** lost `r15` (Deligne–Serre's consequences), now a theorem of Deligne–Serre's printed theorem
  (modular-split).
- **Group G** lost the Jacobian's existence and the normal model, both published and both proved by cloud worker
  W07.

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base.** `lake build +ZInQKernel.OneProof.Main` exits 0 on the base. The kernel and the chain were rebuilt in this
  worktree.
- **Hashes before.** `DumpCompact` gives 10831 constants (`hashes_before.txt`), identical to leaf-fold8's
  `hashes_after.txt`.
- **Lemmas.** `lake env lean scratch/leaf-fold9/test/R1recT.lean` compiles with no errors (about 5 s after imports).
  It took three rounds of fixes: a coercion to `Set`, `zpow` under a β-redex, and a `let` that `simp` does not
  unfold.
- **CloudW07.** `lake build ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists …NormalModel` exits 0, taking
  about 18 min.
- **modular-split.** Merged with `git merge origin/wip/modular-split` (clean, after its `.fleet` report). `TailZ6`
  (with `R15.lean`) and the new `Main` built at the first try.
- **TailZ5.** `lake build ZInQKernel.OneProof.H.TailZ5` succeeds, about 80 s, after one fix in `r5fp_of_rep`.
  - Rewriting `residueImage x = fieldOfModuliPair P` inside `R5ptProps`' conclusion gives a "motive is not type
    correct" error (an auxiliary proof term of `R5ptProps` depends on the field).
  - The fix transports the degree and the embedding along `IntermediateField.equivOfEq`.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** 10917 constants. `cmp_hashes.py` reports 0 removed and 1 changed (`frozenTarget`). The 86 new
  constants are all in `TailZ5` and `TailZ6`.
- **Check9.lean.** Conclusion; closure (212 153 constants, no `sorryAx`); head constant and module of all 61 fields;
  axioms of the CloudW07 proofs and the bridge theorems; the full types of `r1rec_of_rep` and `r5fp_of_rep`.
- **Module size.** TailZ5 is 14 KB and TailZ6 is 15 KB.

**No statement of a leaf, row or glue Prop was changed.**
- Every kept field keeps its type.
- Every removed field is filled by a compiled theorem whose type is exactly the old field's constant.
- No HDec copy was deleted, so no FaithCheck was needed.

## 5. Not folded, and why

Decision rule (leaf-fold7 §5, as the task states it). A fold is taken only if it does one of the following:
- lowers the strict GLUE count;
- replaces a composite or consequence by published-form leaves.

In either case, neither count may rise.

- **(1) mcr-quot (`modelCoordinateResidue_final9`, `heckeVertWitness_of_mcrQuot`). Not taken.**
  - Replacing the project glue `QuotientP1Coordinate` (1 strict GLUE) by mcr-quot's inputs would add:
    - L1 `ProperCurveAF` (composite), L3 `TameQuotientSmooth` (composite) and L6 `TameInertiaCyclic` (composite);
    - L5 `TameFixedPointsDisjoint` (consequence);
    - L2 `FiniteQuotientExists` (special case) and L4 `SmoothModelOfP1` (STANDARD);
    - the two new glue Props `P1SchemeQ` and `CMStabObj`;
    - and `CoverModelOfHeckeN`.

    T5 and `CurveBijIso` are theorems in the chain.
  - That is at least −1 + 6 on the strict count, and −1 + 5 on the lenient count.
  - Note for later (SPECULATIVE): the vendored CloudW07 library has the projective line `AlgebraicGeometry.projectiveLine`
    over a field, which is proper and integral with charts. It may close `P1SchemeQ`. Even then the six L-leaves
    keep the fold from paying.
- **(2) coarse-factor (`r1r2fpRep_of_canonical''`, `x6ConicModel_of_canonical''`). Not taken.**
  - H-43: qm-glue's `ConicCanonical` has the same statement as the field `x6ConicModel` (`X6Kummer.X6ConicModel`:
    `∃ Y Φ X Ψ fY π₆, R1R2fpFullProps … ∧ ConicModel X π₆`), and `x6ConicModel_of_canonical''` also takes `r1r2`.
    The replacement would be a renaming.
  - H-1: `r1r2` (comp) would become:
    - `CanonicalCoarseX6`, which is SGA 1's quotient together with Shimura–Deligne and Deligne's `π₀`, and carries
      the audit's "qualified consequence" caveat, so strict GLUE;
    - `BabaGranathX6` and `GonzalezRotgerX6`;
    - the glue `ReciprocityOfFine`.

    (`CanonicalModelY3` is implied by any of the three existential forms, since each contains `R1fpProps Y Φ`.)
    That is strict −1 + 2. It would be −1 + 1 if `ReciprocityOfFine` were proved from the field `r1rec`, which the
    bridge of §1.1 makes possible.
  - But the same bridge proves `r1rec` and `r5` from `r1r2` (−2 strict), and the two uses exclude each other.
  - So the fold that pays is the one taken: keep `r1r2`, drop `r1rec` and `r5`. `CoarseFactor` is proved
    (coarse-factor) but enters no field.
- **(4) modular-split, the parts not folded.**
  - `dimJacobianEqGenus` (comp) would become the project glue `H0DifferentialsEqHolo`. That is a real gain, since no
    literature is left, but neither count drops.
  - `r17` (c) would become `CarayolRealization` (c): neutral.
  - `eigenformHTNew` (c) would become `KatoRealizationCoh` (c) and the glue `HTDual`: strict +1.
- **(4) reduct-split, shimura-split:** see §7.
- **H-3 `r5count`, H-44 `thetaRatiosAlgebraic`, TYZ T-5 `hS`.** Unchanged from leaf-fold8 §5.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves8`, `t : OpenTextbookLeaves8`.
- Added: `r : OpenResearchLeaves9`, `t : OpenTextbookLeaves9`.
- `l : OpenAddedLeaves8` and `g : OpenGlue7` are unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (5), all proved, none replaced:**
- research `r1rec` (`LeafQM.AV.R1rec`) and `r5` (`LeafQM.AV.R5fp`): proved from the research field `r1r2`
  (`r1rec_of_rep`, `r5fp_of_rep`);
- textbook `t33` (`LeafModCurves.JacobianExists ℚ`) and `normalModelOfFunctionFieldQ`: proved by cloud worker W07
  (PR #11);
- research `r15` (`DeligneSerreConseq`): proved from the research field `dsThm966` (modular-split,
  `ModularSplit.deligneSerreConseq_of_ds`).

**Fields added:** none.

## 7. Fold (4): state of the three branches

| branch | `.fleet` report seen | folded |
|---|---|---|
| modular-split | yes (12:07) | `r15` (§1); the rest is not folded (§5) |
| reduct-split | not yet | — |
| shimura-split | not yet | — |
