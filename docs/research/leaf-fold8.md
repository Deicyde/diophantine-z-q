# leaf-fold8: height, H-87/H-88, six Contrib proofs and TYZ T-11 folded into the single proof; 66 fields, strict GLUE 27 (was 31 of 69)

Task leaf-fold8, 2026-11-14. Base e9240be8 (wip/w58: fork main a6abd709 (w57) with leaf-fold7 inside OneProof,
qm-glue and height-glue). Nothing was merged. New Lean:
- `ZInQKernel/OneProof/H/TailY.lean`, `TailZ.lean`, `TailZ2.lean`, `TailZ3.lean`, `TailZ4.lean`;
- `ZInQKernel/OneProof/TYZSplit.lean`;
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold8/` (results log `log.md`, build notes
`BUILD.md`). No existing OneProof module was edited, and neither was any other file under `ZInQKernel/`,
`blueprint/`, or another task's files. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator below is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves8) (t : HDec.HSyn.OpenTextbookLeaves8) (l : HDec.HSyn.OpenAddedLeaves8)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

The H half goes through the new top of the H assembly:

```lean
theorem HDec.HSyn.sixContactMin_of_open8 (r : OpenResearchLeaves8) (t : OpenTextbookLeaves8)
    (l : OpenAddedLeaves8) (g : OpenGlue7) : ZInQ.SixContactMin
```

(`OneProof/H/TailZ4.lean`). The TYZ half uses tyz-split's derivation
`ZInQ.Contrib.TYZGenus.TYZSplit.tyzThm33Pinned_of_tyzThm33 : TYZThm33 → ∀ ℓ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ`
(`OneProof/TYZSplit.lean`).

The following are **VERIFIED**:
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **No existing constant changed.** op-compact's `DumpCompact` (copy in `scratch/leaf-fold8/`) with
  `cmp_hashes.py` compares 9953 OneProof constants before and 10831 after:
  - no constant was removed;
  - the only constant whose type or value hash changed is `ZInQ.OneProof.frozenTarget`, the intended statement
    change;
  - all 878 new constants are in `TailY`–`TailZ4` and `TYZSplit` (`cmp_hashes_out.txt`).
- `Check8.lean` compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open8`. The closure of
  `sixContactMin_of_open8` has 193 116 constants and no `sorryAx`. The six Contrib proofs and
  `tyzThm33Pinned_of_tyzThm33` have standard axioms (`check8_result.txt`).

**Counts.** The forms are the ones leaf-fold7 used, i.e. frontier r3's: *published form*, *consequence of one
theorem* (c), *composite* (comp) and *project glue* (pg).
- The strict count calls only the published forms LEAF; the lenient count also calls consequences LEAF.
- A field keeps the form leaf-fold7 gave it. A new field takes the form its source report gives, except that
  the source's own review overrides it (`faltingsLemma5BC`, §2).
- The table is printed by `mk_fields8.py` (`counts8.md`).

| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| leaf-fold7 (`sixContactMin_of_open7`) | 69 | 38 | 18 | 12 | 1 | 38 / 31 | 56 / 13 |
| + height-split, height-glue (six height rows) | 71 | 41 | 18 | 11 | 1 | 41 / 30 | 59 / 12 |
| + qm-glue (H-87, H-88) | 72 | 44 | 17 | 10 | 1 | 44 / 28 | 61 / 11 |
| + six cloud-worker Contrib proofs | **66** | **39** | **16** | **10** | **1** | **39 / 27** | **55 / 11** |

**Bundles.**
- `OpenResearchLeaves8`: 31 fields (29 in leaf-fold7).
- `OpenTextbookLeaves8`: 20 fields (23).
- `OpenAddedLeaves8`: 14 fields (16).
- The glue bundle is leaf-fold7's `OpenGlue7`, unchanged: one field, `QuotientP1Coordinate`.

**TYZ side.** The hypothesis `h33` used to be tyz-35's pinned form of TYZ Theorem 3.3, for every `ℓ`. That was the
frontier's GLUE row T-11, a composite. It is now `TYZSplit.TYZThm33`: TYZ Theorem 3.3 in its printed form
(Period7.tex L1299–1311), restricted to `n ≡ 5, 7 (mod 8)` with `𝒫(d)` kept existential. tyz-split counts this as
published form (specialization): the TYZ side goes from 1 GLUE to 1 LEAF among `h11, h29, hS, h33`. `hS` (T-5) is
unchanged, as the task asked.

**Module layout.**
- **Kernel-only modules.** `TailY` and `TailZ` import only kernel modules (`TailZ` imports `TailY`). They hold
  height-glue's `Rows.lean` verbatim, cut in two at a namespace boundary. They could move to
  `ZInQKernel/Contrib/` unchanged.
- **Modules over the chain.** `TailZ2` imports `TailO`; `TailZ3` imports `TailZ2`. They hold qm-glue's
  `HauptGlue.lean` minus its first 2197 lines. Those lines are leafq-check's `Fold.lean`, which is already in
  `TailO` (leaf-fold6 part f10), checked line by line.
- **The bundles.** `TailZ4` imports `TailX`, `TailZ`, `TailZ3` and the six Contrib modules.
- **TYZ.** `OneProof/TYZSplit.lean` imports only `ZInQKernel.Contrib.TYZChain.Main`.
- **Main** imports `TailZ4` and `TYZSplit`. The chain from LPrefix to TailX is untouched.

### 1.1 What changed

Each item below is a field replacement made by compiled theorems. "→" reads "is replaced by".

**height-split and height-glue** (`TailY`, `TailZ` = `scratch/height-glue/Rows.lean` lines 10-3506; `TailZ4`):
- `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` → height-split's eight leaves over the published stable height
  `IsStableFaltingsHeight`:
  - `semistableReductionThm` (SS1), `semistableNeronBaseChange` (SS2), `semistablePersists` (SS3);
  - `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`, `pazukiCor13Upper`, `gaudronRemondThm14`.
- The derivation is `ZInQ.HeightGlue.heightRows_of_t35` (height-glue): height-split's `heightRows_of` with its
  glue bundle `HeightGlue` proved from T35. It gets two more inputs, both from existing textbook fields:
  - N1 (`ZInQ.H5Neron.NeronModelExists`) is the kernel's `ZInQ.Contrib.NeronC.neronModelExists_of_extension`
    applied to `neronSchemeExtensionExists`;
  - T35 is av-split's `AvSplit.Final.h38` applied to `uniformizationLeafAll` and `mumfordTorsionAlgClosed`.

  So **no new glue enters**. The four glue Props of height-split are proved:
  - `AnalyticUniformizationExists` and `AnalyticUniformizationUnique`;
  - `UniformizationDim`;
  - `MetrizationOfUniformization` (proved with no hypothesis).
- **Transports.**
  - `r19`, `r20`, `r21` and `h5fin` are kernel Props and are filled directly.
  - `r18` and `r22` are the chain's copies, stated over leaf-push2's copy `HDec.ZInQ.LeafPush2.stableFaltingsHeight`
    of the Arakelov layer. That copy is not definitionally the kernel's: `FinExt` and `MetrizedModel` are separate
    structures.
  - `r18_lf8` and `r22_lf8` rewrite with the chain's proved `G0HeightCopies.heightCopiesAgree` (g0-assemble), which
    compares the two infima field by field. `r18_lf8` also converts `IsCurve`/`IsJacobian` field by field, as
    `r18Concrete_of` does in the other direction.
- **Effect.** The vacuity caution of leaf-fold6/7 §2 (R19, R20, R22, `h5fin` stated over the project's infimum
  `stableFaltingsHeight`) no longer applies to any field. The kernel's infimum now appears only in theorems.

**qm-glue** (`TailZ2`, `TailZ3` = `scratch/qm-glue/HauptGlue.lean` lines 2198-end; `TailZ4`):
- `valenceFormulaGammaStar` (H-87, c) → `valenceFormulaCocompactEq` and `shimizuCovolumeO1`, via
  `LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves`.
- `qmHauptmodulBase3` (H-88, comp) → the same two and `igusaCMValue24`, together with Igusa's `ψ₄` and `χ₁₀`
  (existing research fields, through `QMSplit.Theta.thetaModularity_of`), via
  `LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves`.
- The glue `GammaStarFromO1` is proved by qm-glue: `QMglue.gammaStarFromO1_proof`, the index-4 covolume
  transfer.
- `ThetaQuotientValue24` (one number, `j_θ = −16/27` at discriminant `−24`) is replaced by Lin–Yang's published
  Igusa vector at that CM value. qm-glue proves the two equivalent (`thetaQuotientValue24_of_igusa` and its
  converse).

**Cloud-worker Contrib theorems** (`TailZ4`; each proves a field's Prop outright, so the field is **dropped**):

| field | proof | universe / head check |
|---|---|---|
| `t3Surj` (H-76) | `ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof.{0}` | field `…NeronMappingAbelianSchemeSurj.{0}`, proof universe-polymorphic, instantiated at 0 |
| `t11bExists` (H-75) | `ZInQ.Contrib.CloudW06PoincareRigidity.T11bExists_proof` | the field is the chain's `HDec.AVB2.T11bExists` (TailM); W06's `T11bExists` has the same text over the kernel's `PkgI3.AbVar`, accepted by unfolding (`t11bExists_lf8`) |
| `t24` (H-33) | `ZInQ.Contrib.CloudW08EigenformTwists.EigenformTwist_proof` | field is the kernel's `PkgI4.EigenformTwist` |
| `zariskiConnectedness` (H-67) | `ZariskiConn.ZariskiConnectedness_proof.{0}` | field `ZariskiConn.ZariskiConnectedness.{0}` |
| `egaIV_8_8_2_ii` (H-64) | `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof` | kernel Prop |
| `egaIV_17_7_8_ii` (H-66) | `ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof` | kernel Prop |

With `t11bExists` proved, T11(b) is proved: `t11b_of_exists5` turns `T11bExists_proof` into the kernel's
`ZInQ.LeafPush2.T11b_Rigidity`. So `qmCentralizerCMC` no longer needs a textbook leaf beside it to give the three
QM rows.

**tyz-split** (`TYZSplit` = `scratch/tyz-split/T11.lean` lines 2-end): `h33` → `TYZSplit.TYZThm33` (see above).

### 1.2 Which constants the fields are (VERIFIED, `Check8.lean`, `check8_result.txt`)

- 24 of the 66 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant
  (leaf-fold7: 33 of 69).
- The nine kernel fields that went:
  - proved by Contrib: `t3Surj`, `t24`, `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii`;
  - replaced by height-split's leaves: `r19`, `r20`, `r21`, `h5fin`.
- The new fields are declared in the new modules:
  - `ZInQ.HeightSplit.*` (TailY), a root namespace, kernel-only;
  - `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`, `…ShimizuCovolumeO1` (TailZ2);
  - `…Value24.IgusaCMValue24` (TailZ3).

  The height leaves could move under `ZInQKernel/Contrib/` unchanged.

## 2. Every hypothesis

"Strict kind": LEAF = published form; GLUE (c) = consequence of one theorem; GLUE (comp) = composite;
GLUE (pg) = project glue. The tables are generated from `scratch/leaf-fold8/fields8.tsv` (`mk_fields8.py`, which
starts from leaf-fold7's `fields7.tsv`). Lean types are written as in `TailZ4.lean`, inside `namespace HDec.HSyn`.

**Forms of the new fields (the readings behind the counts).**
- **SS1, SS2, SS3: consequences.** leaf-fold7 §5 already read SS1 and SS2 this way: the global form of SGA 7 IX 3.6
  and the open-subgroup form of IX 3.3. SS3 is IX 3.3 in global form (height-split §7 caveat).
- **`faltingsLemma5BC`: consequence.** height-split calls it an instance of the printed lemma. Its own statement
  review (height-split §8) says Lemma 5 is printed as an identity with a correction term, and that the inequality
  uses Raynaud's bound, so it is a consequence.
- **`javanpeykarBound`: published form (specialization)**, as height-split gives it. Specializations are counted
  this way throughout leaf-fold7. height-split §7 notes that a stricter reader may call it a consequence. Under
  that reading the height fold is neutral on the strict count (−5 + 5) and still lowers the lenient count by 1
  (`h5fin`).
- **`bostLowerBound`, `pazukiCor13Upper` (half), `gaudronRemondThm14`: published form**, with height-split's RISKs:
  Bost's display, and Pazuki's level-2 coordinates (both height-split §8).
- **`valenceFormulaCocompactEq`, `shimizuCovolumeO1`, `igusaCMValue24`: published form**, as qm-split and qm-glue
  give them. `igusaCMValue24` is equivalent to the old glue number.

### OpenResearchLeaves8 (31 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `r1r2` | `LeafAdopt.R1R2fpRep` | GLUE (comp) | composite | R1(a,c,d), R2, R5 on one Y3, X6: Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8; Baba-Granath 2008 Thm 2.1; Gonzalez-Rotger 2006 Prop. 5.6, Thm 5.12; Lemma QP | pin-apply |  |
| `shimuraFamily` | `QMSplit.Moduli.ShimuraFamily` | GLUE (c) | consequence of one theorem | Shimura 1967 Main Thm I (holomorphic family over the upper half plane) on one fine witness, composed with every algebraic pi : Y -> P1 (GAGA-level step, flagged by qm-split) | qm-split; folded by leaf-fold7 | r1b (project glue) |
| `r1rec` | `LeafQM.AV.R1rec` | GLUE (c) | consequence of one theorem | R1(d), Shimura 1967 Main Thm II; Deligne 1971 3.7-3.13, Thm 4.19 | leaf-adopt |  |
| `r3` | `_root_.ZInQ.LeafPush2.R03_LinYang` | GLUE (comp) | composite | Lin-Yang 2020 Ex. 29; Baba-Granath Thm 2.1; Weil 1957; Lemma P | leaf-push2 |  |
| `igusaPsi4` | `QMSplit.Theta.IgusaPsi4` | LEAF | published form | Igusa, Amer. J. Math. 84 (1962), 86 (1964), 89 (1967): psi4 = 2^-2 sum theta_m^8 is a Siegel modular form of weight 4 (flag: Igusa defines psi4 as an Eisenstein series and prints the theta expression as a theorem) | qm-split; folded by leaf-fold7 | r4 (with igusaChi10) |
| `igusaChi10` | `QMSplit.Theta.IgusaChi10` | LEAF | published form | Igusa 1962, 1967: chi10 = -2^-14 prod theta_m^2 is a Siegel cusp form of weight 10 | qm-split; folded by leaf-fold7 | r4 (with igusaPsi4) |
| `r5` | `LeafQM.AV.R5fp` | GLUE (c) | consequence of one theorem | Gonzalez-Rotger 2006 Thm 5.12 (audit: YES on X0(D,N)) | leaf-qm-fp |  |
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
| `r15` | `DeligneSerreConseq` | GLUE (comp) | composite | Deligne-Serre 1974 Thm 4.1, Lemma 3.2, with T25, T18, T19 | hdec-faithful |  |
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

### OpenTextbookLeaves8 (20 fields)

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
| `t33` | `_root_.LeafModCurves.JacobianExists ℚ` | LEAF | published form | Weil; Milne, Jacobian varieties Thm 1.1, Prop. 6.1 | leaf-modcurves |  |
| `dimJacobianEqGenus` | `_root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE (comp) | composite | Milne, Jacobian varieties Prop. 2.1 with Serre duality (not splittable, av-split 4.2) | curves-g |  |
| `genusX1Field` | `_root_.ZInQ.Contrib.CurvesG.GenusX1Field` | GLUE (comp) | composite | Shimura 1971 6.7, Prop. 6.9, Prop. 1.40 (not statable in published form, curve-split 3.5) | curves-g |  |
| `normalModelOfFunctionFieldQ` | `_root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | LEAF | published form | Stacks 0BXX; Hartshorne I.6.7-6.9 | curves-g |  |
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
- Every field not marked "folded by leaf-fold8" has leaf-fold7's type. The build checks this, since
  `sixContactMin_of_open8` passes those fields unchanged to `sixContactMin_of_open7`.
- The vacuity caution of leaf-fold7 §2 (R19, R20, R22, `h5fin` over `stableFaltingsHeight`) is gone: those fields
  are theorems now.
- The new height leaves are stated over height-split's definitions `IsSemistable` and `IsStableFaltingsHeight`.
  Their non-vacuity is machine-checked only at the zero abelian variety (height-split §7); the torus and abelian
  parts are not exercised. SPECULATIVE: these are faithful renderings of Faltings' definition (Faltings 1983 §1;
  Deligne, Sém. Bourbaki 616), and height-split's independent review found no defect.

**Flagged for a human check.** New in this fold:
- `pazukiCor13Upper`: if Pazuki's level-2 coordinates are `θ[a;0](0, 2Ω)` rather than the classical
  `θ[a;b](0, Ω)`, the leaf (and the kernel row `R22_Pazuki` itself) overstates the print by about `log 4`
  (height-split §8, RISK 1). Unchanged from the row it replaces.
- `bostLowerBound`: the display is unread. The leaf is in Deligne's normalization, the weaker reading.
- `faltingsLemma5BC`: the operative source is Raynaud, Astérisque 127 VII Cor. 2.1.3 (UNVERIFIED).
- `igusaCMValue24`: one number, read off Lin–Yang's eqs. (2), (14) at the Baba–Granath CM value. Equivalent to
  the old glue; the manuscript cites exactly this.
- `valenceFormulaCocompactEq`: stated with Mathlib's invariant measure on `ℍ` and a genuine fundamental-domain
  predicate. Shimura and Rankin state it for `vol(Γ\ℍ)`.

Still open from leaf-fold7: `ShimuraGoodReduction` (guard-free form), `R1R2fpRep`, `RaynaudCriterion` (the case
`m = 3`), and the composites of §3.

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields; `?` marks a field that is not in published form (c or comp). The grouping is a
reading of the docstrings, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** (Shimura 1967, 1971; Shimura–Taniyama; Shimizu; Deligne; Baba–Granath; González–Rotger; Yu; Kurihara; Elkies; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard) | 14 (9) | `r1r2`?, `shimuraFamily`?, `r1rec`?, `r3`?, `r5`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa; Shimura 1976; Mumford, Tata II; Lin–Yang's Igusa vector) | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** (Mumford; Milne; Birkenhake–Lange; Serre GAGA) | 9 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** (BLR; Serre–Tate; SGA 7 IX; Raynaud) | 9 (6) | `r6`?, `r7a`, `r7b`?, `r8`?, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableReductionThm`?, `semistableNeronBaseChange`?, `semistablePersists`? |
| **C′. Schemes and group schemes over a field** (EGA IV 8.10; Cartier; Stacks 04KV, 00TV; SGA 3 VI_A) | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** (Faltings; Bost; Javanpeykar; Pazuki; Gaudron–Rémond) | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** (Tate 1967; Ax–Sen–Tate; Fontaine; Faltings; Scholze; Pan; Berger) | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** (Deligne; Deligne–Serre; Diamond–Shurman; Kato; Carayol; Shimura) | 6 (4) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r15`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** (Weil; Milne JV; Stacks; Shimura 1971; Igusa 1959) | 5 (2) | `t33`, `dimJacobianEqGenus`?, `genusX1Field`?, `normalModelOfFunctionFieldQ`, `igusaGL2` |
| total | **65 (26)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold7 §3:
- **Group D** went from 5 of 8 not in published form to 1 of 7. Faltings' Lemma 5 is the one left.
- **Group C′** lost three EGA rows, which are proved now. **Group B** lost T11(b), also proved.
- **Group C** gained SGA 7 IX's three semistable-reduction statements, as consequences in global form.
- **Group A** lost the valence and Hauptmodul composites. In their place it has the valence formula and Shimizu's
  covolume, both in published form.
- Most of what remains is in groups A and C: the moduli of the Shimura curve, and Néron/monodromy.

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base build.** On the base, `lake build +ZInQKernel.OneProof.Main` took 19 min. It rebuilt the kernel modules
  and the whole chain LPrefix…TailX, which were out of date in this worktree.
- **Hashes before.** `DumpCompact` gave 9953 OneProof constants (`hashes_before.txt`) and the `frozenTarget` type
  (`frozenTarget_before.txt`).
- **New modules.** Each was built with `lake build ZInQKernel.OneProof.H.X`, one at a time:
  - TailY 14 s, TailZ 13 s, TailZ2 14 s, TailZ3 14 s, all at the first try;
  - the six Contrib modules 11 s–3 min 38 s;
  - TailZ4 9 s, after one fix (`r18_lf8`/`r22_lf8`, §1.1);
  - TYZSplit 31 s.

  `verbatim_check8.py` (`verbatim_check8_out.txt`) checks every copied slice: it appears unchanged, as one block,
  after the module's header, with only the `#print` lines dropped. It also checks that lines 37-2197 of
  `HauptGlue.lean` occur in `TailO.lean` in order. They form three contiguous blocks, matching Fold.lean's
  1-934/1326-2563 cut.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** `DumpCompact` gives 10831 constants. `cmp_hashes.py` reports 0 removed and 1 changed
  (`frozenTarget`). The 878 new constants are all in TailY–TailZ4 and TYZSplit.
- **Check8.lean** checks:
  - the kernel conclusion;
  - the closure: 193 116 constants, no `sorryAx`;
  - the head constant and declaring module of all 66 fields;
  - the axioms of the six Contrib proofs and of `tyzThm33Pinned_of_tyzThm33`.
- **Module sizes.** TailY 115 KB, TailZ 81 KB, TailZ2 80 KB, TailZ3 65 KB, TailZ4 15 KB, TYZSplit 29 KB. Each is
  under 150 KB.

**No statement of a leaf, row or glue Prop was changed.** Every field that was not folded keeps its type. Every
folded field is filled by a compiled theorem whose conclusion is the old field's constant, either directly or
through `r18_lf8`, `r22_lf8`, `t11bExists_lf8`. No HDec copy was deleted, so no FaithCheck was needed.

## 5. Not folded, and why

Decision rule (leaf-fold7 §5). A fold is taken only if neither the strict nor the lenient GLUE count rises, and if
it does one of the following:
- lowers the strict GLUE count;
- replaces a consequence or composite by published-form leaves.

- **H-3 `r5count` (height-glue `r5fpCount_of_t11b`).** The route is `R5fpCount` from
  `EichlerOptimalEmbeddingCount` (published), `T11b_Rigidity` (proved now, §1.1), `CMDescent` and
  `QMUniformizationC`. It does not qualify:
  - `QMUniformizationC`'s own docstring calls it "not one printed statement". It bundles Shimura's moduli
    statements for principally polarized surfaces, the algebraicity of QM tori, GAGA for homomorphisms, and the
    passage to the unpolarized `𝒪^×` form, so it is a composite.
  - `CMDescent` bundles Albert's classification with Shimura–Taniyama, so it is at best a consequence.
  - The fold would therefore replace one consequence by a published leaf, a consequence and a composite: strict
    GLUE +1, lenient GLUE +1.

  The proof compiles in height-glue's `QMFull.lean` and could be folded as soon as `QMUniformizationC` is split
  (height-glue §5 lists the pieces: T35, `T11a_RiemannEnd`, class number one, Riemann's algebraicity of QM tori,
  linear algebra of `M₂(ℝ)`).
- **qm-glue H-1 `r1r2`, H-43 `x6ConicModel` (`r1r2fpRep_of_canonical`, `x6ConicModel_of_canonical'`).**
  - In: the existential leaves `CanonicalModelY3` (a "qualified consequence", Lemma QP), `CanonicalCoarseX6`,
    `BabaGranathX6`, `GonzalezRotgerX6`, `ConicCanonical`.
  - Also in: the per-witness glue `ReciprocityOfFine` and the project glue `CoarseFactor`.
  - Out: one composite and one consequence.
  - The strict GLUE count would rise (−2 + 3), so this was not taken. Proving `ReciprocityOfFine` from an
    existential form through qm-split's `compare_iso`, and `CoarseFactor` (descent along a finite map, qm-glue
    §4.3), would make it pay.
- **qm-glue (c) H-44 `thetaRatiosAlgebraic`.** qm-glue found no further Lean reduction (it needs a polarization
  object in `PkgI3.AbVar`).
- **qm-split's final head (ead4b7dc).** Its `Haupt.lean` derives H-87/H-88 from the same leaves by an index
  argument (`…_of_O1`) instead of the proof of `GammaStarFromO1`. qm-glue's `HauptGlue.lean` was used, because it
  is the compiled file that also contains the `IgusaCMValue24` reduction. Both give the same three leaves.
- **TYZ T-5 `hS`.** Left as it is, as the task asked. tyz-split splits it into two GLUE Props, so no gain.
- **Duplicated definitions.**
  - `TailY` and `TailZ` contain height-glue's verbatim root-namespace copies of metrization2's kernel
    (`G0Dim`, `ZInQ.Metrization`, `ZInQ.Metrization2`) and of unif-dims' `JacDetDescends` chain. These are not in
    `ZInQKernel/HDecomp` or `Contrib`; the chain's copies are inside `HDec`, so nothing clashes.
  - `TailZ3` keeps qm-glue's copies of `Valence.lean`'s statements (`HDec.LeafQCheck.QMSplitVB`), which no other
    module has.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves7`, `t : OpenTextbookLeaves7`, `l : OpenAddedLeaves7`.
- Added: `r : OpenResearchLeaves8`, `t : OpenTextbookLeaves8`, `l : OpenAddedLeaves8`.
- `g : OpenGlue7` is unchanged.

**TYZ.**
- Removed: `h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ`.
- Added: `h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33`.
- `h11`, `h29`, `hS`, `hL2`, `hL3` are unchanged.

**Fields removed (14):**
- research: `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin`;
- textbook: `t3Surj`, `t11bExists`, `t24`;
- added: `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii`, `valenceFormulaGammaStar`,
  `qmHauptmodulBase3`.

**Fields added (11):**
- research: `semistableReductionThm`, `semistableNeronBaseChange`, `semistablePersists`, `bostLowerBound`,
  `javanpeykarBound`, `faltingsLemma5BC`, `pazukiCor13Upper`, `gaudronRemondThm14`;
- added: `valenceFormulaCocompactEq`, `shimizuCovolumeO1`, `igusaCMValue24`.

Six removed fields are proved outright, with no replacement: `t3Surj`, `t11bExists`, `t24`,
`zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_17_7_8_ii` (cloud workers W03, W06, W08, W02, W01).
