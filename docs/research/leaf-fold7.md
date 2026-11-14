# leaf-fold7: seven split tasks folded into the single proof; 69 fields, 38 in published form (was 15 of 68)

Task leaf-fold7, 2026-11-14. Base debc37b4 (wip/w56: fork main f70ec251 with wip/one-proof (leaf-fold6 inside
OneProof), curve-split, hodge-split, qm-split). Nothing was merged. New Lean: `ZInQKernel/OneProof/H/TailP.lean` …
`TailX.lean` (nine modules, each under 150 KB) and the switch of `ZInQKernel/OneProof/Main.lean`. Checks and tools:
`scratch/leaf-fold7/` (results log `log.md`). No existing OneProof module, no other file under `ZInQKernel/`,
`blueprint/`, or another task's files was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator below is the source report's, UNVERIFIED unless the audit `locators.md` read it.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves7) (t : HDec.HSyn.OpenTextbookLeaves7) (l : HDec.HSyn.OpenAddedLeaves7)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → TYZ35.TYZThm33Pinned ℓ)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

through the new top of the H assembly

```lean
theorem HDec.HSyn.sixContactMin_of_open7 (r : OpenResearchLeaves7) (t : OpenTextbookLeaves7)
    (l : OpenAddedLeaves7) (g : OpenGlue7) : ZInQ.SixContactMin
```

(`OneProof/H/TailX.lean`). The following are **VERIFIED**:
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- No existing constant changed: op-compact's `DumpCompact` (copy in `scratch/leaf-fold7/`) with `cmp_hashes.py`
  compares 8594 OneProof constants before and 9953 after. No constant was removed. The only constant whose type or
  value hash changed is `ZInQ.OneProof.frozenTarget`, and that is the intended statement change. All 1359 new
  constants are in `TailP`–`TailX` (`cmp_hashes_out.txt`).
- `Check7.lean` compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open7`. The closure
  of `sixContactMin_of_open7` has 186 483 constants and no `sorryAx`.

**Counts.** The forms are frontier r3's: *published form*, *consequence of one theorem* (c), *composite* (comp) and
*project glue* (pg). The strict count calls only the published forms LEAF. The lenient count also calls
consequences LEAF. A field keeps the form frontier r3 gives its row; new fields take the form their source report
gives.

| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| leaf-fold6 (`sixContactMin_of_open6`) | 68 | 15 | 29 | 22 | 2 | 15 / 53 | 44 / 24 |
| + av-glue (T8) | 71 | 19 | 29 | 21 | 2 | 19 / 52 | 48 / 23 |
| + av-split (T4, T5, T35, `homLatticeCorr`, `isogenyQuasiInverse`) | 71 | 24 | 25 | 20 | 2 | 24 / 47 | 49 / 22 |
| + curve-split (H-85 proved, H-81, H-82, H-41, H-83 guard) | 69 | 26 | 24 | 17 | 2 | 26 / 43 | 50 / 19 |
| + qm-split (H-46 proved, H-35, H-42/61/63, H-86, H-2, H-20) | 67 | 31 | 20 | 15 | 1 | 31 / 36 | 51 / 16 |
| + hodge-split (H-8, H-22, H-32, H-51, H-52, H-10) | 69 | 38 | 18 | 12 | 1 | 38 / 31 | 56 / 13 |
| + mcr-glue (`ModelCoordinateResidue` → `QuotientP1Coordinate`) | **69** | **38** | **18** | **12** | **1** | **38 / 31** | **56 / 13** |

Bundles: `OpenResearchLeaves7` has 29 fields (26 in leaf-fold6), `OpenTextbookLeaves7` 23 (21),
`OpenAddedLeaves7` 16 (20) and `OpenGlue7` 1 (1). The **glue bundle** keeps one field, and the field is now
smaller: `QuotientP1Coordinate`. The research field `r1b` was project glue (frontier H-20) and is now a consequence
of one theorem. So the project-glue rows drop from 2 to 1.

For comparison only: leaf-fold6's report used older forms (§2.0 there), under which its 68 fields counted
51 LEAF / 16 LEAF? / 1 GLUE. The numbers above apply frontier r3's forms to both bundles, so the before and after
columns are comparable.

### 1.1 What changed

Each item below is a field replacement made by compiled theorems. "→" reads "is replaced by".

**av-glue** (`TailP` = `scratch/av-glue/Combined.lean`):
- `t8 : PkgI3.PoincareReducibility` (comp) → `poincareComplement`, `cartierSmooth`, `geomConnOfRationalPoint`,
  `groupSchemeEquidim` (all published form), via `AVGlue.poincareReducibility_of_published'`.
- That theorem also needs the quasi-inverse of an isogeny. av-split supplies it (next item), passed to av-glue's
  verbatim copy `AVGlue.WeilPairing.IsogenyQuasiInverse` by unfolding.
- The glue Prop `SimpleImageIsogeny`, which leaf-fold5 had and leaf-fold6 avoided by keeping T8 whole, is now
  proved.

**av-split** (`TailQ` = `scratch/av-split/AvSplitAll.lean`; its verbatim copy of mul-rigidity is replaced by an
import of the kernel module `Contrib/FrobChain/Rigidity.lean`, which has the same text):
- `t4` (c) → `mulEtaleAbelianScheme`.
- `t5` (c) → `mumfordTorsionAlgClosed`.
- `t35` (c) → `uniformizationLeafAll` (kernel AN3 leaf) with `mumfordTorsionAlgClosed`.
- `homLatticeCorr` (comp) → `uniformizationLeafAll` with `gagaMorphism`.
- `isogenyQuasiInverse` (c) → `milneIsogenyQuasiInverse`.

The proofs are `AvSplit.Final.h24`, `h25`, `h38`, `h69`, `h54`. `h54` concludes av-split's root copy of
`WeilPairing.IsogenyQuasiInverse`, which the chain's copy accepts by unfolding.

**curve-split** (`TailR` = `CurveBij.lean` + `CurvesGSplit.lean` + `X0Split.lean`; the guard clause of H-83 is in
`TailW`):
- `curveBijIso` (comp) is **dropped**: `CurveSplit.curveBijIso` proves it with no hypothesis.
- `normalCurveSmoothQ` (comp) → `regularSmoothPerfect` (Stacks 00TV).
- `geomConnectedOfConstantFieldQ` (comp) is **dropped**: it follows from the existing field
  `zariskiConnectedness`.
- `x0Transitive` (c) → `igusaGL2`, the kernel's statement of Igusa's theorem as printed.
- `shimuraGoodReduction` (comp) → `shimuraGoodReductionNoGuard`, the same statement without the `ℚ̄`-point guard
  of `IsShimuraModel`. It is a strictly smaller statement; the guard follows from `r1r2`.
  `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` is curve-split's text, stated inside `namespace HDec` over the
  chain's own `VertWitness` definitions, not over curve-split's root copies.

**qm-split** (`TailU` = six of qm-split's files, compiled over the OneProof chain in place of leaf-fold4's olean
chain, with no change):
- `qmClassNumberOne` (c) is **dropped**: `QMSplit.CNO.qmClassNumberOne_proof`, a norm-Euclidean computation.
- `t27` (c) → `yuThm11`, Yu's Thm 1.1 with its splitting clause.
- `cmOptimalEmbedding` (c), `qmAutCard` (comp), `alFixedPoints` (comp) → `qmCentralizerCMC`, via
  `QMSplit.Aut.rows_of_C` with T11(b) from the field `t11bExists`.
- `stQM` (c) → `shimuraTaniyamaQbar`.
- `r4` (c) → `igusaPsi4`, `igusaChi10`.
- `r1b` (pg) → `shimuraFamily` (c), via `QMSplit.Moduli.r1b_of'`. qm-split's `compare_iso` proves the transport
  between fine witnesses.

**hodge-split** (`TailS`, `TailT` = `HodgeSplit.lean` cut in two at §16; transports in `TailV`):
- `r10` (comp) → `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, together with the next two leaves.
- `senTwist` (c) and `finiteImageHT` (comp) → `tateTwistInvariants`, `axSenTate`.
- `r14` (comp) → `dsThm965`, `dsThm966`.
- `t23` (c) → `bdRInvariants`.
- `r13` (c) → `eigenformHTNew` (c), the newform case: a strictly smaller statement of the same form. T25, which
  the reduction also uses, is the kernel's proved `T25.newformOfEigenform_leaf`.

hodge-split states its rows over the kernel's pkg-I4 layer `ZInQ.Contrib.G9.PkgI4`; the chain states them over its
own copies. `TailV` transports them:
- **Galois representations.** The chain's `PkgI4.GaloisRep` and `GaloisChar` are converted field by field to G9's.
  `FiniteImageHT`, `SenTwist`, `R14Det`, `T23_FontaineClosure` and `EigenformHT` are then accepted by unfolding.
- **R10.** Unfolding times out: it was stopped after 4 M heartbeats. The two `galRep`s act on Tate modules whose
  `Module ℤ_[p]` instances are defined separately, and unifying them is too slow. `HodgeLF7.r10` instead uses two
  compiled lemmas:
  - `IsDeRhamOver` and `htMultOver` are invariant under an isomorphism of representations (`isDeRhamOver_congr`,
    `htMultOver_congr`).
  - The identity `vEquiv : (toG9AbVar A).V p ≃ₗ A.V p` intertwines the two `galRep`s; on a pure tensor the step
    closes by unfolding `galT`.

**mcr-glue** (`TailW` = `MCRGlue{1,2,3}.lean.part` inside `namespace HDec`): the glue `modelCoordinateResidue` →
`quotientP1Coordinate`, via `MCRGlue.modelCoordinateResidue_of_quotient'`. The residue half is proved. The
remaining glue asks only for the finite coordinate map to `P¹_{ℤ_(p)}`.

### 1.2 Which constants the fields are (VERIFIED, `Check7.lean`, `check7_result.txt`)

- 33 of the 69 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant.
  leaf-fold6 had 32 of 68.
- The new kernel field is `igusaGL2` (`Contrib/RLeaf/IgusaSL2.lean`). The kernel fields `t4`, `t5`, `t8`, `t35`,
  `homLatticeCorr`, `t27`, `normalCurveSmoothQ`, `geomConnectedOfConstantFieldQ` and `x0Transitive` were replaced
  (§1.1). `poincareComplement` (`Contrib/AVB1/Poincare.lean`) and `uniformizationLeafAll`
  (`HDecomp/Analytic/Uniformization.lean`) are kernel Props that become fields.
- The other new fields are declared in the new modules:
  - `AVGlue.*` (TailP);
  - `AvSplit.*` and `ZInQ.HomLattice.GAGAMorphism` (TailQ);
  - `CurveSplit.RegularSmoothPerfect` (TailR);
  - `ZInQ.Contrib.HodgeSplit.*` (TailS);
  - `HDec.QMSplit.*` and `…QMSplitSTQM.ShimuraTaniyamaQbar` (TailU);
  - `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` and `HDec.MCRGlue.QuotientP1Coordinate` (TailW).

  A later PR could move them under `ZInQKernel/Contrib/`.

## 2. Every hypothesis

The forms are frontier r3's for the rows it lists; each new field takes the form its source report gives. "Strict
kind": LEAF = published form. GLUE (c) is a consequence of one theorem; GLUE (comp) a composite; GLUE (pg) project
glue. The table is generated from `scratch/leaf-fold7/fields7.tsv`. Lean types are written as in `TailX.lean`,
inside `namespace HDec.HSyn`.

### OpenResearchLeaves7 (29 fields)

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
| `r18` | `ZInQ.LeafPush2.R18_Javanpeykar` | GLUE (c) | consequence of one theorem | Javanpeykar 2014 Thm 1.1.1 (read), with H5 | leaf-push2 |  |
| `r19` | `ZInQ.DefFaltings.R19_GaudronRemond` | LEAF | published form | Gaudron-Remond 2014 Thm 1.4 (read) | def-faltings |  |
| `r20` | `ZInQ.DefFaltings.R20_FaltingsLemma5` | GLUE (c) | consequence of one theorem | Faltings 1983 Lemma 5 | def-faltings |  |
| `r21` | `ZInQ.DefFaltings.R21_Bost` | GLUE (c) | consequence of one theorem | Bost 1996, through Gaudron-Remond 9 (read) | def-faltings |  |
| `r22` | `ZInQ.LeafPush2.R22_Pazuki` | GLUE (c) | consequence of one theorem | Pazuki 2012 Cor. 1.3(2) (read) | leaf-push2 |  |
| `h5fin` | `ZInQ.DefFaltings.StableHeightFinite` | GLUE (comp) | composite | Faltings 1983 1; Deligne, Bourbaki 616; plus correctness of the definition | h5-glue |  |

### OpenTextbookLeaves7 (23 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `t3Surj` | `_root_.ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{0}` | LEAF | published form | BLR 1.2 Prop. 8, surjective half | neron-c |  |
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
| `t11bExists` | `AVB2.T11bExists` | LEAF | published form (half) | Conrad 2006 3; Milne 1986 20 | av-b2 |  |
| `bdRInvariants` | `∀ p, _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p` | LEAF | published form | B_dR^{G_Q_p} = Q_p: Fontaine, Asterisque 223 (1994) Exp. II; Brinon-Conrad, CMI notes 4 | hodge-split; folded by leaf-fold7 | t23 (consequence) |
| `t24` | `_root_.PkgI4.EigenformTwist` | GLUE (c) | consequence of one theorem | Shimura 1971 Prop. 3.64; Atkin-Li 1978 | hdec-faithful |  |
| `yuThm11` | `QMSplit.Yu.YuThm11` | LEAF | published form | Chia-Fu Yu, J. Pure Appl. Algebra 217 (2013) Thm 1.1 (with its splitting clause; case labels dropped) | qm-split; folded by leaf-fold7 | t27 (consequence) |
| `t33` | `_root_.LeafModCurves.JacobianExists ℚ` | LEAF | published form | Weil; Milne, Jacobian varieties Thm 1.1, Prop. 6.1 | leaf-modcurves |  |
| `dimJacobianEqGenus` | `_root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE (comp) | composite | Milne, Jacobian varieties Prop. 2.1 with Serre duality (not splittable, av-split 4.2) | curves-g |  |
| `genusX1Field` | `_root_.ZInQ.Contrib.CurvesG.GenusX1Field` | GLUE (comp) | composite | Shimura 1971 6.7, Prop. 6.9, Prop. 1.40 (not statable in published form, curve-split 3.5) | curves-g |  |
| `normalModelOfFunctionFieldQ` | `_root_.ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | LEAF | published form | Stacks 0BXX; Hartshorne I.6.7-6.9 | curves-g |  |
| `regularSmoothPerfect` | `_root_.CurveSplit.RegularSmoothPerfect` | LEAF | published form (half) | Stacks 00TV (S_q regular implies S smooth at q over a perfect field) | curve-split; folded by leaf-fold7 | normalCurveSmoothQ (composite) |
| `igusaGL2` | `_root_.ZInQ.RLeaf.IgusaGL2` | LEAF | published form | Igusa's theorem: the Galois image on E_j[N] over Q(j) is GL_2(Z/N) (Igusa, Amer. J. Math. 81 (1959); Lang, Elliptic functions Ch. 6 3) | t40-igusa (kernel leaf); folded by leaf-fold7 (curve-split) | x0Transitive (consequence) |
| `neronSchemeExtensionExists` | `_root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | LEAF | published form (weakened) | BLR 1.4 Thm 3 | neron-c |  |

### OpenAddedLeaves7 (16 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `thetaRatiosAlgebraic` | `G0Split.ThetaPt.ThetaRatiosAlgebraic` | GLUE (comp) | composite | Shimura 1976; Mumford Tata II IIIa 8; Igusa (qm-split: ThetaNullNonvanishing + glue, not folded) | g0-thetapoint |  |
| `qmHauptmodulBase3` | `LeafQCheck.HM.QMHauptmodulBase3` | GLUE (comp) | composite | Lin-Yang 2020 Ex. 29; Igusa; Hashimoto 1995; Elkies 1998 (qm-split: valence formula + Shimizu + glue, not folded) | leafq-check |  |
| `qmCentralizerCMC` | `QMSplit.Aut.QMCentralizerCMC` | LEAF | published form | End_O(A) of a QM surface over C is Z or an optimally embedded order Phi^-1(O) of an imaginary quadratic k: Shimura 1967 1-3; Jordan 1981 3; Gonzalez-Rotger 2006 5 | qm-split; folded by leaf-fold7 | cmOptimalEmbedding (consequence), qmAutCard (composite), alFixedPoints (composite) |
| `tateTwistInvariants` | `_root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | LEAF | published form | C_p(i)^{G_K} = 0 for i != 0, K finite over Q_p in Qbar_p: Tate, p-divisible groups (1967) 3.3 Thm 2 | hodge-split; folded by leaf-fold7 | senTwist (consequence), finiteImageHT (composite), with axSenTate; also used for r10 |
| `axSenTate` | `_root_.ZInQ.Contrib.HodgeSplit.AxSenTate` | LEAF | published form | C_p^{G_K} = K: Tate 1967 3.3 Thm 1; Sen 1969; Ax 1970 | hodge-split; folded by leaf-fold7 | senTwist, finiteImageHT, r10 |
| `t09SymmIsogenyExists` | `WeilPairing.T09_SymmIsogenyExists` | GLUE (c) | consequence of one theorem | Mumford 6, 8, 20, 23 (not splittable, av-split 4.1) | weil-pairing |  |
| `milneIsogenyQuasiInverse` | `_root_.AvSplit.MilneIsogenyQuasiInverse` | LEAF | published form (weakened) | fg = [d], gf = [d] as morphisms: Milne 1986 Rem. 8.4; Milne's notes Prop. 7.1; Mumford 7 | av-split; folded by leaf-fold7 | isogenyQuasiInverse (consequence) |
| `x6ConicModel` | `X6Kummer.X6ConicModel` | GLUE (c) | consequence of one theorem | Kurihara 1979; Elkies 1998 3 | x6-kummer |  |
| `y3Connected` | `TSHecke.Y3Connected` | GLUE (comp) | composite | Deligne, PSPM 33 2.1, 2.6.3, with an orbit computation | ts-hecke |  |
| `zariskiConnectedness` | `_root_.ZariskiConn.ZariskiConnectedness.{0}` | LEAF | published form | EGA III_1 4.3.1, 4.3.4 | zariski-conn | (also gives geomConnectedOfConstantFieldQ, curve-split) |
| `shimuraTaniyamaQbar` | `G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | LEAF | published form (specialization) | Shimura-Taniyama 1961 12.4 Prop. 26; Milne, CM notes 7 (model over Qbar) | qm-split; folded by leaf-fold7 | stQM (consequence) |
| `valenceFormulaGammaStar` | `LeafQCheck.VB.ValenceFormulaGammaStar` | GLUE (c) | consequence of one theorem | valence formula (Shimura 1971 Prop. 2.16, Thm 2.20) with the signature of Gamma* (not folded: qm-split's split adds project glue) | leafq-check |  |
| `egaIV_8_8_2_ii` | `_root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` | LEAF | published form | EGA IV_3 8.8.2 (ii) | spread-out |  |
| `egaIV_8_10_5_xii` | `_root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | LEAF | published form | EGA IV_3 8.10.5 (xii) | spread-out |  |
| `egaIV_17_7_8_ii` | `_root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` | LEAF | published form | EGA IV_4 17.7.8 (ii) | spread-out |  |
| `shimuraGoodReductionNoGuard` | `CurveSplitGR.ShimuraGoodReductionNoGuard` | GLUE (comp) | composite | vert-witness's ShimuraGoodReduction without the Qbar-point guard (redundant given r1r2): Kottwitz 1992 5; Buzzard 1997; Morita 1981; Carayol 1986 (not statable in published form today, curve-split 3.6) | curve-split; folded by leaf-fold7 | shimuraGoodReduction (a strictly smaller statement of the same form) |

### OpenGlue7 (1 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `quotientP1Coordinate` | `MCRGlue.QuotientP1Coordinate` | GLUE (pg) | project glue | a finite q : Y -> Z over Z_(p) and Z = P^1_{Z_(p)} by charts with R2fp's fibre relation for the composite: the tame quotient Y/Gamma' = P^1 (SGA 1 Exp. V); no quotient schemes or P^1_{Z_(p)} in Mathlib 4.35 | mcr-glue; folded by leaf-fold7 | modelCoordinateResidue (the residue clause proved) |

Notes on the table. The vacuity caution of leaf-fold6 §2.1 still applies to R19, R20, R22 and `h5fin`: they are
stated over `stableFaltingsHeight`. Every field not marked "folded by leaf-fold7" has leaf-fold6's type; the build
checks this, since `sixContactMin_of_open7` passes those fields unchanged to `sixContactMin_of_open6`.

**Flagged for a human check.** New in this fold:
- `igusaPsi4`, `igusaChi10`: Igusa defines `ψ₄` as an Eisenstein series and prints the theta expression as a
  theorem (qm-split).
- `shimuraFamily`: the reading "for every `π`" needs a GAGA-level composition step (qm-split). Lemma QP enters as
  for `r1r2`.
- `shimuraTaniyamaQbar`: the model is stated over `ℚ̄`, as in Milne's form; Shimura–Taniyama print a number field
  (qm-split).
- `yuThm11`: the simple/non-simple labels are dropped, which makes it weaker.
- `deRhamH1AbVarT`: `H¹_ét` is written as `Hom(V_p A, ℚ_p)`. `hodgeTateDecompAbVar` chooses bases.
  `dsThm965` extends coefficients along `ι_L ∘ ι_C⁻¹` (hodge-split §3).
- `uniformizationLeafAll`, `gagaMorphism`: these are "coordinate forms" of Mumford §1 and of GAGA (bp-analytic §4,
  homlattice §3). That they count as leaves is SPECULATIVE.
- `geomConnOfRationalPoint`, `groupSchemeEquidim`: specializations of Stacks 04KV and of SGA 3 VI_A 2.4, with
  locators UNVERIFIED.

Still open from leaf-fold6: `ShimuraGoodReduction` (level 3 at `3 ∣ D`, now in its guard-free form),
`ValenceFormulaGammaStar`, `R1R2fpRep`, `RaynaudCriterion` (the case `m = 3`).

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields; `?` marks a field that is not in published form (c or comp). The grouping is a
reading of the docstrings, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves and QM abelian surfaces** (Shimura 1967, 1971; Shimura–Taniyama; Deligne; Baba–Granath; González–Rotger; Yu; Kurihara; Elkies; Takeuchi; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard) | 14 (11) | `r1r2`?, `shimuraFamily`?, `r1rec`?, `r3`?, `r5`?, `r5count`?, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `y3Connected`?, `valenceFormulaGammaStar`?, `qmHauptmodulBase3`?, `shimuraGoodReductionNoGuard`? |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa; Shimura 1976; Mumford, Tata II) | 3 (1) | `igusaPsi4`, `igusaChi10`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** (Mumford; Milne; Birkenhake–Lange; Conrad; Serre GAGA) | 10 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t11bExists`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate; SGA 7; Raynaud) | 7 (3) | `r6`?, `r7a`, `r7b`?, `r8`?, `t3Surj`, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme` |
| **C′. Schemes and group schemes over a field** (EGA III₁ 4.3; EGA IV 8.8, 8.10, 17.7; Cartier; Stacks 04KV, 00TV; SGA 3 VI_A) | 8 (0) | `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_8_10_5_xii`, `egaIV_17_7_8_ii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 8 (5) | `r9a`, `r9b`, `r18`?, `r19`, `r20`?, `r21`?, `r22`?, `h5fin`? |
| **E. p-adic Hodge theory** (Tate 1967; Ax–Sen–Tate; Fontaine; Faltings; Scholze; Pan; Berger) | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** (Deligne; Deligne–Serre; Diamond–Shurman; Kato; Carayol; Shimura; Atkin–Li) | 7 (5) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r15`?, `r16`?, `r17`?, `t24`? |
| **G. Algebraic and modular curves** (Weil; Milne JV; Stacks; Shimura 1971; Igusa 1959) | 5 (2) | `t33`, `dimJacobianEqGenus`?, `genusX1Field`?, `normalModelOfFunctionFieldQ`, `igusaGL2` |
| total | **68 (30)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold6 §3:
- Group B gained the published Mumford and Milne statements and lost every consequence row except `t10` and `t09`.
- Groups C′ and E are now entirely in published form, apart from Pan–Berger.
- In group G only `dimJacobianEqGenus` and `genusX1Field` are composites; `curveBijIso` was proved and
  `normalCurveSmoothQ` replaced.
- Group A holds most of what remains: the moduli of the Shimura curve. It needs abelian schemes over a base or a
  coarse comparison (curve-split §3.6, qm-split §3).

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base build.** On the base, `lake build +ZInQKernel.OneProof.Main` rebuilt the chain LPrefix…TailO, about 15
  min, because some kernel modules it imports were out of date in this worktree.
- **Hashes before.** `DumpCompact` gave 8594 OneProof constants (`hashes_before.txt`) and the frozenTarget type
  (`frozenTarget_before.txt`).
- **New modules.** `lake build ZInQKernel.OneProof.H.TailP`, then Q, R, T (with S), U, W, V and X, compiled one at a
  time; each took 8–71 s. All the split tasks' files compiled unchanged in the new environment. The exceptions are
  the documented edits, checked by `verbatim_check7.py` (`verbatim_check7_out.txt`):
  - the mul-rigidity copy in TailQ, 166 lines, replaced by the kernel import of the same text;
  - the GENERATED banner line of av-glue's `Combined.lean`;
  - the imports of TailR, merged into one header.

  Apart from those, every source line appears unchanged and in order. The only added lines are banners,
  `section`/`end` wrappers, the reopened header of TailT, and the reopened namespace of TailW.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** `DumpCompact` gives 9953 constants. `cmp_hashes.py`: 0 removed, 1 changed (`frozenTarget`),
  1359 new, all in TailP–TailX.
- **Check7.lean.** The kernel conclusion, the closure (186 483 constants, no `sorryAx`), and the head constant and
  declaring module of all 69 fields (`check7_result.txt`).
- **Module sizes.** TailP 63 KB, TailQ 125 KB, TailR 85 KB, TailS 110 KB, TailT 103 KB, TailU 114 KB, TailV 8 KB,
  TailW 48 KB, TailX 18 KB. Each is under 150 KB.

**No statement of a leaf, row or glue Prop was changed.** Every field that was not folded keeps its type. Every
folded field is filled by a compiled theorem whose conclusion is the old field's constant, either directly or after
the transports of §1.1.

## 5. Not folded, and why

Decision rule. A fold is taken only if neither the strict GLUE count nor the lenient GLUE count rises, and if it
does one of the following: lowers the strict GLUE count; replaces a consequence or composite by published-form
leaves; or replaces a GLUE field by a strictly smaller statement of the same form, with no new field. The third
case covers `quotientP1Coordinate`, `eigenformHTNew` and `shimuraGoodReductionNoGuard`.

- **height-split, all rows** (H-14 `r18`, H-15 `r19`, H-16 `r20`, H-17 `r21`, H-18 `r22`, H-19 `h5fin`, H-3
  `r5count`).
  - Every route goes through the identification `IsStableFaltingsHeight ↔ stableFaltingsHeight`, which needs SS1
    and SS2. height-split itself calls these consequence-level forms: the global form of SGA 7 IX 3.6 and the
    open-subgroup form of IX 3.3.
  - Example: `r22` (c) would become `PazukiCor13Upper` (published) plus SS1 (c) and SS2 (c). N1 follows from the
    existing `neronSchemeExtensionExists`. The strict GLUE count rises.
  - Folding `r20` and `r22` together leaves the strict GLUE count at 2: SS1 and SS2 replace them, and the field
    count rises by 4.
  - `r18`, `r21` and `h5fin` also need the four glue Props of `HeightGlue`. `r19` is already in published form.
  - `r5count` would need the glue `QMPairEmbeddingCorrespondence` beside the Eichler leaf.
- **mcr-glue's full split.** It is six leaves (L1–L6, three of them composites) plus the glue A, B, C1, C2, so the
  glue goes from 1 to 4. Only the step to `QuotientP1Coordinate` was taken.
- **qm-split, not taken:**
  - H-44 `thetaRatiosAlgebraic`: replaced by a published leaf plus a smaller composite. One more field, no GLUE
    count lowered.
  - H-87 `valenceFormulaGammaStar` and H-88 `qmHauptmodulBase3`: need the project glue `GammaStarFromO1` and the
    number `ThetaQuotientValue24`, so the lenient GLUE count rises.
  - H-1 `r1r2`, H-43 `x6ConicModel`, H-59 `y3Connected`: the per-witness glue props would replace one composite
    by a leaf plus glue.
- **curve-split, H-79 `genusX1Field`.** Only `dim J₁(N) ≤ N²` is used, but that use lives in existing modules: E2
  in `TailD` and `javanpeykarJ1` in `LPrefix` consume `OpenTextbookLeaves4.t34 : DimJ1Genus`, an equality. A bound
  cannot fill that field, so the fold would mean restating the chain above E2. Besides, curve-split's replacement
  `RiemannHurwitzQj` is itself a composite, so the count is neutral.
- **curve-split, H-83:** cannot be stated in published form today; only its guard clause was dropped.
- **av-split H-53 `t09SymmIsogenyExists` and H-78 `dimJacobianEqGenus`:** not splittable over Mathlib (no dual
  abelian variety, no `H¹(X, 𝒪_X)`).
- **hodge-split H-9 `r11r12`:** Pan's and Berger's theorems need `B_st`, which Mathlib does not have.
- **Duplicated definitions that remain.** The new fields are declared in OneProof modules. The av-split, av-glue
  and curve-split pieces are kernel-only, so a PR could move them to `ZInQKernel/Contrib/` unchanged. The copies
  `AVGlue.WeilPairing.IsogenyQuasiInverse`, root `WeilPairing.IsogenyQuasiInverse`, root `ModelGlue.CurveBijIso`
  and hodge-split's G9 rows are verbatim copies of chain rows; `TailX` and `TailV` identify each with the chain's
  row, by unfolding or by the transports. No FaithCheck was needed, since no HDec copy was deleted.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.** Removed: `r : OpenResearchLeaves5`, `t : OpenTextbookLeaves6`, `l : OpenAddedLeaves6`,
`g : OpenGlue6`. Added: `r : OpenResearchLeaves7`, `t : OpenTextbookLeaves7`, `l : OpenAddedLeaves7`,
`g : OpenGlue7`. The six TYZ and GZ hypotheses are unchanged.

**Fields removed (26):**
- research: `r1b`, `r4`, `r10`, `r13`, `r14`;
- textbook: `t4`, `t5`, `t8`, `homLatticeCorr`, `t23`, `t27`, `t35`, `normalCurveSmoothQ`,
  `geomConnectedOfConstantFieldQ`, `x0Transitive`;
- added: `cmOptimalEmbedding`, `qmClassNumberOne`, `senTwist`, `finiteImageHT`, `isogenyQuasiInverse`,
  `qmAutCard`, `alFixedPoints`, `stQM`, `shimuraGoodReduction`, `curveBijIso`;
- glue: `modelCoordinateResidue`.

**Fields added (27):**
- research: `shimuraFamily`, `igusaPsi4`, `igusaChi10`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`,
  `eigenformHTNew`, `dsThm965`, `dsThm966`;
- textbook: `mulEtaleAbelianScheme`, `mumfordTorsionAlgClosed`, `poincareComplement`, `cartierSmooth`,
  `geomConnOfRationalPoint`, `groupSchemeEquidim`, `uniformizationLeafAll`, `gagaMorphism`, `bdRInvariants`,
  `yuThm11`, `regularSmoothPerfect`, `igusaGL2`;
- added: `qmCentralizerCMC`, `tateTwistInvariants`, `axSenTate`, `milneIsogenyQuasiInverse`,
  `shimuraTaniyamaQbar`, `shimuraGoodReductionNoGuard`;
- glue: `quotientP1Coordinate`.

Three removed fields are proved outright, with no replacement: `curveBijIso`, `qmClassNumberOne`,
`geomConnectedOfConstantFieldQ`. The last follows from the existing field `zariskiConnectedness`.
