# leaf-fold2: the results since leaf-fold, folded into one statement of what is still open

Task leaf-fold2, 2026-11-13. Base: 6f296292 (origin/wip/integrate-w42). Lean: `scratch/leaf-fold2/`.
The deliverable is `Leaves2.lean` (flat file). It is built by `assemble.sh` from:
- the scripts `mk_*.py`, `mk_b0*.sh` (order in `scratch/leaf-fold2/BUILD.md`);
- the copied parts `parts/`.

The results log is `scratch/leaf-fold2/log.md`. No file under `ZInQKernel/`, `blueprint/` or
`scratch/h-decomposition/` was edited, and no other task's notes or scratch files. This is model
work, with no human review.

Marks:
- **VERIFIED**: compiled, or read in a file.
- **STANDARD**: published, with a reference.
- **SPECULATIVE**: a judgement.
- **UNVERIFIED**: a theorem number recalled without a source (there is no network here).

## 0. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
    (l : OpenAddedLeaves2) (g : OpenGlue2) : ZInQ.SixContactMin
```

**VERIFIED.** It has no `sorry`, and `#print axioms` gives `[propext, Classical.choice,
Quot.sound]`. The checks are in §5.

The hypotheses are 66 named Props, and none of them is an `opaque` placeholder:

| bundle | fields | kind |
|---|---|---|
| `OpenResearchLeaves2` | 26 | research-level leaves (R1-R22, H5). R1(b), R10, R14 and R17 appear in concrete or corrected form |
| `OpenTextbookLeaves2` | 18 | textbook leaves |
| `OpenAddedLeaves2` | 12 | leaves that the wave 26-27 reductions introduced: 9 LEAF, 3 LEAF? (composite leaf candidates) |
| `OpenGlue2` | 10 | glue still to be proved by the project |

**Count before and after.** Before, the open statement was g0-assemble2's
`sixContactMin_of_leaves3` with leaf-fold's closures applied. That means `ResearchLeaves3` (24),
plus leaf-fold's `OpenTextbookLeaves` (26), plus `GluePieces3` (40).

| | research leaves | textbook leaves | added leaves (LEAF/LEAF?) | glue | total |
|---|---|---|---|---|---|
| before (g0-assemble2 + leaf-fold) | 24 | 26 | 18 | 22 | **90** |
| after (`sixContactMin_of_open2`) | 26 | 18 | 12 | 10 | **66** |

The research-leaf count rises by two because two fields move into that bundle (see the first bullet
below). Glue falls from 22 to 10, and the literature side (leaves) from 68 to 56. For comparison:
- leaf-fold's own `sixContactMin_of_open` has 26 + 26 + 11 = 63 fields. Two of them are `opaque`,
  and its 11 glue pieces are the large unsplit ones.
- g0-assemble2's `sixContactMin_of_leaves3` has 24 + 35 + 40 = 99 fields.

What changed:
- **Moved, not proved.** R1(b) and R17 replace the `opaque` placeholders of leaf-fold's bundle.
  They are g0-assemble2's concrete `r1bFamily` and `carayolR17`, and they move from the glue bundle
  to the research leaves.
- **Merged into existing leaves.** `r14Det` merges into R14, and `g9R10Weights` merges into
  R10 (`PkgI4.DeRhamComparisonHT`, r10-amend).
- **Proved.** 13 fields are proved, and one more follows from a leaf already in the bundle:
  - textbook leaves: T14(a′), T14(b′), T36, T37;
  - added leaves: `mulEtale` (through `MulIsogeny`), `constOrOntoAlgClosed`;
  - glue: `smoothStalkDimOne`, `ratFactorAlgClosed`, `g9AbVarBaseChange`, `oMaximal`,
    `endTransport`, `cotangentSpanBC`, `uniformizationLiftAnalytic`, `productUnifSplits`,
    `unramifiedConjugates`. That is 9 glue fields;
  - from the textbook leaf T35: the glue `productMetrizationOfProductUnif` (unif-dims, with
    infra-smooth-dim's `TangentDimAtOrigin`).
- **Derived.** T39 follows from T40.
- **No longer used.** Two glue fields are dropped: `artinTorsionSurj` and `conjUniformization`.
  conj-twist's final theorem needs neither.
- **Unused textbook leaves deleted.** Seven textbook fields are unused, as g0-assemble2 found
  (§3).

## 1. What was folded, and how Lean checks each statement

Each closed field is a theorem `HDec.HSyn.xxx_proved`. Its type is the file's own Prop, and its
proof is the imported or copied theorem, so Lean checks that the two statements agree.

- **Kernel modules.** Their Props over Mathlib-only definitions are accepted by a plain term proof
  (definitional unfolding, as in leaf-fold §2).
- **Structures.** For statements over a structure of which the kernel has its own copy, there are
  two methods:
  - an explicit field-by-field map: `toP1K` for `ToP1`, and `toAbVarK` for `TangentDimAtOrigin`'s
    `AbVar`, whose fields are all Mathlib types;
  - for proofs that build objects (AbVarBC, unif-dims), the proof is copied over the file's objects.

  Structures are nominal, so a kernel `PkgI3.AbVar` is a different type from `HDec.PkgI3.AbVar`.
  VERIFIED, read in both files.

| field (bundle before) | kind | proof folded in | how | source task |
|---|---|---|---|---|
| `t14a`, `t14b` (T14(a′), T14(b′); textbook) | LEAF | `ZInQ.Contrib.T14.brauerHasse2C`, `brauerReciprocity2C` (`ZInQKernel/Contrib/T14/Main.lean`) | import, `exact` | t1415-tc, kw-new (Tau Ceti's Kummer index bound) |
| T36 `X1Belyi.TorsionStructure` (in `x1`) | LEAF | `ZInQ.RLeaf.t36_torsionStructure` | import, `exact` | rleaf-elliptic |
| T37 `X1Belyi.GoodReductionUnramified` (in `x1`) | LEAF | `ZInQ.RLeaf.T37.t37_goodReductionUnramified` | import, `exact` | rleaf-elliptic |
| T39 `X1Belyi.X1ConstantField` (in `x1`) | LEAF | **from T40**: `ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp` | import | rleaf-elliptic |
| T28 `PkgI1.IgusaClebschSeparation` | LEAF (unused) | `T28.igusaClebschSeparation_proved` (`Contrib/T28/Assemble.lean`) | import, `exact` (recorded only; the field is unused, §3) | t28-igusa, igusa-generic, igusa-special |
| `smoothStalkDimOne` (C1b) | GLUE | `LeafQM.AV.Pin.smoothStalkDimOne` (image-plane's copy of infra-smooth-dim's proof) | module `LF2ImagePlane`, `exact` | infra-smooth-dim, image-plane |
| `constOrOntoAlgClosed` (C2K) | LEAF | `LeafQM.AV.Pin.constOrOntoAlgClosed` | `LF2ImagePlane`, through `toP1K` | image-plane |
| `ratFactorAlgClosed` (C3K) | GLUE | `LeafQM.AV.Pin.ratFactorAlgClosed` | `LF2ImagePlane`, through `toP1K` | image-plane, curve-glue |
| `MobiusGlue` (inside `FibreSimple` and `thetaPoint`) | (derived) | `mobiusGlue_of_t5'` from T5 and the three facts above (mobius-glue's `mobiusGlue_of_curves'`) | proved | image-plane |
| `mulEtale` (used only via `MulIsogeny`) | LEAF | `ZInQ.Contrib.AbVarBC.mulIsogeny` | `Contrib/AbVarBC` copied over the file's objects (part b10) | g9-abvarbc |
| `KerUnitOpen` (not on the route) | LEAF | `ZInQ.Contrib.AbVarBC.kerUnitOpen` | part b10; recorded as `kerUnitOpen_proved` | g9-abvarbc |
| `g9AbVarBaseChange` | GLUE | `ZInQ.Contrib.AbVarBC.abVarBaseChange` | part b10 | g9-abvarbc |
| `g9R10Weights` | LEAF | the second half of R10 corrected (`PkgI4.deRhamComparisonHT_iff`); G9 is then `g9Glue_of_deRhamComparisonHT` | proved from `r.r10` | g9-derham, r10-amend |
| `oMaximal` | GLUE | `G0ModField.KernelField.oMaximal` | kernel-field's later `New.lean` (commits 8a8d29bf, 3106cab5) replaces part a75's older copy (`mk_a75.py`) | kernel-field |
| `endTransport` | GLUE | `endTransport_of (endTransportBC_of_rigidity G0FibreSimple.rigidityHom)`; `RigidityHom` is proved by mul-rigidity | same | kernel-field, mul-rigidity |
| `artinTorsionSurj`, `conjUniformization` | GLUE | no longer used: G10 comes from `G0Galois.conjTwistNontrivial_of_leaves : T5 → T26 → T35 → HomLinearLift → ConjTwistNontrivial` | conj-twist's §13-§16 copied (part b05). Its later commit added `[NumberField K]` to `ConjUniformization`, and a30's copy was updated (diff: no other change) | conj-twist |
| `productUnifSplits` | GLUE | `ZInQ.ProductUnif.productUnifSplits` (no hypotheses) | product-unif §1-§3 copied (part b08, `mk_b08.sh`) | product-unif |
| `productMetrizationOfProductUnif` | GLUE | **from T35**: `ZInQ.UnifDims.productMetrizationOfProductUnif_of_tangentDim t.t35 tangentDimAtOrigin_proved` | unif-dims' `Combined.lean` chain copied (part b09, `mk_unifdims.py`; root lemmas in module `LF2UnifRoot`); `TangentDimAtOrigin` from infra-smooth-dim's `SmoothDimProps.lean` (module `LF2SmoothDim`, namespaces renamed `LF2.*`), transferred through `toAbVarK`. In metrization2's transport section a local field-by-field coercion `ZInQ.DefFaltings.AbVar → PkgI3.AbVar` (= `LeafAdopt.abVarEquiv`) is added, since Leaves.lean has two copies of the structure where the kernel has one | unif-dims, infra-smooth-dim, product-unif, metrization2 |
| `unramifiedConjugates` | GLUE | `G0ModField.unramifiedConjugates` (Mathlib only) | `scratch/inner-twist/UnramConj.lean` verbatim as module `LF2UnramConj`, `exact` | inner-twist |
| `cotangentSpanBC`, `uniformizationLiftAnalytic` | GLUE | `ZInQ.HeightBC.cotangentSpanBC`, `uniformizationLiftAnalytic` | infra-stalks' `HeightBCGlue.lean`: its Part 3 copied (part b07), its Part 1 as module `LF2Stalks` | infra-stalks |
| `r1bFamily` | LEAF | moved to `OpenResearchLeaves2.r1b` (R1(b) concretely; it was the `opaque` `r1an`) | — | fibre-qm-period, g0-assemble2 |
| `carayolR17` | LEAF | moved to `OpenResearchLeaves2.r17` (it was the `opaque` `r17`) | — | g0-mod-newform, g0-assemble2 |
| `r14Det` | LEAF | merged with R14 (`OpenResearchLeaves2.r14 : G0Galois.R14Det`, leaf-fold's correction) | — | g0-mod-galois, leaf-fold |

**r1b-state.** Its leaf `R1bState.R01b_ComplexUniformization'` is not used. The R1(b) field stays
fibre-qm-period's `R1bFamily`. r1b-state reports that two bridges are still needed before its form
implies `R1bFamily`: bp-analytic's `IsUniformization` with `qmAct`, and `HolomorphicP1On` to
`IsHolP1At` (VERIFIED, read in docs/research/r1b-state.md).

## 2. Every remaining field

LEAF means a published theorem, or a consequence of one, stated over genuine definitions. LEAF? is
a leaf candidate: a composite of published results. GLUE is to be proved by the project. Locators are
those of the source reports, all UNVERIFIED here. "Last touched" names the last task that changed
the field's statement or role.

### 2.1 `OpenResearchLeaves2` (26, all LEAF)

| field : Prop | content | last touched |
|---|---|---|
| `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), R2, R5 on `X₆` (canonical model of the Shimura curve, its Atkin–Lehner quotient) | pin-apply (six-clause `R1fpProps`) |
| `r1b : ∀ h, FibreQM.R1bFamily (ownY …) (ownΦ …) (ownπ …)` | R1(b), complex uniformization in family form (Shimura 1967 Main Thm I; Deligne, Bourbaki 389) | fibre-qm-period, g0-assemble2; moved here by leaf-fold2 |
| `r1rec : LeafQM.AV.R1rec` | R1(d), Shimura reciprocity | leaf-adopt |
| `r3 : ZInQ.LeafPush2.R03_LinYang` | R3, Lin–Yang | leaf-push2 |
| `r4 : PkgI1.ThetaModularity` | R4, theta modularity | pkg-I1 |
| `r5 : LeafQM.AV.R5fp` | R5(ii) | leaf-qm-fp |
| `r5count : LeafQM.AV.R5fpCount` | R5(i), the CM count | leaf-qm-fp |
| `r6 : PkgI2.RaynaudCriterion` | R6, Raynaud | pkg-I2 |
| `r7a : PkgI2.NeronOggShafarevich` | R7(a), NOS (Serre–Tate 1968 Thm 1) | pkg-I2 |
| `r7b : PkgI2.SerreTatePotentialGood` | R7(b) | pkg-I2 |
| `r8 : PkgI2.GrothendieckMonodromy` | R8 | pkg-I2 |
| `r9a : PkgI3.FaltingsSemisimple` | R9(a), Faltings 1983 | pkg-I3 |
| `r9b : PkgI3.FaltingsTate` | R9(b), Faltings 1983 | pkg-I3 |
| `r10 : PkgI4.DeRhamComparisonHT` | R10 corrected, with the multiplicity-0 clause (Faltings 1988, Tate 1967) | g9-derham, r10-amend, leaf-fold |
| `r11r12 : PkgI4.PanBerger` | R11 + R12 | pkg-I4 |
| `r13 : PkgI4.EigenformHT` | R13 | pkg-I4 |
| `r14 : G0Galois.R14Det` | R14 with the determinant (Shimura 1971 Thm 7.14; Deligne 1971) | g0-mod-galois, leaf-fold |
| `r15 : DeligneSerreConseq` | R15 | hdec-faithful |
| `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16 | leaf-modcurves |
| `r17 : LadicCond.CarayolR17'` | R17 concretely (Carayol 1986 Thm (A)) | g0-mod-newform, g0-assemble2; moved here by leaf-fold2 |
| `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18 | leaf-push2 |
| `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19 | def-faltings |
| `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20 | def-faltings |
| `r21 : ZInQ.DefFaltings.R21_Bost` | R21 | def-faltings |
| `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22 | leaf-push2 |
| `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5, finiteness half (its `NeronModelMinimal` half is proved) | h5-glue, g0-assemble2 |

### 2.2 `OpenTextbookLeaves2` (18, all LEAF)

| field | content | last touched |
|---|---|---|
| `t5 : PkgI2.TorsionStructure` | T5, `A[n] ≅ (ℤ/n)^{2g}` | pkg-I2 |
| `t6 : PkgI3.HomFreeFinite` | T6, Mumford §19 Thm 3 | pkg-I3 |
| `t7 : PkgI3.CharPolyIndepOfEll` | T7 | pkg-I3 |
| `t8 : PkgI3.PoincareReducibility` | T8 | pkg-I3 |
| `t9 : LeafPush.T09_WeilPairing` | T9 | leaf-push |
| `t10 : T10Etale.T10_TateDuality` | T10 | t10-etale |
| `t11a : ZInQ.LeafPush2.T11a_RiemannEnd` | T11(a) | leaf-push2 |
| `t11b : ZInQ.LeafPush2.T11b_Rigidity` | T11(b) | leaf-push2 |
| `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23 | pkg-I4 |
| `t24 : EigenformTwist` | T24 | hdec-faithful |
| `t26 : PkgI3.TateModuleFree` | T26 | pkg-I3 |
| `t27 : PkgI3.QMDichotomyYu` | T27 | pkg-I3 |
| `t33 : LeafModCurves.JacobianExists ℚ` | T33 | leaf-modcurves |
| `t34 : LeafModCurves.DimJ1Genus` | T34 | leaf-modcurves |
| `t35 : ZInQ.LeafPush2.UniformizationExists` | T35 | leaf-push2 |
| `t38 : X1Belyi.CurveOfFunctionFieldQ` | T38 | x1-belyi; split out of `x1` by leaf-fold2 |
| `t40 : X1Belyi.X1RationalCusp` | T40 (T39 follows from it) | x1-belyi, rleaf-elliptic; split out of `x1` by leaf-fold2 |
| `t41 : ZInQ.H5Neron.NeronModelExists` | T41, Néron models exist | h5-neron |

### 2.3 `OpenAddedLeaves2` (12)

| field | kind | content | last touched |
|---|---|---|---|
| `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | LEAF | CM points via optimal embeddings | fs5-nocm |
| `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` | LEAF? | theta-constant ratios at a CM period matrix are algebraic | g0-thetapoint |
| `qmHauptmodul : PkgI1.QMHauptmodul` | LEAF? | the theta-quotient Hauptmodul of `Γ*` | pkg-I1, fibre-qm-period |
| `qmClassNumberOne : FibreQM.QMClassNumberOne` | LEAF | Eichler class number one, lattice form | fibre-qm-period |
| `qmDenZeroCM3 : FibreQM.QMDenZeroCM3` | LEAF? | Lin–Yang's divisor of `ψ₄` (period-map reduced it to `S8Nonzero`, `S8WeightExact`, `ValenceBoundGammaStar`; not folded) | fibre-qm-period, period-map |
| `burnsideAbsIrred : G0Galois.BurnsideAbsIrred` | LEAF | Burnside's theorem | g0-mod-galois |
| `homLinearLift : G0Galois.HomLinearLift` | LEAF | Birkenhake–Lange Prop. 1.2.1 | conj-twist |
| `senTwist : G0Galois.SenTwist` | LEAF | Sen 1980 | g12-det |
| `finiteImageHT : G0Galois.FiniteImageHT` | LEAF | Tate 1967, Ax–Sen–Tate | g12-det |
| `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | LEAF | T9 restated | weil-pairing |
| `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | LEAF | Mumford §7-8 | weil-pairing |
| `divisiblePoints : WeilPairing.DivisiblePoints` | LEAF | Mumford §4 Appl. 2 | weil-pairing |

### 2.4 `OpenGlue2` (10, all GLUE)

| field | content | last touched; reductions available but not folded |
|---|---|---|
| `x6KummerFibre : FS5NoCM.X6KummerFibre` | the Kummer fibre of `X₆ → P¹` | fs5-nocm; x6-kummer reduces it to `MobiusGlue` (proved here) and a new leaf `X6ConicModel` (§4) |
| `hodgeBCInjective : HeightBC.HodgeBCInjective` | `ψ` injective on the Hodge line | height-bc, infra-stalks (open) |
| `omegaBaseChange : HeightBC.OmegaBaseChange` | `ω` base-changes | height-bc, infra-stalks (open) |
| `periodMapGlue : ∀ h, FibreQM.PeriodMapGlue …` | the period map's fibres and values | fibre-qm-period. period-map reduces it to `BaseChangeClassUnique`, `PiTwistC`, `QMTwistLattice`, `CMDescends` |
| `hauptmodulUnique : FibreQM.HauptmodulUnique` | uniqueness of the normalized Hauptmodul | fibre-qm-period. period-map reduces it to `S8Nonzero`, `SphereFactorAffine` |
| `cPtsTransport : FibreQM.CPtsTransport` | complex points along base change | fibre-qm-period |
| `propTSAll : G0ModField.PropTSAll` | Prop. TS for every admissible cover; truth SPECULATIVE (fibre-cover §3.2) | fibre-cover. prop-ts reduces it to `KummerMeetGlue`, `SpecNonMeeting`, `CoverModelOfHecke` and others |
| `conjIsogMaps : KernelField.ConjIsogMaps` | the conjugacy maps `m_σ = μ_σ ∘ σ` | kernel-field (open) |
| `modelG3 : G0AssembleMod.ModelG3` | G3 on G7's model | g0-assemble2. linked-tate reduces its own `QMModelG3` to `GoodRedTorsion`; that is a different Prop, not folded |
| `linkedTateLocal : G0AssembleMod.LinkedTateLocal` | the linked Tate data with the Frobenius link and local data; truth SPECULATIVE | g0-assemble2 (g8-object's `LinkedTateObj` is a different Prop) |

## 3. The ten `TextbookLeaves` fields that g0-assemble2 found unused

g0-assemble2 §7 found by grep that ten fields are never projected or destructured. leaf-fold2
deletes all ten from `structure TextbookLeaves` in its copy of `Leaves.lean` (`mk_prefix.py`). The
compile of the whole file and of every part succeeds, so Lean confirms that none of them is used
(VERIFIED).

| field | leaf | status | why it is dropped |
|---|---|---|---|
| `t1` | T1, purity of the branch locus | open | unused: the route never applies purity; G2 uses `propTSAll`, not T1 |
| `t2` | T2, Abhyankar (DVR) | proved (leaf-fold) | unused, and proved anyway |
| `t3` | T3, Néron mapping property for abelian schemes | open | unused: E4 uses T41 (Néron models) instead |
| `t4` | T4, reduction is injective on torsion | open | unused: only alg-frob-red's off-route reduction uses it |
| `t16b` | T16(b), local reciprocity with upper numbering | open | unused: D1-D5 go through T20, T21 (proved locally) and g15-ram |
| `t20` | T20, Hilbert's different formula (global) | proved (leaf-fold) | unused, and proved anyway |
| `t21` | T21, Serre's different bound (global) | proved (leaf-fold) | unused, and proved anyway |
| `t28` | T28, Igusa–Clebsch separation | proved (`Contrib/T28`) | unused: QM-PIN made the Igusa step unnecessary. Recorded as `t28_proved` |
| `t29a` | T29(a), normalizer of a division algebra | open | unused (B3's degree bound is `GlueDescent.B3Q.b3_degree_le_QM`, proved without it) |
| `t29b` | T29(b), normalizer in the split case | open | unused, as T29(a) |

The "why" column for the open leaves is a reading of the route (SPECULATIVE in its wording). The
fact that they are unused is VERIFIED by the compile.

## 4. Not folded

- **Reductions, not closures.** These are listed in §2.4: period-map (`periodMapGlue`,
  `hauptmodulUnique`, `qmDenZeroCM3`), prop-ts (`propTSAll`), linked-tate and g8-object (their own
  Props), and r1b-state (§1). Each replaces a field by other named Props, so folding it would not
  shrink the list of open statements. It would only rename them.
- **x6-kummer.** It proves the glue `X6KummerFibre` from `MobiusGlue` and one new leaf
  `X6ConicModel`, the conic model of `X₆ = X₀(6,1)` (VERIFIED, read in docs/research/x6-kummer.md).
  This turns one glue Prop into one new leaf rather than closing it. Not folded: its file copies
  fs5-nocm's §A, which part a60 already holds, so it would need de-duplication. It is the natural
  next step.
- **alg-frob-red** concerns frob-trace's route, not a field of `GluePieces3`.

## 5. Checks (VERIFIED)

**Olean chain.**
- The chain is `LPrefix → TailA → TailB → TailC → TailD → TailE`, plus the modules `LF2ImagePlane` and
  `LF2Stalks`.
- Every module compiles with 0 errors and no `sorry` (times in `log.md`). `LPrefix` takes 582 s and
  `TailC` 193 s; each of the others takes under 110 s.
- In TailE's output, all 27 `#print axioms` lines read `[propext, Classical.choice, Quot.sound]`.
  These include `HDec.HSyn.sixContactMin_of_open2`, `gluePieces_of_open2` and every `*_proved`.
  The output is `scratch/leaf-fold2/olean/TailE_out.txt`, which is not committed: run `./ctail.sh TailE.lean TailE`.

**Flat file.**
- `lake env lean scratch/leaf-fold2/Leaves2.lean` (86 957 lines, final version): **exit 0 in 924 s,
  0 errors, no `sorry`. All 284 `#print axioms` reports read `[propext, Classical.choice,
  Quot.sound]`** (counted by script).
- An earlier flat run failed with 8 errors in part b10, because the root modules' file-level `open`s
  leaked in the single file. Each root-module body is now in its own section (log.md).
- The leaf-fold2 lines of that output are copied into `log.md`. The raw output
  (`flat_out.txt`) contains host paths and is not committed.
- The file still declares Leaves.lean's two `opaque` placeholders, as field types of the old
  `ResearchLeaves`. No field of the four bundles of `sixContactMin_of_open2` mentions them.
- Build first:
  - `lake build ZInQKernel.Contrib.T14.Main ZInQKernel.Contrib.T28.Assemble
    ZInQKernel.Contrib.RLeaf.X1ConstantField ZInQKernel.HDecomp.QM.Pin
    ZInQKernel.HDecomp.Textbook.SkolemNoether`;
  - the modules of leaf-fold §0 and `ZInQKernel.Multiplication.Certificate.ConstantsProperties
    ZInQKernel.Progressions.Final.Instance ZInQKernel.Size.Constants.T`.

**Changes to the copied texts.** Each change is in a script, with its reason:

| script | change | reason |
|---|---|---|
| `mk_parts.py` | `_root_.PkgI4` becomes `_root_.HDec.PkgI4`, and a bare `open ZInQ` becomes `open _root_.ZInQ ZInQ` | the `HDec` wrapper |
| `mk_fix_tailA.py` | eight declarations of part 70 deleted | leaf-fold put identical copies in Leaves.lean; the bodies were checked identical |
| `mk_fix_tailA.py` | part 77's `equivariant_of_asModule` proved by explicit rewrites, same statement | its `simp` no longer closes the goals with the Contrib modules in scope |
| `mk_fix_b.py` | a30's `ConjTwistNontrivial` deleted | leaf-fold copy |
| `mk_fix_b.py` | a30's `ConjUniformization` gets `[NumberField K]` | conj-twist's current text |
| `mk_a75.py` | part a75 takes kernel-field's current `New.lean` | the later commits prove `oMaximal` and `EndTransport` |
| `mk_fix_c.py` | its duplicates of part 40 deleted | duplicates |
| `mk_fix_c.py` | `hR1.2.2.2` becomes `hR1.2.2.2.1` | six-clause `R1fpProps` |
| `mk_fix_c.py` | one `synthInstance.maxHeartbeats 400000` in a95 | an `IsDedekindFiniteMonoid` search timed out |
| `mk_abvarbc.py` | AbVarBC moved over the file's `PkgI3`/`PkgI4` | copied rather than imported (§1) |
| `mk_b07.sh` | infra-stalks' Part 3 lines `open PkgI3 (AbVar)` deleted, as g0-assemble2 did | — |
| `mk_b08.sh` | product-unif §1-§3, lines `open PkgI3 (AbVar)` deleted | same |
| `mk_unifdims.py` | unif-dims' chain without the parts already present (product-height, product-unif §1-§3, g0-dim); root-namespace lemmas moved to module `LF2UnifRoot`; `open ZInQ.LeafPush2` restricted to the six names used; a local coercion between the two abelian-variety structures in one section; infra-smooth-dim's namespaces renamed `LF2.*` in module `LF2SmoothDim` | Leaves.lean's `ZInQ.LeafPush2` repeats most of `ZInQ.DefFaltings`, and it has two `AbVar` structures; the kernel has one of each |

**No statement of a leaf or glue Prop was changed.** There are two exceptions, both forced:
- `TextbookLeaves` loses its ten unused fields;
- a30's copy of `ConjUniformization` gets conj-twist's own current `[NumberField K]`. This only
  weakens the statement, and it is no longer a hypothesis anyway.
