# leaf-fold3: the results since leaf-fold2, folded into one statement of what is still open

Task leaf-fold3, 2026-11-13. Base: 88dc9bd4 (origin/wip/integrate-w46), with origin/wip/kummer-comp
(423d6b7c) and origin/wip/hecke-rest (e27601d8) merged (both have reports). Lean: `scratch/leaf-fold3/`.
The deliverable is the flat file `scratch/leaf-fold3/Leaves3.lean`, built by `assemble.sh` (order in
`scratch/leaf-fold3/BUILD.md`). Results log: `scratch/leaf-fold3/log.md`. No file under `ZInQKernel/`,
`blueprint/`, `scratch/h-decomposition/` or `docs/research/h-decomposition.md`, and no other task's file,
was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; the locators below are the source reports').

## 1. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open3 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves3)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin
```

**VERIFIED.** No `sorry`; `#print axioms HDec.HSyn.sixContactMin_of_open3` gives
`[propext, Classical.choice, Quot.sound]` (olean chain and flat file, §5). Its conclusion is the
kernel's own `ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): `olean/Check3.lean` compiles
`example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open3`.

The hypotheses are 68 named Props; none is an `opaque` placeholder.

| bundle | fields | kind |
|---|---|---|
| `OpenResearchLeaves2` | 26 | research-level leaves (unchanged from leaf-fold2) |
| `OpenTextbookLeaves3` | 20 | textbook leaves (`HomLatticeCorr` for T11(a); T3, T4 back) |
| `OpenAddedLeaves3` | 16 | leaves introduced by reductions: 11 LEAF, 5 LEAF? |
| `OpenGlue3` | 6 | glue to be proved by the project |

**Counts against leaf-fold2** (`sixContactMin_of_open2`, 26 + 18 + 13 + 9 = 66):

| | research | textbook | added (LEAF / LEAF?) | glue | total | of which SPECULATIVE glue |
|---|---|---|---|---|---|---|
| leaf-fold2 | 26 | 18 | 13 (9 / 4) | 9 | 66 | 2 (`propTSAll`, `linkedTateLocal`) |
| leaf-fold3 | 26 | 20 | 16 (11 / 5) | 6 | **68** | **0** |

Glue falls from 9 to 6, and the two glue fields whose truth was SPECULATIVE are gone: each is now a
theorem from leaves and smaller glue. The literature side rises from 57 to 62 because those two
reductions bring their leaves into the open (the four QM facts under Prop. TS, Zariski's connectedness
theorem, and T3/T4, which leaf-fold2 had deleted as unused). The compact count, if `propTSAll` and
`linkedTateLocal` were kept as single glue fields, would be 26 + 18 + 11 + 4 = 59 (§1.2).

### 1.1 What changed (each item is a theorem in `scratch/leaf-fold3/partsF/d90_fold3.lean`)

**Glue closed outright (5).**
- `hodgeBCInjective`, `omegaBaseChange` (hodge-bc2; heightbc-contrib has the same proof over the kernel's
  objects): part c60 = `scratch/hodge-bc2/hbc_proof.lean.part` and `omega_proof.lean.part` verbatim, over
  this file's height-bc copy; theorems `hodgeBCInjective_proved3`, `omegaBaseChange_proved3`.
  `G0Split.StableHeightBaseChange` therefore has no hypothesis left.
- `cPtsTransport` (cpts-transport): part c20 = `scratch/cpts-transport/CPtsTransport.lean`;
  `cPtsTransport_proved3`.
- `conjIsogMaps` (twist-descent): part c40 = kf-glue (g0-assemble3's port, its part d20 lines 431-end;
  lines 16-430 duplicate part a75), part c50 = twist-descent's parts XC, HFD, Main, Final (PartGDM, its unused `GaloisDescentMor`, omitted); `conjIsogMaps_proved3 :=
  conjIsogMaps_of_mulIsogeny mulIsogeny_proved`. **twist-descent's `G0FibreSimple.MulIsogeny` is the Prop
  that g9-abvarbc's `ZInQ.Contrib.AbVarBC.mulIsogeny` proves** (VERIFIED: leaf-fold2's
  `mulIsogeny_proved : G0FibreSimple.MulIsogeny := ZInQ.Contrib.AbVarBC.mulIsogeny`, and here the same
  constant is passed to `conjIsogMaps_of_mulIsogeny`; Lean accepts it), so `ConjIsogMaps` is closed.
- `modelG3` (linked-tate's route + lt-goodred): parts c70 (linked-tate's parts 95-98, as g0-assemble3's
  c10-c15) and c75 (lt-goodred's integration file); `modelG3G6_of_leaves3 hFS r7a r6 t5` gives
  g0-assemble2's `ModelG3G6` from `FibreSimple` and the leaves R7a, R6, T5, with `GoodRedTorsion` proved.

**SPECULATIVE glue replaced by leaves and smaller glue (2).**
- `propTSAll` → `propTSAll_of_pieces3` (part c80, `mk_propts.py`: prop-ts, prop-ts-glue 3d41b3d5,
  ts-kummer, kummer-comp, hecke-rest merged). `KummerMeetGlue` (kummer-comp) and `SpecNonMeeting`
  (prop-ts-glue) are proved, T2 is proved (leaf-fold), `MobiusGlue` follows from T5. What remains is
  hecke-rest's input list for `CoverModelOfHecke`: the leaves `Y3Connected` (R1conn, LEAF?), `QMAutCard`,
  `SerreRigidity3`, `ALFixedPoints`, T5, and the glue `ChartProper`, `ChartQuasiFinite`,
  `HeckeVertWitness`.
- `linkedTateLocal` → `linkedTateLocal_of_leaves3` (part c85, `mk_ltlocal.py`: lt-local's `LtLocal4.lean`,
  unram-roots, frob-pieces' `FrobPiecesFull.lean`, deduplicated against the chain). Details in §1.3.

**Leaves closed or merged.**
- `burnsideAbsIrred` (LEAF) proved from Mathlib (rv-gluepieces2's check, as g0-assemble3's part d10;
  part c10).
- `t11a` (T11(a)) and `homLinearLift` (LEAF) replaced by hom-unify's single leaf `HomLatticeCorr`
  (part c30: the definition verbatim from `ZInQKernel/Contrib/HomUnify/Corr.lean`, with its two proofs
  `homLinearLift_of_corr`, `t11a_riemannEnd_of_corr`). This lowers the count by one, as hom-unify
  recommended.
- `t40` (T40) is **kept**. t40-tate and t40-igusa prove it from the single leaf `X0Transitive`
  (`ZInQ.RLeaf.x1RationalCusp_of_x0Transitive`, `ZInQKernel/Contrib/RLeaf/T40.lean`), but that module
  cannot be imported into this chain: through `TateCuspMuN`/`TateCuspTorsion` it imports Tau Ceti's
  `Backport.Algebra.Group.Units.Basic`, and the environment already contains
  `Units.val_mul_zpow_natCast_mul` from `ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic`
  (imported by the chain's T14/Chebotarev/… modules); Lean refuses the import (VERIFIED, log.md). Since
  `X1Belyi.X1RationalCusp` is over Mathlib definitions only, the kernel theorem discharges this field
  verbatim once the two Tau Ceti copies are reconciled; then T40 becomes `X0Transitive` (same count).

**Imported from the kernel's Contrib instead of copied.**
- `MobiusGlue`'s three curve facts: leaf-fold2's module `LF2ImagePlane` (image-plane's
  `ImagePlaneFinal.lean`) is replaced by `import ZInQKernel.Contrib.Mobius.Main` (mobius-contrib). TailE's
  uses (`_root_.LeafQM.AV.Pin.smoothStalkDimOne`, `constOrOntoAlgClosed`, `ratFactorAlgClosed`) now
  resolve to the Contrib theorems.
- `TangentDimAtOrigin`: `tangentDimAtOrigin_proved3` is dim-contrib's
  `ZInQ.Contrib.Dim.tangentDimAtOrigin` (imported) through leaf-fold2's field map `toAbVarK`; the
  product-metrization step uses it.
- Where the Contrib statement is over the kernel's own structures (`PkgI3.AbVar`, `GroupModel`, …) and this
  file's Prop is over its `HDec` copies, the two Props are nominally different types (structures are
  nominal), so the proof text is copied (hodge-bc2, cpts-transport, kf-glue, twist-descent, linked-tate,
  lt-goodred, prop-ts, lt-local), as leaf-fold2 did for AbVarBC.

**The fork's issue #2, in this copy of `Leaves.lean`** (`mk_prefix.py`):
- (2) the weak `LeafQM.AV.fibre_conjugates_isomorphic` (conclusion not mentioning `j₀`) is replaced by the
  kernel's strengthened statement and proof (`ZInQKernel/HDecomp/QM/Leaves.lean:500`). The old
  declaration had no user.
- (5) the second `#print axioms HSyn.sixContactMin_of_leaves` is dropped.
- (8) the QM "Lemma P" (rv-qm-polar) is renamed "Lemma QP" in all 25 occurrences. The Lean name
  `lemmaP_lattice` is a declaration of `scratch/rv-qm-polar` and `ZInQKernel/HDecomp/QM/Polar.lean`,
  not of this file, so its mention keeps the name with the note "(Lemma QP; Lean name unchanged …)".

**`G7Data` records `[L:ℚ] ≤ D`** (g0-assemble3's fix, `mk_g7bound.py`, parts 75, z85, z86; the diff
against g0-assemble3's parts is the HDec header lines only). lt-local's route needs it, and
`g7OutUnr_of_g4Out` supplies it from G4Out's bound.

### 1.2 Count variants

| variant | research | textbook | added | glue | total |
|---|---|---|---|---|---|
| canonical (`sixContactMin_of_open3`) | 26 | 20 | 16 | 6 | 68 |
| `propTSAll`, `linkedTateLocal` kept as single glue fields (not compiled as a separate theorem) | 26 | 18 | 11 | 4 | 59 |

### 1.3 `linkedTateLocal`: lt-local's ℓ = 5, 3 route (VERIFIED, compiled)

`linkedTateLocal_of_leaves3` is lt-local's `linkedTateLocal_of_tateBridge35` with:
- `UnramRoots 2 5`, `UnramRoots 2 3` from unram-roots' `unramRoots_all` (all `p`, `ℓ`; Mathlib and the
  vendored Tau Ceti);
- `TateBridge35` from frob-pieces' `tateBridge35_of_neron_nmp` (T26, `AbVarSpreadsOut`,
  `ProperSmoothGenConnected`, I2-Red, I2-NMP; afr-absfrob's `AbsFrob` and `FExtendGen` and frob-pieces'
  `SmoothGeomConnIntegral` are proved inside);
- `QMEndRank` from lt-goodred (T6, T27); `FibreSimple` derived in `gluePieces_of_open3`.

Checks asked for by the assignment:
- **lg-kerwild's `exists_localGlue_of_tateModuleFree` is not used** (rv-fast's CONCERN). VERIFIED by a
  dependency-closure check (`scratch/leaf-fold3/olean/Deps3.lean`, a `#eval` over the 179 689 constants
  that `sixContactMin_of_open3` depends on): `LGKerWild.exists_localGlue_of_tateModuleFree` is not in the
  closure. Neither is lg-kerwild's own `localGlue_of_tateBridge35`: the route goes through lt-local's
  `LTLocal.localGlue_at` (the same ℓ = 5, 3 argument, with `UnramRoots` only at `p = 2`), which uses
  lg-kerwild's `kerWild_of_g7` and `descentPts_of_g7` and local-glue's `localGlue_of_descent`. In the closure:
  `LTLocal.localGlue_at`, `LTLocal.g7Clauses_of_transport`, `LTLocal.linkedTateLocalD_of_tateBridge35`,
  `FrobPiecesGood.tateBridge35_of_neron_nmp`, `UnramRootsTask.unramRoots_all`; `sorryAx` is not.
- **`[L:ℚ] ≤ D`** is the last clause of `G7Data` here (§1.1), so lt-local's `g7DegreeBound_gp4` is a
  projection.
- **ε = 1 on `G_L × G_L`** for `TateBridge35`'s data: lt-local's `g7Clauses_of_transport` derives it from
  `G7Data`'s `DescentDatum` (`GlueDescent.B3Q.inflatedNormalized_of`), with `ε'` defined by
  `j(βQ g) j(βQ h) = ε'(g,h) j(βQ(gh))` (VERIFIED, read in `scratch/lt-local/part_g7.lean` l.31-60 and
  compiled here). No other hypothesis of the route is left undischarged: every input above is a field of
  the bundles or a theorem.

## 2. Every remaining hypothesis

LEAF = a published theorem or a consequence of one, stated over genuine definitions. LEAF? = a leaf
candidate (a composite of published results, or a published statement stated on a witness of the leaf
bundle). GLUE = to be proved by the project. Locators are the source reports' (UNVERIFIED here). "Last
task" names the last task that changed the field's statement or role. SPEC = truth SPECULATIVE.

### 2.1 `OpenResearchLeaves2` (26, all LEAF; unchanged from leaf-fold2 §2.1)

| field : Prop | content and source | last task | SPEC |
|---|---|---|---|
| `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), R2, R5 on `X₆`: canonical model of the Shimura curve and its Atkin–Lehner quotient (Shimura 1967 Main Thms I-II; Deligne 1971; Baba–Granath 2008; premise Lemma QP) | pin-apply | no |
| `r1b` (`FibreQM.R1bFamily`, family form) | R1(b), complex uniformization (Shimura 1967 Main Thm I; Deligne, Bourbaki 389) | fibre-qm-period, leaf-fold2 | no |
| `r1rec : LeafQM.AV.R1rec` | R1(d), Shimura reciprocity | leaf-adopt | no |
| `r3 : ZInQ.LeafPush2.R03_LinYang` | R3, Lin–Yang (Igusa–Clebsch invariants on `X₆`) | leaf-push2 | no |
| `r4 : PkgI1.ThetaModularity` | R4, `ψ₄ = 2⁻²Σθ⁸` and `χ₁₀` are Siegel modular forms of weight 4, 10 for `Sp₄(ℤ)` (Igusa 1962, 1967; Igusa, *Theta functions*, Ch. V) | pkg-I1 | no |
| `r5 : LeafQM.AV.R5fp` | R5(ii), González–Rotger 2006 Thm 5.12 (fields of CM points) | leaf-qm-fp | no |
| `r5count : LeafQM.AV.R5fpCount` | R5(i), González–Rotger Prop. 5.6 (`#CM(R) = 2^b h(R)`) | leaf-qm-fp | no |
| `r6 : PkgI2.RaynaudCriterion` | R6, Raynaud (SGA 7 IX 4.7) | pkg-I2 | no |
| `r7a : PkgI2.NeronOggShafarevich` | R7(a), Serre–Tate 1968 Thm 1 | pkg-I2 | no |
| `r7b : PkgI2.SerreTatePotentialGood` | R7(b), Serre–Tate 1968 | pkg-I2 | no |
| `r8 : PkgI2.GrothendieckMonodromy` | R8, SGA 7 IX | pkg-I2 | no |
| `r9a : PkgI3.FaltingsSemisimple` | R9(a), Faltings 1983 | pkg-I3 | no |
| `r9b : PkgI3.FaltingsTate` | R9(b), Faltings 1983 | pkg-I3 | no |
| `r10 : PkgI4.DeRhamComparisonHT` | R10 amended (Faltings 1988, Tate 1967; multiplicity-0 clause) | r10-amend, leaf-fold | no |
| `r11r12 : PkgI4.PanBerger` | R11 + R12 (Pan; Berger) | pkg-I4 | no |
| `r13 : PkgI4.EigenformHT` | R13, Hodge–Tate weights of eigenform representations | pkg-I4 | no |
| `r14 : G0Galois.R14Det` | R14 with determinant (Shimura 1971 Thm 7.14; Deligne 1971) | g0-mod-galois, leaf-fold | no |
| `r15 : DeligneSerreConseq` | R15, Deligne–Serre | hdec-faithful | no |
| `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16, Eichler–Shimura on `J₁(N)` | leaf-modcurves | no |
| `r17 : LadicCond.CarayolR17'` | R17, Carayol 1986 Thm (A) | g0-mod-newform, leaf-fold2 | no |
| `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18, Javanpeykar (Faltings height of `J₁(N)`) | leaf-push2 | no |
| `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19, Gaudron–Rémond isogeny estimate | def-faltings | no |
| `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20, Faltings 1983 Lemma 5 (height under isogeny) | def-faltings | no |
| `r21 : ZInQ.DefFaltings.R21_Bost` | R21, Bost's lower bound | def-faltings | no |
| `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22, Pazuki (theta height vs Faltings height) | leaf-push2 | no |
| `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5, finiteness half (stable Faltings height) | h5-glue | no |

### 2.2 `OpenTextbookLeaves3` (20, all LEAF)

| field | content and source | last task | SPEC |
|---|---|---|---|
| `t3 : PkgI2.NeronMappingAbelianScheme` | T3 = I2-NMP, Néron mapping property of abelian schemes (BLR §1.2) | pkg-I2; back by leaf-fold3 (lt-local route via frob-pieces) | no |
| `t4 : PkgI2.ReductionTorsionBijective` | T4 = I2-Red, reduction bijective on prime-to-`p` torsion (Serre–Tate; Mumford) | pkg-I2; back by leaf-fold3 | no |
| `t5 : PkgI2.TorsionStructure` | T5, `A[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | pkg-I2 | no |
| `t6 : PkgI3.HomFreeFinite` | T6, Mumford §19 Thm 3 | pkg-I3 | no |
| `t7 : PkgI3.CharPolyIndepOfEll` | T7, Mumford §19 / Weil | pkg-I3 | no |
| `t8 : PkgI3.PoincareReducibility` | T8, Poincaré reducibility (Mumford §19) | pkg-I3 | no |
| `t9 : LeafPush.T09_WeilPairing` | T9, Weil pairing (Mumford §20) | leaf-push | no |
| `t10 : T10Etale.T10_TateDuality` | T10, Tate duality | t10-etale | no |
| `homLatticeCorr : HomUnify.HomLatticeCorr` | analytic representation of homomorphisms (Birkenhake–Lange §1.2, Prop. 1.2.1; Mumford §1, §3; GAGA); replaces T11(a) and `HomLinearLift` | hom-unify; folded by leaf-fold3 | no |
| `t11b : ZInQ.LeafPush2.T11b_Rigidity` | T11(b) | leaf-push2 | no |
| `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23, Fontaine | pkg-I4 | no |
| `t24 : EigenformTwist` | T24, twists of eigenforms | hdec-faithful | no |
| `t26 : PkgI3.TateModuleFree` | T26 = I3.M0, `T_ℓA` free of rank `2g` (Mumford §18) | pkg-I3 | no |
| `t27 : PkgI3.QMDichotomyYu` | T27, Yu 2013 Thm 1.1 | pkg-I3 | no |
| `t33 : LeafModCurves.JacobianExists ℚ` | T33, Jacobians exist | leaf-modcurves | no |
| `t34 : LeafModCurves.DimJ1Genus` | T34, `dim J₁(N) = genus` | leaf-modcurves | no |
| `t35 : ZInQ.LeafPush2.UniformizationExists` | T35, `A(ℂ) ≅ ℂ^g/Λ` | leaf-push2 | no |
| `t38 : X1Belyi.CurveOfFunctionFieldQ` | T38, curves from function fields | x1-belyi | no |
| `t40 : X1Belyi.X1RationalCusp` | T40, `K_N` has a degree-one place. In the kernel it follows from `X0Transitive` (Galois transitive on the cyclic subgroups of order `N` of the generic `E_j`, i.e. `X₀(N)` irreducible over `ℚ(j)`; t40-igusa), which could replace it (§1.1: Tau Ceti import clash) | x1-belyi, rleaf-elliptic, t40-igusa | no |
| `t41 : ZInQ.H5Neron.NeronModelExists` | T41, Néron models exist (BLR) | h5-neron | no |

### 2.3 `OpenAddedLeaves3` (16)

| field | kind | content and source | last task | SPEC |
|---|---|---|---|---|
| `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | LEAF | CM points via optimal embeddings (Shimura 1967; Jordan; González–Rotger) | fs5-nocm | no |
| `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` | LEAF? | theta-constant ratios at a CM period matrix are algebraic (Shimura 1976; Mumford, Tata II) | g0-thetapoint | no |
| `qmHauptmodul : PkgI1.QMHauptmodul` | LEAF? | the theta-quotient Hauptmodul of `Γ*` | pkg-I1, fibre-qm-period | no |
| `qmClassNumberOne : FibreQM.QMClassNumberOne` | LEAF | Eichler class number one for `𝒪`, lattice form | fibre-qm-period | no |
| `qmDenZeroCM3 : FibreQM.QMDenZeroCM3` | LEAF? | Lin–Yang's divisor of `ψ₄` (period-map reduces it to `S8Nonzero`, `S8WeightExact`, `ValenceBoundGammaStar`; not folded) | fibre-qm-period, period-map | no |
| `senTwist : G0Galois.SenTwist` | LEAF | Sen 1980 | g12-det | no |
| `finiteImageHT : G0Galois.FiniteImageHT` | LEAF | Tate 1967, Ax–Sen–Tate | g12-det | no |
| `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | LEAF | symmetric isogeny to a dual (Mumford §§6, 8, 20, 23) | weil-pairing | no |
| `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | LEAF | Mumford §7-8 | weil-pairing | no |
| `divisiblePoints : WeilPairing.DivisiblePoints` | LEAF | Mumford §4 Appl. 2 | weil-pairing | no |
| `x6ConicModel : X6Kummer.X6ConicModel` | LEAF? | the conic model of `X₆` (Elkies 1998 §3; Kurihara 1979), on one witness | x6-kummer | no |
| `y3Connected : TSHecke.Y3Connected` | LEAF? | R1conn: `Y₃` connected over `ℚ`, on one witness of R1fp (Shimura; Deligne, Bourbaki 389 §§2-3, PSPM 33 §2.1, Thm 2.6.3; computation `scratch/ts-hecke/pi0_check.py`) | ts-hecke; folded by leaf-fold3 | no |
| `qmAutCard : HeckeRest.QMAutCard` | LEAF | `#Aut(A, ι) ∈ {4, 6, 2}` by CM type (Shimura's classification of `End⁰`; Rotger 2003) | hecke-rest; folded by leaf-fold3 | no |
| `serreRigidity3 : HeckeRest.SerreRigidity3` | LEAF | Serre's lemma, level 3, finite-order form (Serre, Sém. Cartan 1960/61 exp. 17; Silverberg–Zarhin 1996) | hecke-rest; folded by leaf-fold3 | no |
| `alFixedPoints : HeckeRest.ALFixedPoints` | LEAF | fixed points of `w₂, w₃, w₆` on `X₀⁶(1)` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (Ogg 1983; Rotger 2004) | hecke-rest; folded by leaf-fold3 | no |
| `properSmoothGenConnected : FrobPiecesNeron.ProperSmoothGenConnected` | LEAF? | Zariski's connectedness theorem for smooth proper schemes over `𝓞_L[1/f]` (EGA III₁ 4.3) | frob-pieces; folded by leaf-fold3 | no |

### 2.4 `OpenGlue3` (6, all GLUE)

| field | content | last task; reductions not folded | SPEC |
|---|---|---|---|
| `periodMapGlue : ∀ h, FibreQM.PeriodMapGlue …` | the period map's fibres and values | fibre-qm-period. period-map reduces it to `BaseChangeClassUnique` (now proved by cpts-transport), `PiTwistC`, `QMTwistLattice`, `CMDescends`: folding would replace 1 field by 3 | no |
| `hauptmodulUnique : FibreQM.HauptmodulUnique` | uniqueness of the normalized Hauptmodul | fibre-qm-period. period-map: `S8Nonzero`, `SphereFactorAffine` (1 → 2) | no |
| `chartProper : HeckeRestCurve.ChartProper` | the two charts of `π : Y₃ → P¹` are proper (curve theory) | hecke-rest | no |
| `chartQuasiFinite : HeckeRestCurve.ChartQuasiFinite` | the two charts are locally quasi-finite | hecke-rest | no |
| `heckeVertWitness : HeckeRestNV.HeckeVertWitness` | one unramified vertical prime above `p > 324` (equivalent to Lemma NV) | hecke-rest | no (hecke-rest: true, route h-b1 §3) |
| `abVarSpreadsOut : FrobPiecesNeron.AbVarSpreadsOut` | N1-g1: an abelian variety over a number field spreads out to an abelian scheme over `𝓞_L[1/f]` (EGA IV₃ 8.8.2, 8.10.5; IV₄ 17.7.8) | neron-lg, frob-pieces | no |

## 3. The remaining leaves by the theory they come from

The 62 leaves (26 + 20 + 16) fall into eight groups. Counts are of bundle fields.

| group (published theory) | # | fields |
|---|---|---|
| **A. Shimura curves with quaternionic multiplication** (Shimura 1967, 1971; Deligne, Bourbaki 389; Baba–Granath 2008; González–Rotger 2006; Rotger 2003-2004; Ogg 1983; Elkies 1998; Kurihara 1979; Eichler; Lin–Yang) | 14 | `r1r2`, `r1b`, `r1rec`, `r3`, `r5`, `r5count`, `cmOptimalEmbedding`, `qmHauptmodul`, `qmClassNumberOne`, `qmDenZeroCM3`, `x6ConicModel`, `y3Connected`, `qmAutCard`, `alFixedPoints` |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa 1962, 1967, 1972; Shimura 1976; Mumford, Tata II) | 2 | `r4`, `thetaRatiosAlgebraic` |
| **B. Abelian varieties: the textbook theory** (Mumford, *Abelian varieties*; Birkenhake–Lange; Milne; Yu 2013 for T27; Serre's lemma) | 16 | `t5`, `t6`, `t7`, `t8`, `t9`, `t10`, `homLatticeCorr`, `t11b`, `t26`, `t27`, `t35`, `t09SymmIsogenyExists`, `isogenyQuasiInverse`, `divisiblePoints`, `serreRigidity3`, `t4` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate 1968; SGA 7; Raynaud; EGA III for Zariski's connectedness) | 7 | `r6`, `r7a`, `r7b`, `r8`, `t3`, `t41`, `properSmoothGenConnected` |
| **D. Faltings 1983 and Faltings heights** (Faltings; Gaudron–Rémond; Bost; Pazuki; Javanpeykar) | 8 | `r9a`, `r9b`, `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` |
| **E. p-adic Hodge theory** (Faltings 1988; Tate 1967; Sen 1980; Fontaine; Berger; Pan) | 6 | `r10`, `r11r12`, `r13`, `t23`, `senTwist`, `finiteImageHT` |
| **F. Galois representations of modular forms** (Shimura 1971; Deligne 1971; Deligne–Serre; Carayol 1986; Eichler–Shimura) | 5 | `r14`, `r15`, `r16`, `r17`, `t24` |
| **G. Modular and algebraic curves** (Jacobians; `X₀(N)`, `X₁(N)`; function fields of curves) | 4 | `t33`, `t34`, `t38`, `t40` (in the kernel: from `X0Transitive`) |
| total | **62** | |

So `SixContactMin` follows, by a compiled Lean proof, from: the arithmetic theory of the Shimura curve
`X₀⁶(1)` and its QM abelian surfaces (A), Igusa's theta description of genus-2 Siegel modular forms (A′), the textbook theory of abelian varieties (B) and of Néron
models (C), Faltings' theorems and the height estimates around them (D), p-adic Hodge theory (E), the
Galois representations attached to modular forms (F) and basic modular-curve facts (G); plus the six
glue Props of §2.4 (two on the period map of `X₆`, three on the Hecke cover of `P¹`, one on spreading
out abelian varieties). The grouping is a reading of the docstrings (SPECULATIVE in its boundaries:
`serreRigidity3`, `t4` could go under B or C; `qmHauptmodul`, `qmDenZeroCM3` are about theta quotients on
`X₆` and could go under A′).

## 4. Corrections to h-decomposition.md §3

Written as a patch, not an edit: `scratch/leaf-fold3/h-decomposition-section3.patch`
(`git apply --check` succeeds on the base). It updates the glue-pieces table of §3:
- **DimFinite, DimBaseChange, ProductExists, HeightCopiesAgree**: proved outright (g0-dim, g0-product,
  `G0HeightCopies.heightCopiesAgree`).
- **ReverseIsogeny**: proved from the leaves R19, H5 and `DimFinite` (`reverseIsogeny_of_leaves3`).
- **StableHeightBaseChange**: proved outright (height-bc's four glue Props, all proved by infra-stalks
  and hodge-bc2; in the kernel as heightbc-contrib's `ZInQ.HeightBC.stableHeightBaseChange`).
- **MobiusGlue**: proved from T5 (image-plane; mobius-contrib in the kernel).
- **FibreSimple, ProductModelHeight**: proved from leaves; **ThetaPointOfFibre, ModularConstituent**: open,
  reduced to the leaves and the six glue Props of §2.4.

## 5. Checks

**Olean chain** (`scratch/leaf-fold3/chain.sh`, one Lean process at a time; times in `log.md`):
`LPrefix` (558 s) → `TailA`-`TailD` → `LF2Stalks`, `LF2UnifRoot`, `LF2SmoothDim`, `LF2UnramConj`, `LF3Cot`
→ `TailE` → `TailF` (parts c10-c75) → `TailG` (c80, Prop. TS) → `TailH` (c85, lt-local route) → `TailI`
(d90, the bundles): every module 0 errors, no `sorry`. The 16 `#print axioms` lines of `TailI` (every
`*_proved3`, `propTSAll_of_pieces3`, `linkedTateLocal_of_leaves3`, `gluePieces_of_open3`,
`sixContactMin_of_open3`, hom-unify's two lemmas) all read `[propext, Classical.choice, Quot.sound]`
(VERIFIED). The copied parts' own `#print` lines are dropped; the axioms of everything they prove are
covered by the closure of `sixContactMin_of_open3`.

**Flat file** `scratch/leaf-fold3/Leaves3.lean` (110 826 lines, md5 703c1618fd1f…, all chain sources in
one file): `lake env lean scratch/leaf-fold3/Leaves3.lean` **exits 0 in 1042 s, 0 errors, no `sorry`; all 288
`#print axioms` reports read `[propext, Classical.choice, Quot.sound]`** (counted by script; 5 of them are
line-wrapped). An earlier flat run (before the `simpa only` edit of `mk_propts.py`) had 1 error in kummer-comp's
Abhyankar core, where the flat file's simp set differs from the olean chain's (log.md). The raw output
`flat_out.txt` contains host paths and is not committed.

**Dependency closure** (`olean/Deps3.lean`, 25 s): the closure of `HDec.HSyn.sixContactMin_of_open3` has
179 689 constants; it contains the proofs folded here (`twistDescent`, `hodgeBCInjective`, `omegaBaseChange`,
`goodRedTorsion`, `burnsideAbsIrred`, `KummerComp.kummerMeetGlue`, `PropTSGlue.specNonMeeting`, the kernel's
`ZInQ.Contrib.Dim.tangentDimAtOrigin` and `LeafQM.AV.Pin.smoothStalkDimOne` from Contrib.Mobius) and not
`sorryAx` or `LGKerWild.exists_localGlue_of_tateModuleFree` (VERIFIED).

**Changes to the copied texts** (each in a script, with its reason):

| script | change | reason |
|---|---|---|
| `mk_prefix.py` | issue #2 items 2, 5, 8 | the assignment |
| `mk_g7bound.py` | `G7Data` gains `Module.finrank ℚ L ≤ heightD`; three proof adjustments (g0-assemble3's text) | lt-local's route needs `[L:ℚ] ≤ D` |
| `mk_lf3.py` | leaf-fold's HDec edits (`_root_.PkgI4` → `_root_.HDec.PkgI4`; `open … ZInQ` also opens root `ZInQ`); `#print`/`#check`/`import` lines dropped (this also drops one docstring line of hecke-rest that begins with the word `import`); `open PkgI3 (AbVar)` dropped in c60; kf-glue's lines 16-430 (duplicates of part a75) and twist-descent's PartGDM (the unused `GaloisDescentMor`, not defined in the kf-glue port) omitted | the HDec wrapper; duplicates |
| `mk_propts.py` | merge of PropTS.lean, PropTSGlue.lean, KummerComp.lean, HeckeRestAll.lean with duplicate declarations dropped (by full name, with their `… in` modifiers; also identical text); `rw [bcPt, …]` → `rw [LeafQM.AV.bcPt, …]`; one `simpa using h1` → `simpa only [RingHom.comp_apply, map_natCast] using h1`; `synthInstance.maxHeartbeats 400000` | the files share a verbatim prefix; two names are open at once in this chain; the flat file's simp set; instance search with this chain's larger instance set |
| `mk_ltlocal.py` | merge of LtLocal4.lean, UnramRoots.lean, FrobPiecesFull.lean with declarations already in the chain dropped (by full name; anonymous instances by namespace and text). The dropped copies whose text differs from the chain's: `G0Galois.resQ`, `G14Trace.FrobTraceLink`, `G0Dim.pkgI3_dim_baseChange`, `LeafAdopt.abVarEquiv` (docstrings, blank lines, `rfl` fields), and frob-pieces' `G7Data`, `g7OutUnr_of_g4Out`, `g7Out_of_g7OutUnr`, `modularConstituent_of_ranges` (the version without the `[L:ℚ] ≤ D` clause); the chain's versions are used and the copied proofs compile against them | duplicates; none of these is a hypothesis of `sixContactMin_of_open3`, so the choice cannot change what the theorem assumes |
| `assemble.sh` | `LF2ImagePlane` replaced by `import ZInQKernel.Contrib.Mobius.Main`; new modules `LF3Cot`, `TailF`-`TailI`; anonymous sections left open by a copied file are closed before its part's `end` (`py/balance.py`) | §1.1 |

**No statement of a remaining leaf or glue Prop was changed.** The bundles' field types are the source
files' own definitions (§2); the only definition changed is `G7Data` (g0-assemble3's fix), which is not a
field type.

## 6. Not folded, and why

- **period-map's reductions** of `periodMapGlue`, `hauptmodulUnique` and `qmDenZeroCM3`: each replaces one
  field by two or three (with `BaseChangeClassUnique` proved by cpts-transport, `periodMapGlue` would
  become `PiTwistC`, `QMTwistLattice`, `CMDescends`). Not folded, so as not to grow the list with renamings.
- **ts-sn**: not needed; prop-ts-glue's final file (3d41b3d5) already proves `SNSpecialize` and
  `SpecNonMeeting`.
- **ts-hecke's current `TSHecke.lean`**: hecke-rest's `HeckeRestAll.lean` contains the earlier ts-hecke
  file it was built on, whose `HeckeFibreSizes` has the extra clause `∀ P, #fibre ≤ M` that hecke-rest
  proves; that version is used (`mk_propts.py`).
- **linked-frob** (`LinkedFrob` from the same four inputs) and **g8-tate** (`TateBridgeOnL`): alternatives
  to lt-local's route; lt-local's needs no `KernelFieldBreaks` and no `TateRamAtThree`, so it was taken.
- **afr-absfrob, frob-pieces, alg-frob-red**: folded inside lt-local's route (part c85).
- **heightbc-contrib, mobius-contrib, dim-contrib**: their theorems are over the kernel's structures; the
  first is folded by copying hodge-bc2's proof text (the Props are nominally different), the other two
  are imported (§1.1).
