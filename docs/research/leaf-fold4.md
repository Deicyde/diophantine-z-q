# leaf-fold4: the results since leaf-fold3, folded into one statement of what is still open

Task leaf-fold4, 2026-11-13. Base 8ec80711 (fork main after w47), with origin/wip/leaf-fold3 (f7951690),
period-glue (7e1531df), zariski-conn (3802f2bc), t5-torsion (58ac8d0b), homlattice (89a1fc02),
kerwild-fix (f596943a), frobchain-contrib (f4bf0b72) and hecke-rest (6c2c1d76) merged; spread-out
(aa304ed7) was already in the base. origin/wip/vert-witness and origin/wip/t40-clash did not exist
during the run (no report to merge). Lean: `scratch/leaf-fold4/` (build order `BUILD.md`, `chain.sh`,
`assemble.sh`; results log `log.md`). No file under `ZInQKernel/`, `blueprint/`, `scratch/h-decomposition/`
or `docs/research/h-decomposition.md`, and no other task's file, was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; the locators below are the source reports').

## 1. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open4 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves4)
    (l : OpenAddedLeaves4) (g : OpenGlue4) : ZInQ.SixContactMin
```

**VERIFIED.** No `sorry`; `#print axioms HDec.HSyn.sixContactMin_of_open4` gives
`[propext, Classical.choice, Quot.sound]` (olean chain and flat file, §5). Its conclusion is the
kernel's own `ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): `olean/Check4.lean` compiles
`example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open4`.

The hypotheses are 66 named Props; none is an `opaque` placeholder.

| bundle | fields | kind |
|---|---|---|
| `OpenResearchLeaves2` | 26 | research-level leaves (unchanged since leaf-fold2) |
| `OpenTextbookLeaves4` | 19 | textbook leaves (leaf-fold3's 20 without T26) |
| `OpenAddedLeaves4` | 20 | leaves introduced by reductions: 13 LEAF, 7 LEAF? |
| `OpenGlue4` | 1 | glue to be proved by the project: `HeckeVertWitness` |

**Counts against leaf-fold3** (`sixContactMin_of_open3`, 26 + 20 + 16 + 6 = 68):

| | research | textbook | added (LEAF / LEAF?) | glue | total |
|---|---|---|---|---|---|
| leaf-fold3 | 26 | 20 | 16 (11 / 5) | 6 | 68 |
| leaf-fold4 | 26 | 19 | 20 (13 / 7) | **1** | **66** |

Glue falls from 6 to 1 (five glue fields closed: three proved outright, two reduced to leaves). The
literature side goes from 62 to 65: four leaf fields leave (T26 and `DivisiblePoints`, now theorems from T5;
`QMDenZeroCM3`, now a theorem from R4 and two period-glue leaves; `ProperSmoothGenConnected`, replaced by
Zariski's theorem in its published form) and seven enter (Zariski's connectedness theorem, three EGA IV
statements under N1-g1, and period-map/period-glue's `CMDescends`, `GammaStarGen`, `ValenceBoundGammaStar`).
The one remaining glue Prop, `HeckeVertWitness`, is equivalent to hecke-rest's `HeckeNoVertRam` (Lemma NV);
the parallel task vert-witness is working on it.

### 1.1 What changed (each item is a theorem in `scratch/leaf-fold4/partsF/d95_fold4.lean`)

**Glue proved outright (3).**
- `chartProper`, `chartQuasiFinite` (hecke-rest, final version 6c2c1d76): `mk_propts.py` re-run on the merged
  `scratch/hecke-rest/HeckeRestAll.lean`, so part c80 now contains `HeckeRestCurve.chartProper` (Mathlib's
  valuative criterion) and `chartQuasiFinite_of_proper` (Stacks 02UP, Jacobson); `chartProper_proved4`,
  `chartQuasiFinite_proved4`. hecke-rest's `coverModelOfHecke_of_heckeRest` no longer takes them, so the one
  call in leaf-fold3's d90 was adjusted (its two arguments became unused).
- `hauptmodulUnique` (period-glue): period-map's `hauptmodulUnique_of'` with period-glue's `s8Nonzero_proof`
  (a certified theta evaluation, `Re Σθ⁸(Ω(√2+i)) < 0`) and `sphereFactorAffine_proof` (open mapping,
  removable singularities, injective holomorphic maps of `P¹`); `hauptmodulUnique_proved4`. Part c90
  (`mk_periodglue.py`) is period-map's five parts and period-glue's six files plus its end-to-end theorem,
  over the chain.

**Glue reduced to leaves (2).**
- `periodMapGlue` (period-glue): `periodMapGlue_of_leaves4 h t5 homLatticeCorr cmDescends` is period-map's
  `periodMapGlue_own` with period-glue's `baseChangeClassUnique_proof`, `piTwistC_of` (with
  `twistOrbitFinite_of'`, `fibreTransferC_proof`), `qmTwistLattice_of'`, period-map's `piCMC_of` and
  `cmFixedHasCM_of`. Its two non-leaf inputs are **kernel theorems, used directly**:
  `AutOInnerFinite` is mobius-glue's `LeafQM.AV.Pin.autOInnerFinite` (`ZInQKernel/Contrib/Mobius/Glue.lean`)
  and Skolem–Noether is `TSkolemKW.leafSkolemNoether` (`ZInQKernel/HDecomp/Textbook/SkolemNoether.lean`).
  period-glue's `T11aRiemannHom` is derived from the existing leaf `HomLatticeCorr`
  (`t11aRiemannHom_of_corr4`, both clauses at `g = h`), so it adds no leaf. New leaf candidate: `CMDescends`.
- `abVarSpreadsOut` (spread-out): `abVarSpreadsOut_of_ega4` applies the kernel's
  `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega` (imported) to `toAbVarK4 B`, the kernel's abelian
  variety with the same scheme `B.X`. New leaves: EGA IV₃ 8.8.2 (ii), 8.10.5 (xii), IV₄ 17.7.8 (ii).

**Leaves closed or replaced.**
- `qmDenZeroCM3` (LEAF?) is a theorem: period-map's `qmDenZeroCM3_of''` with `s8Nonzero_proof` and period-glue's
  `s8WeightExact_of` (`qmDenZeroCM3_of_leaves4`), from R4 (`ThetaModularity`, already a research leaf) and the
  leaf candidates `GammaStarGen` and `ValenceBoundGammaStar` (−1 +2).
- `properSmoothGenConnected` (LEAF?) is replaced by Zariski's connectedness theorem in its published form,
  `ZariskiConn.ZariskiConnectedness` (zariski-conn, `ZInQKernel/Contrib/ZariskiConn/Basic.lean`, imported;
  `properSmoothGenConnected_of_zariski4`). Same count; LEAF? becomes LEAF.
- `t26` (T26 = I3.M0, `TateModuleFree`) is a theorem from T5 (t5-torsion's
  `T5Torsion.TateFree.tateModuleFree_of_torsionStructure`, file `T5Full.lean` compiled as root module
  `LF4T5`; `tateModuleFree_of_t5'`). The two `TorsionStructure`s (chain copy, kernel) differ only nominally;
  `torsionStructureK_of4` transports the class `IsAbelianVariety` (−1).
- `divisiblePoints` (LEAF) is no longer needed: its only use was G12's `tatePairingZl_of_leaves`, through the
  surjectivity of `T_ℓ A → A(K̄)[ℓᵏ]`; `tatePairingZl_of_leaves4` is that proof verbatim with the surjectivity
  taken from T5 (`T5Torsion.TateFree.tate_surj_of_torsionStructure`), and `gluePieces_of_open4` is leaf-fold3's
  `gluePieces_of_open3` with `detTate_of_leaves4` in its place (`mk_d95_glue.py`, the replacements listed there) (−1).

**How the kernel's theorems are used over the chain's copies.** The chain's structures are copies inside
`namespace HDec` (`HDec.PkgI3.AbVar`, `HDec.LeafQM.O`, …), nominally different from the kernel's. Lean
accepted every one of the following by definitional unfolding, with no proof work (VERIFIED, TailK): the kernel's
`autOInnerFinite` (over `_root_.LeafQM.O`) as this file's `AutOInnerFinite`; `leafSkolemNoether`;
`properSmoothGenConnected_of_zariskiConnectedness` as `FrobPiecesNeron.ProperSmoothGenConnected` (both over
Mathlib only); `NF.abVarSpreadsOut_of_ega … (toAbVarK4 B)` as `AbVarSpreadsOut … B`; T5 and T26 across the
two `PkgI2`/`PkgI3` copies. The dependency closure check (§5) confirms the kernel constants are the ones used.

### 1.2 Count variants

| variant | research | textbook | added | glue | total |
|---|---|---|---|---|---|
| leaf-fold3 (`sixContactMin_of_open3`) | 26 | 20 | 16 | 6 | 68 |
| **canonical (`sixContactMin_of_open4`)** | 26 | 19 | 20 | 1 | **66** |
| + vert-witness (not compiled here): `HeckeVertWitness` → leaf `ShimuraGoodReduction` + glue `SpecialFibreUniformizer`, `ModelCoordinate`, `ModelComparison` | 26 | 19 | 21 | 3 | 69 |
| + homlattice (not compiled here): `HomLatticeCorr` → `StrongUniformizationExists` + `GAGAMorphism` (T35 stays: `Strong → UniformizationExists` is not proved) | 26 | 20 | 20 | 1 | 67 |
| t5-torsion's further options (not compiled): T5 → `TorsionCardNonC`, or T5 → `KernelDegree` + `MulUnramifiedPosChar` | 26 | 19 | 20 | 1 | 66 / 67 |

vert-witness (report 28b716b6) reduces `HeckeVertWitness` to one leaf (good reduction of `Y₃`, Morita/Carayol)
and three glue Props; it raises the glue count, so it is not folded into the canonical statement. homlattice's
swap would raise the count by one in this assembly, because `UniformizationLeafAll` is not a field here (T35 is),
so it is not folded (the assignment's condition).

## 2. Every remaining hypothesis

LEAF = a published theorem or a consequence of one, stated over genuine definitions. LEAF? = a leaf
candidate (a composite of published results, or a published statement stated on a witness of the leaf
bundle). GLUE = to be proved by the project. Locators are the source reports' (UNVERIFIED here). "Last
task" names the last task that changed the field's statement or role. SPEC = truth SPECULATIVE.

### 2.1 `OpenResearchLeaves2` (26, all LEAF; unchanged since leaf-fold2)

| field : Prop | content and source | last task | SPEC |
|---|---|---|---|
| `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), R2, R5 on `X₆`: canonical model of the Shimura curve and its Atkin–Lehner quotient (Shimura 1967 Main Thms I-II; Deligne 1971; Baba–Granath 2008; premise Lemma QP) | pin-apply | no |
| `r1b` (`FibreQM.R1bFamily`, family form) | R1(b), complex uniformization (Shimura 1967 Main Thm I; Deligne, Bourbaki 389) | fibre-qm-period, leaf-fold2 | no |
| `r1rec : LeafQM.AV.R1rec` | R1(d), Shimura reciprocity | leaf-adopt | no |
| `r3 : ZInQ.LeafPush2.R03_LinYang` | R3, Lin–Yang (Igusa–Clebsch invariants on `X₆`) | leaf-push2 | no |
| `r4 : PkgI1.ThetaModularity` | R4, `ψ₄ = 2⁻²Σθ⁸` and `χ₁₀` are Siegel modular forms of weight 4, 10 for `Sp₄(ℤ)` (Igusa 1962, 1967; Igusa, *Theta functions*, Ch. V); since leaf-fold4 also an input of `QMDenZeroCM3` (period-glue's `s8WeightExact_of`) | pkg-I1 | no |
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


### 2.2 `OpenTextbookLeaves4` (19, all LEAF; leaf-fold3's 20 without `t26`)

| field | content and source | last task | SPEC |
|---|---|---|---|
| `t3 : PkgI2.NeronMappingAbelianScheme` | T3 = I2-NMP, Néron mapping property of abelian schemes (BLR §1.2) | pkg-I2; back by leaf-fold3 (lt-local route via frob-pieces) | no |
| `t4 : PkgI2.ReductionTorsionBijective` | T4 = I2-Red, reduction bijective on prime-to-`p` torsion (Serre–Tate; Mumford) | pkg-I2; back by leaf-fold3 | no |
| `t5 : PkgI2.TorsionStructure` | T5, `A[n] ≅ (ℤ/n)^{2g}` (Mumford §4) | pkg-I2; t5-torsion: also gives T26 (`tateModuleFree_of_t5'`) and replaces `DivisiblePoints` in G12 (`detTate_of_leaves4`); on subfields of `ℂ` it is a corollary of T35 (t5-torsion, not used here) | no |
| `t6 : PkgI3.HomFreeFinite` | T6, Mumford §19 Thm 3 | pkg-I3 | no |
| `t7 : PkgI3.CharPolyIndepOfEll` | T7, Mumford §19 / Weil | pkg-I3 | no |
| `t8 : PkgI3.PoincareReducibility` | T8, Poincaré reducibility (Mumford §19) | pkg-I3 | no |
| `t9 : LeafPush.T09_WeilPairing` | T9, Weil pairing (Mumford §20) | leaf-push | no |
| `t10 : T10Etale.T10_TateDuality` | T10, Tate duality | t10-etale | no |
| `homLatticeCorr : HomUnify.HomLatticeCorr` | analytic representation of homomorphisms (Birkenhake–Lange §1.2, Prop. 1.2.1; Mumford §1, §3; GAGA); replaces T11(a) and `HomLinearLift` | hom-unify; folded by leaf-fold3 | no |
| `t11b : ZInQ.LeafPush2.T11b_Rigidity` | T11(b) | leaf-push2 | no |
| `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | T23, Fontaine | pkg-I4 | no |
| `t24 : EigenformTwist` | T24, twists of eigenforms | hdec-faithful | no |
| `t27 : PkgI3.QMDichotomyYu` | T27, Yu 2013 Thm 1.1 | pkg-I3 | no |
| `t33 : LeafModCurves.JacobianExists ℚ` | T33, Jacobians exist | leaf-modcurves | no |
| `t34 : LeafModCurves.DimJ1Genus` | T34, `dim J₁(N) = genus` | leaf-modcurves | no |
| `t35 : ZInQ.LeafPush2.UniformizationExists` | T35, `A(ℂ) ≅ ℂ^g/Λ` | leaf-push2 | no |
| `t38 : X1Belyi.CurveOfFunctionFieldQ` | T38, curves from function fields | x1-belyi | no |
| `t40 : X1Belyi.X1RationalCusp` | T40, `K_N` has a degree-one place. In the kernel it follows from `X0Transitive` (Galois transitive on the cyclic subgroups of order `N` of the generic `E_j`, i.e. `X₀(N)` irreducible over `ℚ(j)`; t40-igusa), which could replace it (§1.1: Tau Ceti import clash) | x1-belyi, rleaf-elliptic, t40-igusa | no |
| `t41 : ZInQ.H5Neron.NeronModelExists` | T41, Néron models exist (BLR) | h5-neron | no |


### 2.3 `OpenAddedLeaves4` (20)

| field | kind | content and source | last task | SPEC |
|---|---|---|---|---|
| `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | LEAF | CM points via optimal embeddings (Shimura 1967; Jordan; González–Rotger) | fs5-nocm | no |
| `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` | LEAF? | theta-constant ratios at a CM period matrix are algebraic (Shimura 1976; Mumford, Tata II) | g0-thetapoint | no |
| `qmHauptmodul : PkgI1.QMHauptmodul` | LEAF? | the theta-quotient Hauptmodul of `Γ*` | pkg-I1, fibre-qm-period | no |
| `qmClassNumberOne : FibreQM.QMClassNumberOne` | LEAF | Eichler class number one for `𝒪`, lattice form | fibre-qm-period | no |
| `senTwist : G0Galois.SenTwist` | LEAF | Sen 1980 | g12-det | no |
| `finiteImageHT : G0Galois.FiniteImageHT` | LEAF | Tate 1967, Ax–Sen–Tate | g12-det | no |
| `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | LEAF | symmetric isogeny to a dual (Mumford §§6, 8, 20, 23) | weil-pairing | no |
| `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | LEAF | Mumford §7-8 | weil-pairing | no |
| `x6ConicModel : X6Kummer.X6ConicModel` | LEAF? | the conic model of `X₆` (Elkies 1998 §3; Kurihara 1979), on one witness | x6-kummer | no |
| `y3Connected : TSHecke.Y3Connected` | LEAF? | R1conn: `Y₃` connected over `ℚ`, on one witness of R1fp (Shimura; Deligne, Bourbaki 389 §§2-3, PSPM 33 §2.1, Thm 2.6.3; computation `scratch/ts-hecke/pi0_check.py`) | ts-hecke; folded by leaf-fold3 | no |
| `qmAutCard : HeckeRest.QMAutCard` | LEAF | `#Aut(A, ι) ∈ {4, 6, 2}` by CM type (Shimura's classification of `End⁰`; Rotger 2003) | hecke-rest; folded by leaf-fold3 | no |
| `serreRigidity3 : HeckeRest.SerreRigidity3` | LEAF | Serre's lemma, level 3, finite-order form (Serre, Sém. Cartan 1960/61 exp. 17; Silverberg–Zarhin 1996) | hecke-rest; folded by leaf-fold3 | no |
| `alFixedPoints : HeckeRest.ALFixedPoints` | LEAF | fixed points of `w₂, w₃, w₆` on `X₀⁶(1)` are CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (Ogg 1983; Rotger 2004) | hecke-rest; folded by leaf-fold3 | no |

| `zariskiConnectedness : ZariskiConn.ZariskiConnectedness.{0}` | LEAF | Zariski's connectedness theorem in its published form: `f` proper, `Y` locally noetherian, `𝒪_Y(U) → 𝒪_X(f⁻¹U)` bijective ⇒ `f` geometrically connected (EGA III₁ 4.3.1 with 4.3.4; Hartshorne III 11.3); replaces leaf-fold3's LEAF? `properSmoothGenConnected` (zariski-conn: `properSmoothGenConnected_of_zariskiConnectedness`, kernel Contrib, imported) | zariski-conn; folded by leaf-fold4 | no |
| `cmDescends : FibreQM.PeriodMapH.CMDescends` | LEAF? | a level-3 QM surface over `ℂ` with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is the base change of one over `ℚ̄` with the same CM (Shimura–Taniyama 1961; Shimura 1998 §12; with T11b and `A[3](ℚ̄) = A[3](ℂ)`; flagged for a human check, period-glue §5.2) | period-map; folded by leaf-fold4 | no |
| `gammaStarGen : FibreQM.PeriodGlue.GammaStarGen` | LEAF? | `Γ* ⊆ ⟨ι(1+i+j), ι((j−3)/2), ℚ^×⟩` (signature `(0;2,4,6)`: Takeuchi 1977, Elkies 1998 §3, Baba–Granath; Poincaré's polygon theorem, Beardon §9.8; numerically checked on 30 elements; period-glue §5.3) | period-glue; folded by leaf-fold4 | no |
| `valenceBoundGammaStar : FibreQM.PeriodMap.ValenceBoundGammaStar` | LEAF? | valence bound `2 Σ_T ord_τ F ≤ m` for weight-`2m` forms on `Γ*` (valence formula: Shimura 1971 Thm 2.20, Prop. 2.16; Rankin Thm 4.1.4; with the signature above; period-glue §5.1) | period-map; folded by leaf-fold4 | no |
| `egaIV_8_8_2_ii : ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii` | LEAF | EGA IV₃ 8.8.2 (ii): a finitely presented scheme over `lim Dᵢ` (qcqs, affine transitions) descends to some `Dᵢ` (Stacks 01ZM) | spread-out; folded by leaf-fold4 | no |
| `egaIV_8_10_5_xii : ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | LEAF | EGA IV₃ 8.10.5 (xii): properness descends to some stage (Stacks 081F) | spread-out; folded by leaf-fold4 | no |
| `egaIV_17_7_8_ii : ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii` | LEAF | EGA IV₄ 17.7.8 (ii): smoothness descends to some stage (Stacks 07RP) | spread-out; folded by leaf-fold4 | no |

### 2.4 `OpenGlue4` (1, GLUE)

| field | content | last task; reductions not folded | SPEC |
|---|---|---|---|
| `heckeVertWitness : HeckeRestNV.HeckeVertWitness` | one unramified vertical prime above each `p > 324` in the Hecke cover (equivalent to Lemma NV, `HeckeNoVertRam`) | hecke-rest. vert-witness reduces it to the leaf `ShimuraGoodReduction` and three glue Props (`SpecialFibreUniformizer`, `ModelCoordinate`, `ModelComparison`): 1 → 4, not folded (§1.2) | no (hecke-rest: true, route h-b1 §3) |

## 3. The remaining leaves by the theory they come from

The 65 leaves (26 + 19 + 20) fall into nine groups. Counts are of bundle fields.

| group (published theory) | # | fields |
|---|---|---|
| **A. Shimura curves with quaternionic multiplication** (Shimura 1967, 1971; Shimura–Taniyama 1961; Deligne, Bourbaki 389; Baba–Granath 2008; González–Rotger 2006; Rotger 2003-2004; Ogg 1983; Elkies 1998; Kurihara 1979; Takeuchi 1977; Eichler; Lin–Yang) | 16 | `r1r2`, `r1b`, `r1rec`, `r3`, `r5`, `r5count`, `cmOptimalEmbedding`, `qmHauptmodul`, `qmClassNumberOne`, `x6ConicModel`, `y3Connected`, `qmAutCard`, `alFixedPoints`, `cmDescends`, `gammaStarGen`, `valenceBoundGammaStar` |
| **A′. Theta functions and Siegel modular forms of genus 2** (Igusa 1962, 1967, 1972; Shimura 1976; Mumford, Tata II) | 2 | `r4`, `thetaRatiosAlgebraic` |
| **B. Abelian varieties: the textbook theory** (Mumford, *Abelian varieties*; Birkenhake–Lange; Milne; Yu 2013 for T27; Serre's lemma) | 14 | `t5`, `t6`, `t7`, `t8`, `t9`, `t10`, `homLatticeCorr`, `t11b`, `t27`, `t35`, `t09SymmIsogenyExists`, `isogenyQuasiInverse`, `serreRigidity3`, `t4` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate 1968; SGA 7; Raynaud) | 6 | `r6`, `r7a`, `r7b`, `r8`, `t3`, `t41` |
| **C′. Scheme theory: limits and connectedness** (EGA III₁ 4.3; EGA IV₃ 8.8, 8.10; EGA IV₄ 17.7) | 4 | `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_8_10_5_xii`, `egaIV_17_7_8_ii` |
| **D. Faltings 1983 and Faltings heights** (Faltings; Gaudron–Rémond; Bost; Pazuki; Javanpeykar) | 8 | `r9a`, `r9b`, `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` |
| **E. p-adic Hodge theory** (Faltings 1988; Tate 1967; Sen 1980; Fontaine; Berger; Pan) | 6 | `r10`, `r11r12`, `r13`, `t23`, `senTwist`, `finiteImageHT` |
| **F. Galois representations of modular forms** (Shimura 1971; Deligne 1971; Deligne–Serre; Carayol 1986; Eichler–Shimura) | 5 | `r14`, `r15`, `r16`, `r17`, `t24` |
| **G. Modular and algebraic curves** (Jacobians; `X₀(N)`, `X₁(N)`; function fields of curves) | 4 | `t33`, `t34`, `t38`, @@T40@@ |
| total | **65** | |

So `SixContactMin` follows, by a compiled Lean proof, from these nine bodies of published mathematics and the
one glue Prop `HeckeVertWitness`. The grouping is a reading of the docstrings (SPECULATIVE in its boundaries:
`serreRigidity3`, `t4` could go under B or C; `gammaStarGen`, `valenceBoundGammaStar` are facts about the
Fuchsian group `Γ*` and could form their own group).

**Flagged for a human check** (from the source reports): `CMDescends` (period-glue §5.2: CM-type hypothesis and
"up to isomorphism" in Shimura–Taniyama), `ValenceBoundGammaStar` (§5.1: normalization of `e_P` and weight),
`GammaStarGen` (§5.3: orientation in Poincaré's theorem); the seven LEAF? fields are `thetaRatiosAlgebraic`,
`qmHauptmodul`, `x6ConicModel`, `y3Connected`, `cmDescends`, `gammaStarGen`, `valenceBoundGammaStar`.

## 4. Corrections to h-decomposition.md §3

Written as a patch, not an edit: `scratch/leaf-fold4/h-decomposition-section3.patch` (`git apply --check`
succeeds on this base). It contains leaf-fold3's patch (rows 1-12 of the glue-pieces table, which is still not
applied to `docs/research/h-decomposition.md`) with these updates:
- the status line now names leaf-fold4 and `sixContactMin_of_open4` (26 + 19 + 20 leaves, 1 glue Prop);
- **row 9, ThetaPointOfFibre**: proved from leaves (no glue left: `PeriodMapGlue`, `HauptmodulUnique`,
  `QMDenZeroCM3` are theorems from leaves and kernel theorems);
- **row 10, ModularConstituent**: reduced to leaves and the one glue Prop `HeckeVertWitness` (ChartProper and
  ChartQuasiFinite proved; N1-g1 from EGA IV; Zariski's theorem; `DetTate` without `DivisiblePoints`; T26 from T5);
- **row 12, MobiusGlue**: also from T35 alone (t5-torsion), not used here.
Other parts of h-decomposition.md that predate leaf-fold2-4 (its leaf lists in §§1-2 and the earlier glue
counts) are stale in the same way; leaf-fold4.md §2 is the current list.

## 5. Checks

**Olean chain** (`scratch/leaf-fold4/chain.sh`, one Lean process at a time; times in `log.md`): `LPrefix`
(625 s) → `TailA`-`TailD` → `LF2Stalks`, `LF2UnifRoot`, `LF2SmoothDim`, `LF2UnramConj`, `LF3Cot` → `TailE` →
`TailF` → `TailG` (c80 with hecke-rest's curve proofs) → `TailH` → `TailI` (leaf-fold3's d90) → `LF4T5`
(t5-torsion's `T5Full.lean`, root namespace) → `TailJ` (c90, period-map + period-glue) → `TailK` (d95, the
bundles): every module 0 errors, no `sorry`. The 17 `#print axioms` lines of `TailK` all read
`[propext, Classical.choice, Quot.sound]` (VERIFIED).

**Kernel conclusion and dependency closure** (`olean/Check4.lean`, 28 s): `example : (∀ r t l g,
_root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open4` compiles. The closure of
`HDec.HSyn.sixContactMin_of_open4` has 181 113 constants. It contains `HeckeRestCurve.chartProper`,
`chartQuasiFinite_of_proper`, period-glue's `s8Nonzero_proof`, `sphereFactorAffine_proof`,
`baseChangeClassUnique_proof`, `piTwistC_of`, `qmTwistLattice_of'`, `s8WeightExact_of`, the kernel's
`LeafQM.AV.Pin.autOInnerFinite`, `TSkolemKW.leafSkolemNoether`,
`ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness`, `ZInQ.Contrib.SpreadOut.NF.abVarSpreadsOut_of_ega`,
t5-torsion's `tateModuleFree_of_torsionStructure` and `tate_surj_of_torsionStructure`, lt-local's
`localGlue_at`; it does **not** contain `sorryAx`, `WeilPairing.DivisiblePoints`, the old
`tatePairingZl_of_leaves`/`detTate_of_leaves`, leaf-fold3's `gluePieces_of_open3`, or lg-kerwild's
`exists_localGlue_of_tateModuleFree` (VERIFIED).

@@FLAT@@

**Changes to the copied texts** (each in a script, with its reason; leaf-fold3's are unchanged, see
leaf-fold3.md §5):

| script | change | reason |
|---|---|---|
| `mk_propts.py` (re-run) | the merged hecke-rest `HeckeRestAll.lean` (final): part c80 gains the curve proofs | hecke-rest's final version |
| `partsF/d90_fold3.lean` | `propTSAll_of_pieces3` calls `coverModelOfHecke_of_heckeRest` without `hP hQ` (now unused arguments) | hecke-rest's new signature |
| `mk_periodglue.py` | period-map's five parts, period-glue's six files and final part in PGAll's order; `import`/`#print` lines dropped; dedup by full name only (none dropped; `mk_propts_walk.py` with `TEXT_DEDUP = False`, since identical text in another namespace is not a duplicate); `open ZInQ.LeafPush2 (CPts cptObj IsUniformization …)` after each `namespace HSyn.G0Split.FibreQM…` line (the chain's a80_fqm has the same `open`; FibreQM.lean had copies in `HSyn.G0Split`); `_root_.PeriodGlue.` → `_root_.HDec.PeriodGlue.` | the HDec wrapper and g0-assemble2's port of fibre-qm-period |
| `mk_d95_glue.py` | `gluePieces_of_open4` = d90's `gluePieces_of_open3` with eight textual replacements (listed in the script, each asserted to occur once); `tatePairingZl_of_leaves4` = TailB's `tatePairingZl_of_leaves` with one argument replaced | §1.1 |
| `assemble.sh`, `chain.sh` | modules `LF4T5`, `TailJ`, `TailK`; flat file `Leaves4.lean` | §1.1 |

**No statement of a remaining leaf or glue Prop was changed.** Every field type is a source file's own
definition (§2).

## 6. Not folded, and why

- **vert-witness** (report at 18:26): `HeckeVertWitness` from the leaf `ShimuraGoodReduction` and three glue Props.
  Folding would raise the glue from 1 to 3 (§1.2), so it is recorded as a variant only.
- **homlattice**: `homLatticeCorr_of_strong_gaga`. In this assembly `UniformizationLeafAll` is not a field
  (T35 `UniformizationExists` is, and `StrongUniformizationExists → UniformizationExists` is not proved), so
  replacing `HomLatticeCorr` by `StrongUniformizationExists` + `GAGAMorphism` raises the count by one; not
  folded (the assignment's condition).
- **kerwild-fix**: `KWFix.TateBridgeE`/`tateBridge35E` would give ε₅ = 1 and `[L:ℚ] ≤ D` from `G4Out`; here both
  already hold on lt-local's route (`G7Data` carries `[L:ℚ] ≤ D`; ε = 1 from the descent datum, leaf-fold3 §1.3),
  and lg-kerwild's every-`ℓ` theorem is not on the route (closure check), so it lowers no count. Not folded.
- **frobchain-contrib**: its theorems (`ZInQ.Contrib.FrobChain.tateBridge35_of_neron_nmp`, …) are over the
  kernel's `PkgI3.AbVar`, `G14Bridge.TateBridge35`, `FrobPiecesNeron.AbVarSpreadsOut`; the chain's Props of the
  same names are the HDec copies, so the Props are not the same constants and the copied proofs (part c85) stay.
  The two Props that are over Mathlib only are used from the kernel: `ProperSmoothGenConnected` (via
  zariski-conn) and `SmoothGeomConnIntegral` (already imported by leaf-fold3 from `Contrib/FrobPieces`).
  (SPECULATIVE: the defeq transport that worked for `AbVarSpreadsOut` would probably also work for
  `TateBridge35`; it changes no count and was not tried.)
- **t5-torsion, other options**: dropping T5 altogether needs T26 in general (about 40 glue theorems pass
  `TateModuleFree` on over all fields), so T5 stays as the leaf, as t5-torsion recommends ((a) + (e) are folded).
  `mobiusGlue_of_T35` is not used (MobiusGlue still comes from T5 through `mobiusGlue_of_t5'`; same leaves).
- **spread-out's `abVarSpreadsOut_of_ega_loc`** (17.7.8 replaced by the glue `SmoothAtLocalizationBaseChange`):
  trades a leaf for glue; not used.
