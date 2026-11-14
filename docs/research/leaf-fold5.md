# leaf-fold5: the last glue Prop of leaf-fold4 folded in, group-B/C/G leaves weakened, 27 fields on kernel Props

Task leaf-fold5, 2026-11-13/14. Base ee7582da (wip/integrate-w52: fork main 71dc3f1b with stab-clash, smooth-fibre,
model-glue, tyz-35, tyz-lcal), which contains leaf-fold4. Nothing was merged. Lean: `scratch/leaf-fold5/` (build
order `BUILD.md`, `chain.sh`, `assemble.sh`, the part generators `mk_e10.py`, `mk_e20.py`; results log `log.md`).
No file under `ZInQKernel/`, `blueprint/`, `scratch/h-decomposition/` or `docs/research/h-decomposition.md`, and no
other task's file, was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source
(there is no network here; the locators below are the source reports').

## 1. Main result

```lean
theorem HDec.HSyn.sixContactMin_of_open5 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves5)
    (l : OpenAddedLeaves5) (g : OpenGlue5) : ZInQ.SixContactMin
```

**VERIFIED.** No `sorry`; `#print axioms HDec.HSyn.sixContactMin_of_open5` gives
`[propext, Classical.choice, Quot.sound]` (olean chain, §4; flat file: FLAT_RESULT). Its conclusion is the kernel's
own `ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`): `olean/Check5.lean` compiles
`example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open5`.

The hypotheses are 70 named Props; none is an `opaque` placeholder.

| bundle | fields | kind |
|---|---|---|
| `OpenResearchLeaves5` | 26 | research-level leaves (leaf-fold2's 26; six of them now stated over the kernel's Props) |
| `OpenTextbookLeaves5` | 21 | textbook leaves: 17 LEAF, 4 LEAF? |
| `OpenAddedLeaves5` | 21 | leaves introduced by reductions: 12 LEAF, 9 LEAF? |
| `OpenGlue5` | 2 | glue to be proved by the project: `ModelCoordinateResidue`, `SimpleImageIsogeny` |

**Counts against leaf-fold4** (`sixContactMin_of_open4`, 26 + 19 + 20 + 1 = 66):

| | research | textbook | added | glue | total | LEAF / LEAF? / GLUE |
|---|---|---|---|---|---|---|
| leaf-fold4 | 26 | 19 | 20 | 1 | 66 | 58 / 7 / 1 |
| **leaf-fold5** | 26 | 21 | 21 | **2** | **70** | **55 / 13 / 2** |

`HeckeVertWitness`, leaf-fold4's last glue Prop, is now a theorem (goal (a)): from vert-witness's leaf
`ShimuraGoodReduction`, model-glue's textbook statement `CurveBijIso`, the existing fields `r1r2` and `t5`, and one
new glue Prop, model-glue's `ModelCoordinateResidue` (the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`; not proved anywhere).
smooth-fibre's `SmoothFibreReduced` enters as the kernel's theorem. So the glue Prop on the Hecke route is replaced
by a smaller one, and two leaf candidates enter. The second glue Prop, av-b1's `SimpleImageIsogeny`, comes from
goal (b)'s replacement of T8 by Poincaré's published complement theorem; keeping T8 as a leaf would give
26 + 21 + 21 + 1 = 69 with glue 1 (§1.3).

Goal (b) replaces nine textbook fields by strictly weaker published statements or theorems:
T3 → its surjective half; T6, T7 → their algebraically closed forms (Mumford's own setting); T8 → Poincaré's
complement theorem (+ glue); T9 → a theorem from two existing fields; T11(b) → its existence half; T34 → its two
halves; T38 → three statements with its rational-point clause proved; T41 → the scheme-level Néron model (group law
proved); and `serreRigidity3` (Serre's lemma) is a theorem from T35 and `HomLatticeCorr`.

Goal (c): 27 of the 70 fields are now the kernel's own constants (leaf-fold4: 5). The 11 kernel leaves of
av-b1/curves-g/neron-c are used directly (their kernel theorems are applied to the chain's objects through
leaf-fold4's `toAbVarK4`/`ofAbVarK4`), and 11 more fields (R6, R7a, R7b, R8, R9a, R9b, T4, T5, T27, T33, T35)
are restated over the kernel's Props, with a proved transport to the chain's copy (part e40). smooth-fibre's two
lemmas, which model-glue had copied, are the kernel's.

### 1.1 What changed (each item is a theorem in `scratch/leaf-fold5/parts/`)

**(a) `HeckeVertWitness` from leaves and one smaller glue Prop** (part e10 = vert-witness's `VertMain.lean.part`
and model-glue's `ModelGlue{,2,…,6}.lean.part`, ported into `namespace HDec` by `mk_e10.py`; part e90).
`heckeVertWitness_of_leaves5 hL r.r1r2 (torsionStructure_ofK5 t.t5) g.modelCoordinateResidue l.curveBijIso` is
model-glue's `ModelGlue.heckeVertWitness_of_curveBijIso`, which is vert-witness's `heckeVertWitness_of_leaves` with
- `SmoothFibreReduced` := the kernel's `ZInQ.SmoothFibre.smoothFibreReduced` (`ZInQKernel/Contrib/SmoothFibre/Basic.lean`;
  the statement is over Mathlib only, so Lean accepts the kernel's term; model-glue's verbatim copy of the proof is
  dropped);
- `ModelCoordinate` := `modelCoordinate_of_residue` (Gauss criterion) from the glue `ModelCoordinateResidue`;
- `ModelComparison` := `modelComparison_of_curveBijIso` (comparison morphism `𝒴_ℚ → Y`, integrality, function
  fields; all proved) from T5 (through `TwistClassFinite`) and the leaf candidate `CurveBijIso`.
Port edits (`mk_e10.py`, each asserted to occur once): the kernel's `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`
for model-glue's verbatim copy; model-glue's uses of the kernel's `curveFacts` and `smoothStalkDimOne` (over the
kernel's `ToP1`) replaced by the chain's own `HSyn.curveFacts5` (`curveFacts_of_leaves` with leaf-fold3's three
`_proved` theorems, which are the kernel's theorems through `toP1K`; the same term leaf-fold3's `mobiusGlue_of_t5'`
uses) and `HSyn.smoothStalkDimOne_proved`. No declaration of the two tasks' parts was already in the chain; no
statement was changed (`ShimuraGoodReduction`, `CurveBijIso`, `ModelCoordinateResidue`, `HeckeVertWitness` are the
source text).

**(b) Leaves replaced by weaker published statements** (parts e20, e30, e90).
- av-b2 (part e20 = `scratch/av-b2/olean/AVB2Main.lean`, namespace `AVB2`, verbatim; it was compiled by av-b2 on
  leaf-fold3's chain, which leaf-fold4's extends; its kernel import `Contrib.AVB2.SerreLemma`):
  `t9_of_leaves5` (T9 from `t09SymmIsogenyExists` + `isogenyQuasiInverse`, −1), `serreRigidity3_of_T35_5`
  (from `t35` + `homLatticeCorr`, −1), `t11b_of_exists5` (T11(b) from `T11bExists`, uniqueness proved; same count).
  av-b2's `DivisiblePoints`/`MulIsogenyPosChar` are not needed (leaf-fold4 removed `DivisiblePoints`).
- av-b1 (kernel `ZInQKernel/Contrib/AVB1/`, imported; part e30): `t6_of_algClosed5`, `t7_of_algClosed5`
  (same count), `t8_of_simpleImage5` (T8 from `PoincareComplement` LEAF + `SimpleImageIsogeny` GLUE, +1).
- curves-g (kernel `ZInQKernel/Contrib/CurvesG/`): `t38_of_split5` (T38's point clause proved; (A), (B), (C):
  +2), `t34_of_split5` (+1). The chain's `IsCurve` class and `IsJacobian` are copies: rebuilt field by field
  (`isJacobianK_of5`).
- neron-c (kernel `ZInQKernel/Contrib/NeronC/`): `t3_of_surj5` (injective half proved; same count),
  `t41_of_extension5` (group law and uniqueness proved; the chain's `NeronModelExists` is over h5-neron's copy
  `ZInQ.DefFaltings.AbVar`, so the kernel's abelian variety is `⟨A.X⟩` and the kernel's `GroupModel` is rebuilt
  field by field; same count).

**(c) Kernel Props for chain copies** (part e40). For each of T5, T4, R6, R7a, R7b, R8, R9a, R9b, T27, T35, T33 a
theorem `*_ofK5 : <kernel Prop> → <chain Prop>`; the classes `IsAbelianVariety`, `IsAbelianScheme`, `IsCurve` are
rebuilt from their fields, abelian varieties pass by `toAbVarK4`/`ofAbVarK4`, `HasGoodReduction` by
`hasGoodReduction_iffK5` (its `IsAbelianScheme` is a copy). R9a needs 8·10⁶ heartbeats (Lean unfolds `galRep` for
about 80 s). The bundles take the kernel's Prop as the field.

### 1.2 Which constants the fields are (VERIFIED, `check5_result.txt`)

Kernel constants (27): research `r6`, `r7a`, `r7b`, `r8`, `r9a`, `r9b`; textbook `t3Surj`, `t4`, `t5`,
`homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t27`, `t33`, `dimJacobianEqGenus`,
`genusX1Field`, `t35`, `normalModelOfFunctionFieldQ`, `normalCurveSmoothQ`, `geomConnectedOfConstantFieldQ`,
`x0Transitive`, `neronSchemeExtensionExists`; added `zariskiConnectedness`, the three EGA IV fields; glue
`simpleImageIsogeny`. The other 43 are the chain's copies inside `namespace HDec` (§5).

### 1.3 Count variants

| variant | research | textbook | added | glue | total |
|---|---|---|---|---|---|
| leaf-fold4 (`sixContactMin_of_open4`) | 26 | 19 | 20 | 1 | 66 |
| **canonical (`sixContactMin_of_open5`)** | 26 | 21 | 21 | 2 | **70** |
| T8 kept as a leaf (not compiled separately; `t8_of_simpleImage5` dropped) | 26 | 21 | 21 | 1 | 69 |
| T8 by av-b1's finer split (`ImageFactorization` + `SimpleSurjIsogeny`, both GLUE; not compiled here) | 26 | 21 | 21 | 3 | 71 |
| without the curves-g splits (T34, T38 kept as leaves) | 26 | 18 | 21 | 2 | 67 |

## 2. Every remaining hypothesis

LEAF = a published theorem or a consequence of one, stated over genuine definitions. LEAF? = a leaf candidate (a
composite of published results, or a published statement whose exact source is not settled). GLUE = to be proved by
the project. Locators are the source reports' (UNVERIFIED here). "Last task" names the last task that changed the
field's statement or role. "K" = the field is the kernel's own constant (§1.2).

### 2.1 `OpenResearchLeaves5` (26, all LEAF)

Unchanged statements since leaf-fold2 (leaf-fold4.md §2.1 has the full sources). Six are now the kernel's Props.

| field | content and source | last task | K |
|---|---|---|---|
| `r1r2 : LeafAdopt.R1R2fpRep` | R1(a,c,d), R2, R5 on `X₆` (Shimura 1967; Deligne 1971; Baba–Granath 2008); also an input of `HeckeVertWitness` (CM objects exist) | pin-apply | |
| `r1b` | R1(b), complex uniformization (Shimura 1967 Main Thm I) | fibre-qm-period, leaf-fold2 | |
| `r1rec : LeafQM.AV.R1rec` | R1(d), Shimura reciprocity | leaf-adopt | |
| `r3 : ZInQ.LeafPush2.R03_LinYang` | R3, Lin–Yang | leaf-push2 | |
| `r4 : PkgI1.ThetaModularity` | R4, Igusa | pkg-I1 | |
| `r5 : LeafQM.AV.R5fp` | R5(ii), González–Rotger 2006 Thm 5.12 | leaf-qm-fp | |
| `r5count : LeafQM.AV.R5fpCount` | R5(i), González–Rotger Prop. 5.6 | leaf-qm-fp | |
| `r6 : PkgI2.RaynaudCriterion` | R6, Raynaud (SGA 7 IX 4.7) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r7a : PkgI2.NeronOggShafarevich` | R7(a), Serre–Tate 1968 Thm 1 | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r7b : PkgI2.SerreTatePotentialGood` | R7(b), Serre–Tate 1968 | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r8 : PkgI2.GrothendieckMonodromy` | R8, SGA 7 IX | pkg-I2; kernel Prop by leaf-fold5 | K |
| `r9a : PkgI3.FaltingsSemisimple` | R9(a), Faltings 1983 | pkg-I3; kernel Prop by leaf-fold5 | K |
| `r9b : PkgI3.FaltingsTate` | R9(b), Faltings 1983 | pkg-I3; kernel Prop by leaf-fold5 | K |
| `r10 : PkgI4.DeRhamComparisonHT` | R10 amended (Faltings 1988, Tate 1967) | r10-amend | |
| `r11r12 : PkgI4.PanBerger` | R11 + R12 (Pan; Berger) | pkg-I4 | |
| `r13 : PkgI4.EigenformHT` | R13 | pkg-I4 | |
| `r14 : G0Galois.R14Det` | R14 with determinant (Shimura 1971 Thm 7.14; Deligne 1971) | g0-mod-galois | |
| `r15 : DeligneSerreConseq` | R15, Deligne–Serre | hdec-faithful | |
| `r16 : LeafModCurves.R16_EichlerShimuraJ1'` | R16, Eichler–Shimura on `J₁(N)` | leaf-modcurves | |
| `r17 : LadicCond.CarayolR17'` | R17, Carayol 1986 Thm (A) | g0-mod-newform | |
| `r18 : ZInQ.LeafPush2.R18_Javanpeykar` | R18, Javanpeykar | leaf-push2 | |
| `r19 : ZInQ.DefFaltings.R19_GaudronRemond` | R19, Gaudron–Rémond | def-faltings | |
| `r20 : ZInQ.DefFaltings.R20_FaltingsLemma5` | R20, Faltings 1983 Lemma 5 | def-faltings | |
| `r21 : ZInQ.DefFaltings.R21_Bost` | R21, Bost | def-faltings | |
| `r22 : ZInQ.LeafPush2.R22_Pazuki` | R22, Pazuki | leaf-push2 | |
| `h5fin : ZInQ.DefFaltings.StableHeightFinite` | H5, finiteness half | h5-glue | |

### 2.2 `OpenTextbookLeaves5` (21: 17 LEAF, 4 LEAF?)

| field | kind | content and source | last task | K |
|---|---|---|---|---|
| `t3Surj : ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj` | LEAF | every `K`-morphism `𝒜_K → ℬ_K` of generic fibres of abelian schemes over a DVR extends (BLR §1.2 Prop. 8, applied with the smooth test scheme `𝒜`); replaces T3, whose injective half is proved (`neronMappingAbelianScheme_injective`) | neron-c; folded by leaf-fold5 | K |
| `t4 : PkgI2.ReductionTorsionBijective` | LEAF | T4 = I2-Red, reduction bijective on prime-to-`p` torsion (Serre–Tate; Mumford) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `t5 : PkgI2.TorsionStructure` | LEAF | T5, `A[n] ≅ (ℤ/n)^{2g}` (Mumford §4); also gives T26 and `TwistClassFinite` (now used by `ModelComparison` too) | pkg-I2; kernel Prop by leaf-fold5 | K |
| `homFreeFiniteAlgClosed : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | LEAF | Mumford, *Abelian varieties* §19 Thm 3 over an algebraically closed field (the published statement); replaces T6 | av-b1; folded by leaf-fold5 | K |
| `charPolyIndepOfEllAlgClosed : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | LEAF | Mumford §19 Thm 4 (consequence: degree and `deg(n − φ)` dropped) over an algebraically closed field; replaces T7 | av-b1; folded by leaf-fold5 | K |
| `poincareComplement : ZInQ.Contrib.AVB1.PoincareComplement` | LEAF | Poincaré's complement theorem (Milne 1986 Prop. 12.1; Mumford §19 Thm 1), weakened (`CharZero`, no closed-immersion clause); with the glue `SimpleImageIsogeny` replaces T8 | av-b1; folded by leaf-fold5 | K |
| `t10 : T10Etale.T10_TateDuality` | LEAF | T10, Tate duality | t10-etale | |
| `homLatticeCorr : HomUnify.HomLatticeCorr` | LEAF | analytic representation of homomorphisms (Birkenhake–Lange Prop. 1.2.1; Mumford §1, §3); also an input of Serre's lemma now | hom-unify | |
| `t11bExists : AVB2.T11bExists` | LEAF | T11(b) without uniqueness: homomorphisms `A_L → B_L` descend to `k` algebraically closed of char 0 (Conrad, Enseign. Math. 52 (2006) §3; Milne 1986 §20) | av-b2; folded by leaf-fold5 | |
| `t23 : ∀ p, PkgI4.T23_FontaineClosure p` | LEAF | T23, Fontaine | pkg-I4 | |
| `t24 : EigenformTwist` | LEAF | T24, twists of eigenforms | hdec-faithful | |
| `t27 : PkgI3.QMDichotomyYu` | LEAF | T27, Yu 2013 Thm 1.1 | pkg-I3; kernel Prop by leaf-fold5 | K |
| `t33 : LeafModCurves.JacobianExists ℚ` | LEAF | T33, Jacobians exist (Weil; Milne 1986 Thm 1.1, Prop. 6.1) | leaf-modcurves; kernel Prop by leaf-fold5 | K |
| `dimJacobianEqGenus : ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | LEAF? | `dim Jac X = genus` of the function field, for curves over `ℚ` (Milne 1986 Prop. 2.1 with Thm 1.1/Prop. 6.1; Serre duality, Hartshorne III.7.12; regular differentials, Hartshorne II.8): a composite of published results; first half of T34 | curves-g; folded by leaf-fold5 | K |
| `genusX1Field : ZInQ.Contrib.CurvesG.GenusX1Field` | LEAF? | the genus of `K_N` is the genus of `Γ₁(N)` (Shimura 1971 §6.7, Prop. 6.9, Prop. 1.40; invariance under `ℚ → ℂ`): composite; second half of T34 | curves-g; folded by leaf-fold5 | K |
| `t35 : ZInQ.LeafPush2.UniformizationExists` | LEAF | T35, `A(ℂ) ≅ ℂ^g/Λ` | leaf-push2; kernel Prop by leaf-fold5 | K |
| `normalModelOfFunctionFieldQ : ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ` | LEAF | (A) a normal proper integral model of dimension 1 of a finite extension of `ℚ(T)` (Stacks, Algebraic Curves, Tag 0BXX; Hartshorne I.6.7-6.9, II.6.7); part of T38 | curves-g; folded by leaf-fold5 | K |
| `normalCurveSmoothQ : ZInQ.Contrib.CurvesG.NormalCurveSmoothQ` | LEAF? | (B) a normal integral curve locally of finite type over `ℚ` is smooth of relative dimension 1 (Atiyah–Macdonald 9.2 + Stacks 00TV/0B8X): composite of two printed facts; part of T38 | curves-g; folded by leaf-fold5 | K |
| `geomConnectedOfConstantFieldQ : ZInQ.Contrib.CurvesG.GeomConnectedOfConstantFieldQ` | LEAF? | (C) a proper normal integral curve with constant field `ℚ` is geometrically connected (Stacks 0FD1; EGA III 4.3): composite; part of T38 (its rational-point clause is proved, `nonempty_ratPt_of_place`) | curves-g; folded by leaf-fold5 | K |
| `x0Transitive : ZInQ.RLeaf.X0Transitive` | LEAF | `X₀(N)` irreducible over `ℚ(j)` (Lang, *Elliptic functions* Ch. 5 §2 Thm 3; Cox Thm 11.18); gives T40 | t40-igusa, t40-clash | K |
| `neronSchemeExtensionExists : ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | LEAF | a smooth separated quasi-compact `𝓞_L`-scheme with generic fibre `A_L` to which maps from smooth schemes extend (BLR §1.4 Thm 3 with §1.2 Def. 1; no group law, no uniqueness asked); replaces T41 | neron-c; folded by leaf-fold5 | K |

### 2.3 `OpenAddedLeaves5` (21: 12 LEAF, 9 LEAF?)

| field | kind | content and source | last task |
|---|---|---|---|
| `cmOptimalEmbedding : FS5NoCM.CMOptimalEmbedding` | LEAF | CM points via optimal embeddings (Shimura 1967; Jordan; González–Rotger) | fs5-nocm |
| `thetaRatiosAlgebraic : ThetaPt.ThetaRatiosAlgebraic` | LEAF? | theta-constant ratios at a CM period matrix are algebraic (Shimura 1976; Mumford, Tata II) | g0-thetapoint |
| `qmHauptmodul : PkgI1.QMHauptmodul` | LEAF? | the theta-quotient Hauptmodul of `Γ*` | pkg-I1 |
| `qmClassNumberOne : FibreQM.QMClassNumberOne` | LEAF | Eichler class number one for `𝒪` | fibre-qm-period |
| `senTwist : G0Galois.SenTwist` | LEAF | Sen 1980 | g12-det |
| `finiteImageHT : G0Galois.FiniteImageHT` | LEAF | Tate 1967, Ax–Sen–Tate | g12-det |
| `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | LEAF | symmetric isogeny to a dual (Mumford §§6, 8, 20, 23); now also gives T9 | weil-pairing |
| `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | LEAF | Mumford §7-8; now also gives T9 | weil-pairing |
| `x6ConicModel : X6Kummer.X6ConicModel` | LEAF? | the conic model of `X₆` (Elkies 1998 §3; Kurihara 1979) | x6-kummer |
| `y3Connected : TSHecke.Y3Connected` | LEAF? | `Y₃` connected over `ℚ` (Shimura; Deligne, Bourbaki 389) | ts-hecke |
| `qmAutCard : HeckeRest.QMAutCard` | LEAF | `#Aut(A, ι) ∈ {4, 6, 2}` (Shimura; Rotger 2003) | hecke-rest |
| `alFixedPoints : HeckeRest.ALFixedPoints` | LEAF | fixed points of `w₂, w₃, w₆` (Ogg 1983; Rotger 2004) | hecke-rest |
| `zariskiConnectedness : ZariskiConn.ZariskiConnectedness` (K) | LEAF | Zariski's connectedness theorem (EGA III₁ 4.3.1, 4.3.4) | zariski-conn |
| `cmDescends : PeriodMapH.CMDescends` | LEAF? | CM QM surfaces over `ℂ` descend to `ℚ̄` (Shimura–Taniyama 1961; Shimura 1998 §12; flagged for a human check) | period-map |
| `gammaStarGen : PeriodGlue.GammaStarGen` | LEAF? | generators of `Γ*` (Takeuchi 1977, Elkies 1998 §3; Poincaré's polygon theorem) | period-glue |
| `valenceBoundGammaStar : PeriodMap.ValenceBoundGammaStar` | LEAF? | valence bound on `Γ*` (Shimura 1971 Thm 2.20) | period-map |
| `egaIV_8_8_2_ii` (K) | LEAF | EGA IV₃ 8.8.2 (ii) (Stacks 01ZM) | spread-out |
| `egaIV_8_10_5_xii` (K) | LEAF | EGA IV₃ 8.10.5 (xii) (Stacks 081F) | spread-out |
| `egaIV_17_7_8_ii` (K) | LEAF | EGA IV₄ 17.7.8 (ii) (Stacks 07RP) | spread-out |
| `shimuraGoodReduction : VertWitness.ShimuraGoodReduction` | LEAF? | for `p > 324`, a proper smooth curve `𝒴/ℤ_(p)` with a family `𝒜 : QMFamily 𝒴` of level-3 QM abelian surfaces, fibres at all characteristic-0 points, bijection on `ℚ̄`-points, Hecke automorphisms (twists, `𝒪^×`) over `ℤ_(p)`, and a `ℚ̄`-point (`IsShimuraModel`, eight clauses). Kottwitz, J. AMS 5 (1992) §5; Morita 1981; Carayol 1986; Buzzard 1997. LEAF? because which source states full level 3 at `3 ∣ D` literally is UNVERIFIED (vert-witness §3 caveat; needs a human check) | vert-witness; folded by leaf-fold5 |
| `curveBijIso : ModelGlue.CurveBijIso` | LEAF? | a morphism of proper smooth curves over `ℚ` bijective on `ℚ̄`-points is an isomorphism (quasi-finite + proper ⇒ finite, EGA III 4.4.2; degree 1 by generic étaleness, Hartshorne II.6.9, III.10.7; finite birational onto normal ⇒ iso): a composite of textbook results | model-glue; folded by leaf-fold5 |

Dropped since leaf-fold4: `serreRigidity3` (a theorem from `t35` and `homLatticeCorr`, av-b2).

### 2.4 `OpenGlue5` (2, GLUE)

| field | content | last task |
|---|---|---|
| `modelCoordinateResidue : ModelGlue.ModelCoordinateResidue` | on a model `(𝒴, 𝒜)` of `ShimuraGoodReduction` at `p > 324`, a coordinate `ρ : 𝒴 → P¹` over `ℤ_(p)` with R2fp's fibre relation on `ℚ̄`-points (`CoordFibres`), defined at every point whose stalk is a DVR with maximal ideal `(p)`, with residue transcendental over the prime field. Content: the tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}` (SGA 1 Exp. V; `p ∤ |Γ'|`) and the three CM sections staying disjoint mod `p`. Not proved: neither quotient schemes nor `P¹_{ℤ_(p)}` exist in Mathlib 4.35 (model-glue §2) | model-glue (replaces leaf-fold4's `HeckeVertWitness`) |
| `simpleImageIsogeny : ZInQ.Contrib.AVB1.SimpleImageIsogeny` (K) | a nonzero homomorphism out of a simple abelian variety (char 0) is an isogeny onto its image (image factorization + finite kernel; av-b1 §3.3). Not proved: scheme-theoretic images and kernels of group schemes are not available for the kernel's `AbVar` | av-b1 (with T8's replacement) |

## 3. The remaining leaves by the theory they come from

The 68 leaves (26 + 21 + 21) fall into nine groups (counts are of bundle fields).

| group (published theory) | # | fields |
|---|---|---|
| **A. Shimura curves with quaternionic multiplication** (Shimura 1967, 1971; Shimura–Taniyama; Deligne; Baba–Granath; González–Rotger; Rotger; Ogg; Elkies; Kurihara; Takeuchi; Eichler; Lin–Yang; Kottwitz, Morita, Carayol, Buzzard for good reduction) | 17 | `r1r2`, `r1b`, `r1rec`, `r3`, `r5`, `r5count`, `cmOptimalEmbedding`, `qmHauptmodul`, `qmClassNumberOne`, `x6ConicModel`, `y3Connected`, `qmAutCard`, `alFixedPoints`, `cmDescends`, `gammaStarGen`, `valenceBoundGammaStar`, `shimuraGoodReduction` |
| **A′. Theta functions and Siegel modular forms of genus 2** | 2 | `r4`, `thetaRatiosAlgebraic` |
| **B. Abelian varieties: the textbook theory** (Mumford; Birkenhake–Lange; Milne; Conrad; Yu 2013) | 12 | `t4`, `t5`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`, `homLatticeCorr`, `t11bExists`, `t27`, `t35`, `t09SymmIsogenyExists`, `isogenyQuasiInverse` |
| **C. Néron models, reduction and monodromy** (BLR; Serre–Tate; SGA 7; Raynaud) | 6 | `r6`, `r7a`, `r7b`, `r8`, `t3Surj`, `neronSchemeExtensionExists` |
| **C′. Scheme theory: limits and connectedness** (EGA III₁ 4.3; EGA IV 8.8, 8.10, 17.7) | 4 | `zariskiConnectedness`, `egaIV_8_8_2_ii`, `egaIV_8_10_5_xii`, `egaIV_17_7_8_ii` |
| **D. Faltings 1983 and Faltings heights** | 8 | `r9a`, `r9b`, `r18`, `r19`, `r20`, `r21`, `r22`, `h5fin` |
| **E. p-adic Hodge theory** | 6 | `r10`, `r11r12`, `r13`, `t23`, `senTwist`, `finiteImageHT` |
| **F. Galois representations of modular forms** | 5 | `r14`, `r15`, `r16`, `r17`, `t24` |
| **G. Algebraic and modular curves** (Jacobians; function fields and normal models; genus; `X₀(N)`; morphisms of curves) | 8 | `t33`, `dimJacobianEqGenus`, `genusX1Field`, `normalModelOfFunctionFieldQ`, `normalCurveSmoothQ`, `geomConnectedOfConstantFieldQ`, `x0Transitive`, `curveBijIso` |
| total | **68** | |

Plus the glue Props `ModelCoordinateResidue` (arithmetic geometry of the model of `Y₃`: tame quotients) and
`SimpleImageIsogeny` (group schemes: images and kernels). The grouping is a reading of the docstrings (SPECULATIVE in
its boundaries: `t4` could go under C, `curveBijIso` under C′, `shimuraGoodReduction` under C).

**LEAF? fields** (13): `dimJacobianEqGenus`, `genusX1Field`, `normalCurveSmoothQ`, `geomConnectedOfConstantFieldQ`,
`thetaRatiosAlgebraic`, `qmHauptmodul`, `x6ConicModel`, `y3Connected`, `cmDescends`, `gammaStarGen`,
`valenceBoundGammaStar`, `shimuraGoodReduction`, `curveBijIso`. **Flagged for a human check**: `ShimuraGoodReduction`
(level 3 at `3 ∣ D`, vert-witness §3), `CMDescends`, `ValenceBoundGammaStar`, `GammaStarGen` (period-glue §5).

## 4. Checks

**Kernel build** (`kernel_targets.txt`, one `lake build`, 23:40-23:49) plus `Contrib.AVB2.SerreLemma`.

**Olean chain** (`scratch/leaf-fold5/chain.sh`, one Lean process at a time; times in `log.md`): leaf-fold4's committed
sources `scratch/leaf-fold4/olean/{LPrefix,…,TailK}.lean` compiled unchanged (LPrefix 551 s … TailK 13 s, 0 errors
each), then `TailL` (part e10, 11 s), `TailM` (parts e20, e30, e40, 110 s), `TailN` (part e90, 5 s): 0 errors, no
`sorry`. All 28 `#print axioms` lines of TailM and TailN read `[propext, Classical.choice, Quot.sound]` (VERIFIED).

**Kernel conclusion and dependency closure** (`olean/Check5.lean`, 25 s; output without host paths in
`check5_result.txt`): `example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open5`
compiles. The closure has 184 142 constants. It contains `ZInQ.SmoothFibre.smoothFibreReduced`,
`ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`, `ZInQ.Contrib.AVB1.homFreeFinite_of_algClosed`,
`charPolyIndepOfEll_of_algClosed`, `poincareReducibility_of_simpleImage`,
`ZInQ.Contrib.CurvesG.curveOfFunctionFieldQ_of_split`, `nonempty_ratPt_of_place`, `dimJ1Genus_of_split`,
`ZInQ.Contrib.NeronC.neronMappingAbelianScheme_of_surj`, `neronMappingAbelianScheme_injective`,
`neronModelExists_of_extension`, `ZInQ.Contrib.AVB2.lattice_serre`, `HDec.AVB2.serreRigidity3_of_T35`,
`t9_of_leaves3`, `t11b_of_exists`, `HDec.ModelGlue.heckeVertWitness_of_curveBijIso`,
`HDec.VertWitness.heckeVertWitness_of_leaves`, `modelComparison_of_curveBijIso`, `modelCoordinate_of_residue`; it does
**not** contain `sorryAx`, av-b2's `divisiblePoints_of_posChar` or `MulIsogenyPosChar` (VERIFIED).

**Flat file** `scratch/leaf-fold5/Leaves5.lean` (FLAT_LINES lines, md5 FLAT_MD5…; leaf-fold4's `Leaves4.lean` with
the eight new kernel imports in its header and the three new bodies appended): FLAT_DETAIL

**Changes to the copied texts** (each in a script, with its reason):

| script | change | reason |
|---|---|---|
| `mk_e10.py` | vert-witness's `VertMain.lean.part` + model-glue's six parts, `#print`/`import` lines dropped, leaf-fold's `hdec` edits; `smoothFibreReduced'` and `isReduced_of_etale_of_isDomain'` := the kernel's theorems; `curveFacts` → `HSyn.curveFacts5`, `smoothStalkDimOne` → `HSyn.smoothStalkDimOne_proved` | (c); the kernel's curve facts are over the kernel's `ToP1`, not the chain's |
| `mk_e20.py` | av-b2's `AVB2Main.lean` from `namespace AVB2` to `end AVB2`, verbatim | av-b2 |
| `parts/e30_kernel.lean`, `e40_kernelfields.lean`, `e90_fold5.lean` | hand-written transports and bundles | §1.1 |

**No statement of a remaining leaf or glue Prop was changed.** Every field type is a source file's own definition.

## 5. Not folded, and why

- **The other 43 fields as kernel Props** (goal (c)). A probe (`olean/Probe6.lean`) found that none of the 23 chain
  Props with a kernel namesake is definitionally equal to it (all quantify over copied structures). Eleven were
  transported (part e40). Not done: `r1rec`, `r3`, `r5`, `r5count` (over the copied `QML3`, `QMPair`, `QMStr`
  structures), `r19`-`r22`, `h5fin` (Faltings heights: `stableFaltingsHeight` ranges over the copied `GroupModel`,
  so an equality of heights would need a bijection of model types), `r16`, `r17`, `r18` (modular-curve and
  Galois-representation structures; not attempted). The remaining fields have no kernel namesake in the build (the
  QM, period, Hecke, p-adic and Galois-representation layers live only in the scratch chain).
- **vert-witness's coarser forms** (`heckeVertWitness_of_goodReduction₃` etc.): not needed; the finest form is used.
  model-glue's `ModelCoordinateResidue` is unproved, so a glue Prop remains on the Hecke route.
- **av-b1's finer T8 split** (`ImageFactorization` + `SimpleSurjIsogeny`): one more glue Prop; `SimpleImageIsogeny`
  is the task's choice (§1.3).
- **curves-g's proposal `DimJ1LeSq`** (T34 weakened to `dim J₁(N) ≤ N²`, the only use): a proposal without a
  compiled replacement of the chain's consumers; not folded.
- **neron-c's mention of neron-lg** (N1 reduced to local leaves and two unproved glue Props): trades a leaf for glue.
- **homlattice** (`HomLatticeCorr` → `StrongUniformizationExists` + `GAGAMorphism`): as in leaf-fold4 §6, raises the
  count by one here.
- **t5-torsion's further options** and **kerwild-fix**, **frobchain-contrib**: as in leaf-fold4 §6.
