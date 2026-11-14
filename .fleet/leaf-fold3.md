# leaf-fold3 (2026-11-13)

**Result.** `HDec.HSyn.sixContactMin_of_open3 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves3)
(l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin` (the kernel's own `ZInQ.SixContactMin`),
no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`. Hypotheses: 68 named Props =
26 research leaves + 20 textbook + 16 added (11 LEAF, 5 LEAF?) + **6 glue** (leaf-fold2: 66 with 9 glue,
2 of them SPECULATIVE; now 0 SPECULATIVE glue).

**Folded.** Closed: `hodgeBCInjective`, `omegaBaseChange` (hodge-bc2), `cPtsTransport` (cpts-transport),
`conjIsogMaps` (twist-descent; its `MulIsogeny` is g9-abvarbc's proved Prop), `modelG3` (linked-tate +
lt-goodred's `GoodRedTorsion`), `burnsideAbsIrred` (Mathlib). `HomLatticeCorr` replaces T11(a) and
`HomLinearLift` (hom-unify). `propTSAll` → hecke-rest's inputs (prop-ts-glue, kummer-comp, ts-kummer
merged): leaves `Y3Connected`, `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`; glue `ChartProper`,
`ChartQuasiFinite`, `HeckeVertWitness`. `linkedTateLocal` → lt-local's ℓ = 5, 3 route (UnramRoots proved,
TateBridge35 via frob-pieces): glue N1-g1 `AbVarSpreadsOut`, leaf `ProperSmoothGenConnected`, textbook
T3/T4 back. lg-kerwild's every-ℓ theorem is not used; `[L:ℚ] ≤ D` is in `G7Data` (g0-assemble3's fix);
ε = 1 comes from the descent datum. Mobius and TangentDim imported from Contrib. Issue #2 items 2, 5, 8 done.

**Compiles.** Olean chain LPrefix → TailA-I (scratch/leaf-fold3/chain.sh): all 0 errors. Flat file Leaves3.lean (110 826 lines): exit 0 in 1042 s, 0 errors, 288 axiom reports all standard; dependency closure contains no `sorryAx` and not lg-kerwild's every-ℓ theorem.

**Remains.** 6 glue: `periodMapGlue`, `hauptmodulUnique` (period-map's reductions not folded: they add
fields), `ChartProper`, `ChartQuasiFinite`, `HeckeVertWitness`, `AbVarSpreadsOut`. T40 stays a leaf:
`Contrib/RLeaf/T40.lean` (T40 from `X0Transitive`) cannot be imported next to the chain's Tau Ceti modules
(duplicate `Units.val_mul_zpow_natCast_mul` from Tau Ceti's Backport copy). Leaves grouped by theory in
docs/research/leaf-fold3.md §3 (Shimura QM curves 14, theta/Siegel 2, abelian varieties 16, Néron models 7, Faltings/heights
8, p-adic Hodge 6, modular Galois reps 5, curves 4). h-decomposition §3 corrections:
scratch/leaf-fold3/h-decomposition-section3.patch.
