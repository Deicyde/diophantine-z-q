# g0-assemble3 (fleet summary)

**Result (VERIFIED).** `HSyn.sixContactMin_of_leaves4 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces4) :
ZInQ.SixContactMin` compiles in `scratch/g0-assemble3/G0Assemble3.lean` (90 509 lines). `lake env lean` exits 0 in 966 s
with 0 errors and no `sorry`, and all 220 `#print axioms` reports are `[propext, Classical.choice, Quot.sound]`. It also
compiles over the olean chain `LPrefix → TailA → TailB → TailC → TailE → TailF → TailD`. Report:
`docs/research/g0-assemble3.md`.

**GluePieces4: 46 fields = 14 LEAF + 3 LEAF? + 29 GLUE** (g0-assemble2's `GluePieces3` had 40 = 15 + 3 + 22).
- **14 fields proved outright:** `mulEtale`, `smoothStalkDimOne`, `constOrOntoAlgClosed`, `ratFactorAlgClosed`,
  `productUnifSplits`, `cotangentSpanBC`, `uniformizationLiftAnalytic`, `unramifiedConjugates`, `oMaximal`,
  `endTransport`, `burnsideAbsIrred`, `g9AbVarBaseChange`, `artinTorsionSurj`, `conjUniformization`. The sources are
  infra-stalks, image-plane/infra-smooth-dim, unif-dims/product-unif, inner-twist, kf-glue, rv-gluepieces2, g9-abvarbc
  and conj-twist.
- **`g9R10Weights` moved into R10:** `ResearchLeaves4.r10 : DeRhamComparisonHT` (r10-amend), which is old R10 plus that
  clause.
- **9 fields replaced by smaller named Props:** `x6KummerFibre` (by the leaf `X6ConicModel`),
  `productMetrizationOfProductUnif` (by the leaf `AnalyticUniformizationOfDim`), `periodMapGlue`, `hauptmodulUnique`,
  `qmDenZeroCM3` (period-map), `propTSAll` (prop-ts-glue's 14 Props), `conjIsogMaps` (`TwistDescent`), and `modelG3`
  and `linkedTateLocal` (linked-tate: `GoodRedTorsion`, `QMEndRank`, `LinkedFrob`, `KernelFieldBreaks`,
  `TateRamAtThree`).
- The count rises only because two big Props split into many small ones.

**Fixes.**
- `G0ModField.G7Data` now carries `Module.finrank ℚ L ≤ heightD`. Every use was checked; four `.2^11` projections were
  adjusted.
- Name collision: linked-tate's `GluePieces3` is now `HSyn.LinkedTate.GluePieces3`. `HSyn.GluePieces3` is
  g0-assemble2's. rv-gluepieces2's 15-field bundle is not copied.

**Not folded.** g8-object, alg-frob-red and local-glue are alternatives on the old `LinkedTateLocal` route and would
need bridges. r1b-state is a variant statement. cm-points is on the CR3 side. conj-pieces turns the leaf
`HomLinearLift` into the leaf `HoloHomLift`.

**What remains.**
- The 29 glue Props, by area:
  - period-map: 6;
  - prop-ts-glue: 14;
  - height-bc: 2;
  - `cPtsTransport`;
  - `twistDescent`;
  - linked-tate: 5.
- SPECULATIVE truth: `heckeIrreducible`, `twistDescent`, `linkedFrob`.
- The assembly still uses g0-assemble2's root-namespace `Leaves.lean`. Porting it to the current `namespace HDec`
  version has not been done.
