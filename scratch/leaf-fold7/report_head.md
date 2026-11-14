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

