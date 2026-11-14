# av-split (fleet summary)

**Result.** Five of the seven abelian-variety GLUE rows of frontier r3 are now theorems from five published-form
leaves, with no glue left; the other two cannot be split over Mathlib's definitions today. No row statement was
changed; none was found false, vacuous or stronger than its sources. Report: `docs/research/av-split.md`.

| row | leaves | proof |
|---|---|---|
| H-24 `PkgI2.ReductionTorsionBijective` (T4) | `MulEtaleAbelianScheme` (`[m]` étale on abelian schemes, `m` invertible) | `AvSplit.T4.reductionTorsionBijective_of_mulEtale` |
| H-25 `PkgI2.TorsionStructure` (T5) | `MumfordTorsionAlgClosed` (Mumford §4 App. 2 over `k = k̄`) | `AvSplit.torsionStructure_of_mumford` |
| H-38 `UniformizationExists` (T35) | kernel AN3 `UniformizationLeafAll` + the H-25 leaf | `AvSplit.Final.h38` |
| H-54 `IsogenyQuasiInverse` | `MilneIsogenyQuasiInverse` (morphism form) | `AvSplit.isogenyQuasiInverse_of_milne` |
| H-69 `HomLatticeCorr` | kernel AN3 + homlattice's `GAGAMorphism` | `AvSplit.HomLatticeAN3.homLatticeCorr_of_leaf_gaga` |
| H-53 `T09_SymmIsogenyExists` | — needs `Pic⁰`/dual abelian variety (not in Mathlib) | stays GLUE |
| H-78 `DimJacobianEqGenus` | — needs `Ω¹_X` / `K`-linear `H¹(X,𝒪_X)` (not in Mathlib) | stays GLUE |

Proved on the way (from Mathlib): Stacks 29.35.17 (unramified separated: maps agreeing at a point agree),
Stacks 04GG (1)⇒(8) via Mathlib's local structure of étale algebras, the scheme form of Hensel's lemma, valuation
rings of algebraically closed fields are henselian, `#(ℂ^g/Λ)[n] = n^{2g}`, `g = dim A` for AN3's uniformization,
base change of uniformizations and analytic homomorphisms along `σ : K → ℂ`.

**What compiles.** `scratch/av-split/AvSplitAll.lean` (concatenation of the component files, `build_all.py`):
0 errors, ~25 s; `AvSplit.Final.all_rows` and every theorem depend only on `propext`, `Classical.choice`,
`Quot.sound`. Component files `T4.lean`, `T5Isog.lean`, `T35.lean`, `T35AN3.lean`, `HomLatticeAN3.lean`
(contains homlattice's file verbatim) and the superseded `HomLattice.lean` each compile alone.

**What remains.** H-53, H-78 (missing Mathlib definitions); the leaf locators are UNVERIFIED (no network);
strict count effect if folded: 70 Props, 22 LEAF / 48 GLUE (from 17 / 53), to be checked by a fold. Two rows are
proved at universe 0 (the universe of all consumers).
