# pkg-I2 results log

Task: package I2 (reduction theory; steps A5, A6, A8, C6, C10, D2 of docs/research/h-trust.md).
Marks: VERIFIED (read in a source, computed, compiled), STANDARD (published, reference given),
SPECULATIVE. Locators from memory are UNVERIFIED.

## Step 1 (2026-11-11): Mathlib inventory and first draft

Mathlib v4.35.0 objects used (VERIFIED by grep of .lake/packages/mathlib):
- `IsRegularLocalRing` (RingTheory/RegularLocalRing/Defs.lean, Stacks 00KU)
- `Algebra.IsEtaleAt`, `Algebra.IsUnramifiedAt`, `Algebra.QuasiFiniteAt` (RingTheory/Etale/Locus,
  Unramified/Locus, QuasiFinite/Basic)
- `ValuationSubring.decompositionSubgroup`, `.inertiaSubgroup` (RingTheory/Valuation/RamificationGroup)
- `Grp (Over X)`, `GrpObj`, `MonObj.Hom.group` (scoped instance: group law on `X ⟶ G`)
- `CartesianMonoidalCategory (Over S)` for schemes (AlgebraicGeometry/Pullbacks.lean:709)
- `(Over.pullback f).mapGrp` (base change of group objects; Monoidal/Cartesian/Over.lean:198,305)
- `IsProper`, `Smooth`, `GeometricallyIntegral`, `GeometricallyConnected` (morphism classes)
- `isCommMonObj_of_isProper_of_geometricallyIntegral` (proper geometrically integral group scheme
  over a field is commutative; Group/Abelian.lean:133)
Absent (VERIFIED by grep): Néron models, Tate modules, semistable reduction, strict henselization.

Draft scratch/pkg-I2/I2.lean, first version: defs `specOver`, `IsAbelianVariety`, `IsAbelianScheme`,
`Pts`, `torsion`, `galHom`, `galAct`, `IsInertia`, `HasGoodReduction`, `InertiaTrivialOn`, `UnipSq`;
leaves `PurityBranchLocus` (Stacks 0BMB ring form), `NeronOggShafarevich` (Serre–Tate Thm 1).
Compile: `lake env lean scratch/pkg-I2/I2.lean`: no errors, no warnings, 40 s (VERIFIED).
