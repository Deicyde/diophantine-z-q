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

## Step 2: abelian-variety leaves and Abhyankar (DVR) compile

Added to scratch/pkg-I2/I2.lean: `baseChange`, `toW`, `IsReductionOf`; leaves
`SerreTatePotentialGood` (Serre–Tate Thm 2), `GrothendieckMonodromy` (SGA 7 IX 3.6 + 3.5 ⇒),
`RaynaudCriterion` (SGA 7 IX 4.7 + 3.5 ⇒), `NeronMappingAbelianScheme` (BLR 1.2 Prop 8),
`ReductionTorsionBijective` (Serre–Tate §1), `TorsionStructure` (Mumford §4),
`AbhyankarDVR` (SGA 1 X 3.6 / Stichtenoth 3.9.1).
API facts found while compiling (VERIFIED): a morphism of `Grp C` has underlying `C`-morphism
`f.hom.hom` (Grp → Mon → C); `Ideal.ramificationIdx` is now the length definition
(`q.ramificationIdx R`), the older one is `ramificationIdx'`.
Compile: no errors, no warnings (VERIFIED).

Finding (SPECULATIVE until written as glue, argument below): A6 (good reduction at v ∤ 3) follows
from Raynaud (m = 3), NOS (c) with m = 3ⁿ, TorsionStructure and the 𝒪-action, using that
B ⊗ ℚ₃ is a division algebra: N = σ − 1 commutes with 𝒪₃, N² = 0, A[3ⁿ] free of rank one over
𝒪/3ⁿ ⇒ N = right multiplication by c with c² ≡ 0 mod 3ⁿ ⇒ N kills A[3^k] for n = 2k. This route
does not use SGA 7 IX 3.6, the toric-part/Néron argument (Morita), Serre–Tate Thm 2, or the
torsion-freeness of 1 + 3M₄(ℤ₃).

## Step 3: Mumford §19 Thm 4 leaf; glue proved from leaves

Added: leaf `CharpolyIndependentOfEll` (Mumford §19 Thm 4, finite-level form); lemmas
`galAct_mul/inv/pow/one` (from Mathlib `MonObj.comp_mul`, `GrpObj.comp_inv`, `MonObj.comp_pow`,
`MonObj.comp_one`); glue theorems
- `inertiaTrivial_of_goodReduction` (C6/A8: good reduction ⇒ inertia trivial on A[ℓⁿ]) from NOS: PROVED;
- `fixed_of_unipSq_of_iterate` (algebraic core of D2): PROVED;
- `D2_fixed_of_raynaud` (D2: inertia element of p-power order on x ∈ A[ℓⁿ] fixes x) from Raynaud: PROVED;
- `goodReduction_of_QM_rational3` (A6 via Raynaud + NOS + TorsionStructure; QM given as K-endomorphisms
  I, J with I² = 2, J² = -3, IJ = -JI on K̄-points): statement compiles, body `sorry`, outline in docstring.
Compile: only warning "declaration uses sorry" at goodReduction_of_QM_rational3 (VERIFIED).
`#print axioms` (VERIFIED): the three proved glue theorems use [propext, Classical.choice, Quot.sound];
goodReduction_of_QM_rational3 adds sorryAx.
API notes: `CategoryTheory.Hom.commGroup` is a scoped instance (MonObj) found automatically once
`IsCommMonObj A.X` is in context; `pow_gcd_eq_one` is an iff in this Mathlib.

## Step 4: report

docs/research/pkg-I2.md written: per input the published statement, the leaf, Lean objects, use in
A5/A6/A8/C6/C10/D2; glue status; the Raynaud route for A6 (SPECULATIVE, argument in §4.2);
𝕎(𝔽̄_p) in place of ℤ_(p)^sh for Prop. TS (Mathlib: `WittVector.isDiscreteValuationRing`,
`isAdicCompleteIdealSpanP`, VERIFIED by grep); correction of wk-h §3.2 row I2 (statable: yes).
Mathlib absences checked by grep (VERIFIED): no `IsCohenMacaulay`/miracle flatness, no strict
henselization (only `HenselianLocalRing`), no Néron models or Tate modules.
Final leaf count: 11 (`PurityBranchLocus`, `AbhyankarDVR`, `NeronOggShafarevich`,
`SerreTatePotentialGood`, `GrothendieckMonodromy`, `RaynaudCriterion`, `NeronMappingAbelianScheme`,
`ReductionTorsionBijective`, `TorsionStructure`, `CharpolyIndependentOfEll`, `HomRankBound`).
Last compile of scratch/pkg-I2/I2.lean: one warning (sorry in goodReduction_of_QM_rational3), no errors.
Not done: non-vacuity instance (trivial group as IsAbelianVariety) — not attempted in Lean.
