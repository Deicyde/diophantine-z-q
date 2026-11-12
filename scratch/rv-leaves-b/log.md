# rv-leaves-b results log

## Step 1. Read leaves (VERIFIED by reading)
- scratch/pkg-I2/I2.lean (476 l.), scratch/pkg-I3/I3.lean (694 l.), scratch/pkg-I6/I6.lean (492 l.),
  scratch/glue-conductor/{Breaks,Dyadic,Level}.lean.
- Mathlib facts checked in .lake/packages/mathlib (VERIFIED):
  - `ZMod N` topology is `⊥` (discrete): Topology/Instances/ZMod.lean:24. So I6's continuity
    conditions on cochains are genuine (not vacuous).
  - `ℍ[R, a, b] = QuaternionAlgebra R a 0 b` (Algebra/Quaternion.lean:83): i² = a, j² = b.
  - `continuousCohomology` (RepresentationTheory/Homological/ContCohomology/Basic.lean:131) is the
    homology of G-invariant iterated C(G, C(G, …, M)) (homogeneous continuous cochains); the
    comparison with inhomogeneous cochains C(Gⁿ, M) is a TODO in Mathlib (file header).
  - No Skolem–Noether in Mathlib (grep "Skolem": only model theory / tactic hits).

## Step 2. scratch/rv-leaves-b/Repairs.lean — COMPILES, no sorry, no warnings (VERIFIED,
`lake env lean`, 31 s, 2026-11-11)
- I3 definitions (I3.lean lines 1-374, verbatim) + I2's `IsAbelianVariety` class (verbatim).
- `RvLeavesB.ofGrp`: I2 abelian variety (Grp object + IsAbelianVariety) ↦ I3 `AbVar`, same X.
- `RvLeavesB.homOfGrp`, `homOfGrp_hom`: Grp morphism ↦ I3 `Hom`, same underlying morphism (rfl).
- `RvLeavesB.QMDichotomyIndef`: I3.Q with hypothesis `0 < a` (indefinite B); OPTIONAL weakening.
  Recompiled after docstring edit: no errors (VERIFIED).
- Retracted finding: "definite B needs Shimura" is WRONG; simple A has [D:ℚ] | 4 so End⁰ = B, allowed
  by the conclusion. QMDichotomy is true from Mumford §19/§21 + Silverman III.9.4.

## Verdicts (details in docs/research/rv-leaves-b.md)
- FAITHFUL: I2-P, I2-NOS, I2-ST2, I2-SS, I2-Ray, I2-NMP, I2-Red, I2-Tors, I2-AbDVR, I2-Char,
  I2-Rank; I3.F1, F2, M0, M1, M2; I6.1, 2a-c, 2a′-c′, 3, 4, 5, 6, 7, 8, 9, 10;
  glue-conductor HilbertDifferentFormula, SerreDifferentBound.
- FAITHFUL AFTER REPAIRS (citation only): I3.Q (composite of Mumford §19 Thm 1, Cor 2, §21 and
  Silverman III.9.4; no single locator);
  I3.M3 (PoincareReducibility: true, but over non-closed k cite the k-rational form, not
  Mumford §19 Thm 1 which is over k̄).
- None STRONGER THAN PUBLISHED, VACUOUS or WRONG found.
- Glue with sorry (not leaves): I2 goodReduction_of_QM_rational3 (A6), I6 artinConductor_le_of_upper
  (D4), I6 sq_principalUnits (D3; proved in glue-conductor/Dyadic.lean).

## Step 3. Report docs/research/rv-leaves-b.md written (35 leaves, verdict table)
