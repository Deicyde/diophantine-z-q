# hdec-faithful log

## Step 1 (read sources)
- Read: HeightMin.lean, Height.lean (SixContactMin, SixContactEstimate, ratHeight, contactSet,
  contactSupport, heightH6), h-trust.md §§0-2 (36 steps A1-F4), prereq-survey.md, wk-h.md §§1-3.
- Next: read N5 L377-972 and appendix L10936-11005; JHeight.lean.

## Step 2 (read N5 and Mathlib grep)
- Read N5 L377-972 (proof of Thm 4.1) and L10936-11005 (lem:de-rham-descent); JHeight.lean
  (JHeightBound, sixContactMin_of_jHeightBound proved).
- Mathlib v4.35 (.lake/packages/mathlib) grep, VERIFIED:
  - present: group schemes over a field (`GrpObj` in `Over (Spec K)`; AlgebraicGeometry/Group/Abelian.lean:
    proper geom. integral group schemes are commutative), `Field.absoluteGaloisGroup`,
    `ValuationSubring.decompositionSubgroup/inertiaSubgroup` (RingTheory/Valuation/RamificationGroup),
    `AlgHom.IsArithFrobAt`, `arithFrobAt` (RingTheory/Frobenius), `NumberField.discr`,
    `CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k`, `qExpansion h f`, `BDeRhamPlus/BDeRham R p`
    (perfectoid; no Galois action, no filtration API).
  - absent: AbelianVariety, TateModule, Chebotarev, Kronecker–Weber, Brauer–Nesbitt, Skolem–Noether,
    Hilbert symbol, Hecke operators.

## Step 3 (Lean: cheap definitions + statable leaves), scratch/hdec-faithful/Defs0.lean
- Compiles with `lake env lean` (no errors), VERIFIED. Contents: Qbar, GQ (Krull topology),
  LiesOver (valuation subring of Qbar above p), IsArithFrob, GaloisRep ℓ n (continuous
  GQ →* GL_n(PadicAlgCl ℓ)), UnramifiedAt (Mathlib inertiaSubgroup), FrobTrace, IsComplexConj,
  IsOdd, IsIrreducible (Burnside form), IsSemisimple, CF N k (CuspForm on Gamma1 N), coeff (qExpansion 1),
  HasNebentypus, IsNormalizedEigenform (Hecke recursion on q-coefficients), AttachedTo.
- Leaves stated: FrobeniusDense (Chebotarev consequence), KroneckerWeber, SkolemNoether,
  HasseBrauerQ (CSA split at all p ⇒ split), BrauerNesbitt, DeligneSerreConseq.
- Pitfalls: `ι∞` is not an identifier (use ιC); slash notation needs `open scoped ModularForm`.

## Step 4 (leaf list fixed; drafting the note)
- Pan Thm 1.0.4 (arXiv v2, as recorded in h-a011 §1.1): hypotheses continuous, irreducible,
  finitely ramified, pst at p, odd; p odd; distinct HT weights; p=3 clause. Conclusion "comes from
  a cuspidal eigenform up to twist" is undefined in Pan's intro (risk: Lean reading must be fixed).
- Leaf list: L1-L35 with L11a-f (40 statements): 21 research-level, 19 textbook; 8 packages.
- Glue list: G0 (top) + G1-G20; G20 (F4) already proved in ZInQKernel/Hypotheses/JHeight.lean.

## Step 5 (Leaves.lean compiles)
- `lake build ZInQKernel.Hypotheses.JHeight` first (rebuilt ZInQ.NumericalTowerBounds,
  ZInQ.ExplicitCutoffBounds from the upstream `lean/` package; 5 s), then
  `lake env lean scratch/hdec-faithful/Leaves.lean`: no errors, 36 `sorry` warnings
  (35 placeholder leaves + `jHeightBound_of_leaves`), VERIFIED.
- Stated (concrete): SkolemNoether, HasseBrauerQ, KroneckerWeber, FrobeniusDense, BrauerNesbitt,
  EigenformRepExists, DeligneSerreConseq, EigenformTwist (8 statements).
- Proved glue: `weight_match` (G12 weight arithmetic), `prod_primes_pow_le` (G16), axioms
  propext, Classical.choice, Quot.sound. `sixContactMin_of_leaves` routes through the proved
  `ZInQ.JHeight.sixContactMin_of_jHeightBound` (G20).
- Defs0.lean removed (superseded by Leaves.lean §0-§1).
- Note fix needed: statement count is 40 leaves = 43 statements when L15, L27, L28 are split;
  placeholders 35, stated 8.
