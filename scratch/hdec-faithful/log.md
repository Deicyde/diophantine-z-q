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
