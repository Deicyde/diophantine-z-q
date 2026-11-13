
## Compile runs (`lake env lean scratch/g0-mod-galois/ModGalois.lean`, ~3m20s each)

- run1: failed at import (ZInQ olean missing); fixed by `lake build ZInQKernel.Hypotheses.JHeight
  ZInQKernel.Compiler.Precision.HeightConstant` (14 s, replay).
- run2: g11, g12 compile with axioms [propext, Classical.choice, Quot.sound]; g8 errors (h1
  argument, `AddCommMonoid (A.T ℓ)` instance), bundle missing `open PkgI4 (GaloisRep)`.
- run3: one error left in g8 (instance on `A.T ℓ`: needs `open ... MonObj` for the point group).
- run4: VERIFIED `G0Galois.g8`, `g11`, `g12`, `g8_g12`, `g8_g12_of_leaves` all depend on
  [propext, Classical.choice, Quot.sound] (no sorry). `commonConstituent_of_sides` had 2 errors
  (implicit arg of `ofInjective_apply`; `Subrepresentation (tate J 5)` vs
  `Subrepresentation (repBaseChange …)` mismatch). In run4 `G8Matrix` still had `A.dim = 2`;
  changed afterwards to `finrank (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` (true without T26 is not provable from
  `dim A = 2` alone; finrank is proved in g8 from T26).

## Statements (all in namespace `G0Galois`)

- Inputs: `G2Out K T`, `G3Out A ℓ T`, `G6Out A`, `G7Out A ℓ Tm c ε a β u`.
- Outputs: `G8Out A ℓ ρ r`, `G9Out r`, `G10Out r`, `G11Out T r`, `G12Out r₅`.
- Named glue: `G8Matrix`, `G9Glue`, `G10Glue`, `G12Weight`, `G12Det` (bundle `GaloisPieces`).
- Theorems: `g8`, `g11`, `finitelyRamified_of_g11`, `isIrreducible_of_g8`, `g12`, `g8_g11`,
  `g8_g12`, `g8_g12_of_leaves`, link `commonConstituent_of_sides` (with `JSide`).

## Findings

- Leaf gap (VERIFIED by reading `HSyn.EigenformRepExists`): R14 in consequence form omits
  `det ρ_g = ε_g χ^{k−1}`; G12's determinant argument needs it (`G12Det`); trace data at
  arithmetic Frobenius alone do not determine the determinant. Recommendation: add the published
  determinant clause to R14.
