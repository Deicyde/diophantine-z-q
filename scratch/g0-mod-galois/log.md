
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
  changed afterwards to `finrank (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4`: with `dim A = 2` alone it is true but not
  provable without T26; the finrank is proved in g8 from T26.

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
- run5: link lemma: one rewrite failure left (second `keyA`, subtype membership form).
- run6: resQ redefined as `res (qEmb K)` (copied `exists_res`, `res` from scratch/e1-sub) so that
  `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (`resQ_spec`, `eq_resQ`); added the copied g0-mod-newform
  interface (`NF.toRep`, `NF.PanOutput`, `NF.IsConstituentOf`, `NF.ModData`, `NF.G12Spec`,
  `NF.NewformG12Out`), `FiniteCharDirichlet`, `isConstituentOf_of_intertwines`, `panOutput_of_g12`,
  `newformG12Out_of_galois`. Errors: `τ` not coerced (type ascription), `GaloisChar` not opened,
  noncomputable section missing.
- run7 (2m49s): VERIFIED 0 errors, 0 `declaration uses sorry`; axioms [propext, Classical.choice,
  Quot.sound] for g8, g11, g12, g8_g12, g8_g12_of_leaves, commonConstituent_of_sides,
  isConstituentOf_of_intertwines, newformG12Out_of_galois.

## Partner interfaces (read from origin refs, 02:15)

- g0-mod-newform (217e17f0) input `G12Out A := ∃ D : ModData L A, G12Spec D`; copied verbatim as
  `G0Galois.NF.*`; proved by `newformG12Out_of_galois`.
- g0-mod-field (ceada656) output `G7Data` (points-level descent datum, complex scalars, `L'` as an
  IntermediateField); the ℓ-adic realization into `G7Out` is the named step `G7Realize`, stated in
  prose only (different environment: partners import ZInQKernel/HDecomp, leaves live in Split.lean).
- TestMatrix (prefix of Split.lean to line 7776 + objects + part_matrix.lean; 1m09s): VERIFIED
  `g8Matrix_of_burnside : BurnsideAbsIrred → G8Matrix` compiles (after replacing `exact` by
  `rw [LinearMap.toMatrix_mulVec_repr]; rfl` in the intertwining).
- run8 (2m34s): full file with part_matrix.lean; `GaloisPieces.burnside : BurnsideAbsIrred` in
  place of `G8Matrix`. VERIFIED 0 errors, 0 sorry; axioms standard for g8, g8Matrix_of_burnside,
  g11, g12, g8_g12, g8_g12_of_leaves, commonConstituent_of_sides, isConstituentOf_of_intertwines,
  newformG12Out_of_galois.
