
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
- run9-10: part_det.lean: `R14Det` (R14 with its published determinant clause, a leaf), `DetTate`
  (glue from T9), `ResQFiniteIndex` (glue), `FrobeniusDenseQ` (= the bundle's T18, `frobeniusDenseQ_of`
  by defeq), copied `eq_of_eq_on_arithFrob` (c9-rhof), `det_fin_two_eq_trace`, and
  `g12Det_of : R14Det → DetTate → ResQFiniteIndex → FrobeniusDenseQ → G12Det`. run10 VERIFIED:
  `g12Det_of` axioms standard.
- run11 (2m31s): `GaloisPieces` = {burnside, r14det, deRham, odd, weight, detTate, finIndex}; the
  bundle theorems use `g8Matrix_of_burnside` and `g12Det_of`. VERIFIED 0 errors, 0 sorry, all ten
  G0Galois theorems on [propext, Classical.choice, Quot.sound].
- Finding (02:55): g0-mod-field (origin 9f698815) copied `resQ`, `Vb`, `tate`, `G2Out`, `G7Out` from
  this branch at 20fa1287 (`G0ModField.GaloisCopy`), proved `ResQRange` for the Mathlib-map `resQ`
  and the bridge `galoisG2Out_of_g7Data`, and stated `TateBridge` (their `G7Data` → this `G7Out`).
  My run6 redefinition `resQ := res (qEmb K)` broke that match, so `resQ` is restored to
  `Field.absoluteGaloisGroup.map (algebraMap ℚ K)`. `qEmbRing K` is the `IsAlgClosed.lift` that
  `map` chooses, and `resQ_spec` (`qEmbRing K (resQ K τ x) = τ (qEmbRing K x)`) is proved by unfolding
  `map` (`AlgEquiv.restrictNormal_commutes`). Test file /tmp/g0mg/TestRes.lean (import Mathlib, 8 s):
  0 errors. A script check finds the five definitions identical, token for token, to their copies.
- run12 (2m30s): VERIFIED 0 errors, 0 sorry; all eleven G0Galois theorems on standard axioms.
- Model review (subagent, read-only, no Lean): all nine named Props and four inputs judged TRUE and
  non-vacuous. Docstring defects D1 (`Tm σ = μ_σ∘σ`, not `a_σ μ_σ∘σ`), D2 (G10 argument), D3 (Sen
  weights), D4, D5 repaired.
- run13 (2m33s): after the docstring repairs. VERIFIED 0 errors, 0 sorry; ten G0Galois theorems on
  standard axioms.
