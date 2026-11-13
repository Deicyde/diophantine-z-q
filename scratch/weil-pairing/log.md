# weil-pairing results log

- 23:05 start. `lake build ZInQKernel.HDecomp.Objects`: OK (50 s).
- WeilPairing.lean §1-§2 (torsion `tors A n`, `Mu K n = μ_n(K̄)`, `galTors`, `galMu`, `torsMap`,
  `Pairing A B n := tors A n →+ tors B n →+ Mu K n`, `IsPerfect`, `IsAlternating`,
  `IsGalEquivariant`, `pull`; lemmas `add_left/right`, `val_mul_left/right`, `nsmul_left/right`,
  `val_pow_eq_one`, `IsAlternating.skew`, `IsAlternating.pull`, `IsGalEquivariant.pull`,
  `.pull_hom`, `homP_galP`, `torsMap_galTors`, `IsPerfect.left_trivial`, `isPerfect_zero_iff`):
  COMPILES (lake env lean, 5 s, no errors).
- 23:50 §3-§4 COMPILE: `comp`, `homP_comp`, `torsMap_comp`, `WeilDual` (structure: dual, e_n,
  perfect, galois, compat), `IsDualHom`, `IsDualHom.unique`, `IsDualHom.comp`, `weil`
  (e^λ_n(x,y) = e_n(x, λy)), `weil_galois`, `IsSymmetric`, `SymmIsogeny`, `IsQuasiInverse`,
  `RosatiPositive`, `Polarization`, `SymmIsogeny.IsPrincipal`, `weil_nondeg`,
  `weil_perfect_of_principal`, `isSymmetric_pullback`, `weil_pullback`; leaves
  `T09_SymmIsogenyExists`, `T09plus_PolarizationExists`, `IsogenyQuasiInverse`; non-vacuity
  `weilDualZero`, `symmIsogeny_zero` (T9 holds at A = 0), `tors_zero_eq`.
- FINDING: `WeilDual` is not unique (over K̄ any Â with Â[n] ≅ A[n] carries one); leaves over it
  must be existential. A leaf "∀ D D' f, ∃ dual morphism" would NOT be a consequence (SPECULATIVE
  counterexample over K̄: non-isogenous Â' of the same dimension). Not stated.
- 23:23 §5-§6 COMPILE, axioms [propext, Classical.choice, Quot.sound] for all printed:
  `OldT9.T09_WeilPairing` (verbatim copy of `LeafPush.T09_WeilPairing`, universe 0);
  `oldT9_of_symmIsogeny : T09_SymmIsogenyExists → IsogenyQuasiInverse → OldT9.T09_WeilPairing`
  (VERIFIED, compiled: the new T9 implies the old consequence form, all six clauses);
  `galMu_eq_nsmul`, `weil_cyclotomic` (e^λ_n(σx,σy) = χ_n(σ)·e^λ_n(x,y), Mathlib's
  `modularCyclotomicCharacter'`); `det_sq_of_similitude` (comm. ring, unit Gram det:
  det(f)² = c^rank), `det_sq_of_similitude_field`; `twist_finite_four` (C8 determinant argument
  from (det r)⁴ = χ⁴ on a finite-index subgroup).
