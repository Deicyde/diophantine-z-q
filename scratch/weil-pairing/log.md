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
- §7 COMPILES: `wv` (non-dependent e^λ_n on A(K̄)), `wv_eq/pow/one/add_left/add_right/
  nsmul_left/nsmul_right/compat/galois`; `TMu K ℓ = T_ℓ(μ)` (Objects' `Tate.T` of K̄ˣ), `galTMu`;
  `tatePairing D lam hℓ : T_ℓ A →ₗ[ℤ_ℓ] T_ℓ A →ₗ[ℤ_ℓ] T_ℓ(μ)` (the ℓ-adic Weil pairing,
  components e^λ_{ℓ^k}(x_k, y_k)); `tatePairing_self` (alternating), `tatePairing_galois`,
  `galTMu_eq_cyclotomic` (Mathlib `cyclotomicCharacter`), `tatePairing_cyclotomic`:
  E^λ(σx, σy) = χ_ℓ(σ)·E^λ(x, y) — the ℓ-adic G12/C8-item-1 input, PROVED from a `WeilDual`.
- 23:35 §8-§9 COMPILE (axioms standard): `iterate_smul`, `eq_zero_of_coprime`, leaf
  `DivisiblePoints`, `rootSeq`, `tate_surj` (T_ℓ M → M[ℓ^k] onto for ℓ-divisible M),
  `tatePairing_left_ker` (E^λ has trivial left kernel given λψ = [d] and surjectivity),
  `det_sq_of_similitude_domain`, `det_galRep_sq` (det ρ_ℓ(σ)² = χ_ℓ(σ)^{rank T_ℓ A} on V_ℓ A),
  `units_divisible`, `exists_tmu_gen` (compatible ζ_n of exact order ℓ^n), `exists_dlog`, `dlog`,
  `tmuCoord`, `tmuCoordLin` (T_ℓ(μ) →ₗ ℤ_ℓ), `tmuCoordLin_injective`; glue target
  `G12_DetInput` and `g12_detInput_of_leaves : T09_SymmIsogenyExists → IsogenyQuasiInverse →
  PkgI3.TateModuleFree → DivisiblePoints → G12_DetInput` (PROVED).
- §10 COMPILES: `polarization_zero` (T9⁺ holds at A = 0), `weil_ne_zero_of`.
