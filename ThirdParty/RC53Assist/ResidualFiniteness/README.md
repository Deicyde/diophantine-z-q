# Residual finiteness of the stage Selmer complexes

`StageResidual.lean` supplies the arithmetic input `ResidualCohomologyFinite` of
`InnerLimitArith/StageInputs.lean` (the finiteness hypothesis of the finite free model of the
retained inner-limit lemma, manuscript lines 4391–4414) for the actual stage Selmer complexes at
`A_i = (ℤ/2^i)[t]/t^i`. The only inputs beyond the data are the finiteness prints
`MilneLocalFiniteness` and `MilneGlobalFiniteness` (Milne, *Arithmetic duality theorems*, I, Theorem 2.1 and
Corollary 4.15), already used by `stageSelmerCohomologyFinite`.

## Route

1. Base change of continuous cochains with discrete coefficients: for a compact group `G`, an
   `A`-algebra `B` and a discrete `A`-module `N`, `B ⊗_A C^n_cont(G, N) ≅ C^n_cont(G, B ⊗_A N)`,
   `b ⊗ f ↦ (x ↦ b ⊗ f(x))`, compatibly with the differentials and with restriction
   (`cochainBaseChangeEquivOf`, `cochainBaseChangeEquivOf_comm`, `natCochainsBaseChangeIso`,
   `natBaseChangeF_res`). A locally constant function on the compact space `G^n` factors through a
   finite discrete quotient, on which tensoring commutes with the finite power (`lcTensorEquiv`).
2. Through the Selmer cone and the local conditions: `B ⊗_A C_U(G_{K,S}, M)` is the Selmer complex
   of the base-changed module `B ⊗_A M` with the local conditions
   `B ⊗_A U_v → C^•_cont(G_v, B ⊗_A M)` (`residualConditions`, `residualSelmerIso`,
   `residualGaloisSelmerIso`).
3. Finiteness: for `B` the residue field `k`, `k ⊗_A M` is a finite discrete module whose order
   divides `#M`, and `galoisSelmerCohomologyFinite_of_prints` applies to it
   (`galoisSelmer_residualCohomologyFinite`).

## Results for the actual stage complexes (no input beyond the prints and the data)

* `stageStrictSelmer_residualCohomologyFinite`: `selCx (actualSelData_zero W i α)` (zero
  conditions).
* `stageRelaxedSelmer_residualCohomologyFinite`: `selCx (actualSelData_full W i α)` (full
  conditions).
* `stageKummerSelmer_residualCohomologyFinite`: the Kummer conditions
  (`kummerGaloisLocalConditions`) at every place of `S`.
* `actualStageSelmer_full_residualCohomologyFinite`,
  `actualStageSelmer_zero_residualCohomologyFinite`: `selCx (actualSelData hS W i α c)` with full
  (respectively zero) conditions at the old places `S₀` and the unramified conditions at `S − S₀`.

## Results with an explicit local input

* `stageSelmer_residualCohomologyFinite`: any local conditions `Δ` for `M_i`, given
  `∀ v, ResidualCohomologyFinite (Δ.U v)`.
* `actualStageSelmer_residualCohomologyFinite`: any old conditions `c` at `S₀`, given their residual
  finiteness; the unramified conditions at `S − S₀` are discharged.
* The local input is discharged by `residualCohomologyFinite_zeroCx` (zero condition),
  `localCx_residualCohomologyFinite` (full condition), `urAt_residualCohomologyFinite` (unramified
  condition), `residualCohomologyFinite_cocycleCondition` (cocycle conditions, among them the
  Kummer conditions, given finiteness of `H¹(G_v, M)`) and `residualCohomologyFinite_of_finite_X`
  (any condition complex with finite terms).

All conclusions have the shape `ResidualCohomologyFinite (selCx …)` over `Acoef i`, which is the
ring `StageA i` of the stage complexes `G i` of the inner-limit producer (the same quotient
`(ℤ/2^i)[X]/(X^i)`).

## Not covered

* Residual finiteness of other local conditions (for instance the orthogonal complements) is an
  explicit hypothesis of the general statements.
* The remaining hypotheses of the inner-limit producer (flatness of the stage complexes, bounded
  residual cohomology and a uniform bound on the residual ranks) are not addressed here;
  `residualGaloisSelmerIso` identifies the residual complex with the Selmer complex of the residual
  module `k ⊗_{A_i} M_i`, the natural starting point for such bounds.
