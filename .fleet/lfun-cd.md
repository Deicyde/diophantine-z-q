# lfun-cd: Mathlib's L-series of C_d, computed in Lean

**What is proved** (new file `ZInQKernel/RouteK/Rank/LFunctionCd.lean`, namespace
`ZInQ.Literature`). The file has no sorry and no axiom. It covers odd squarefree `d`, which
includes every `d ≡ 5 (mod 8)` in the CR3 Props. `v` is a place of `ℚ` and `p = natGenerator v`.

1. **Local results** (task item 1).
   - `isMinimal_cdLocal`: the model `y² = x³ − d²x` is minimal over the completion at every `p`.
     The reason is `Δ = (2d)^6 ∉ 𝔪^12`, through a generic DVR lemma
     `isMinimal_baseChange_of_notMem`.
   - `hasGoodReduction_cdLocal` for `p ∤ 2d`, and `hasAdditiveReduction_cdLocal` for `p ∣ 2d`.
   - `localPolynomial_cdLocal_of_not_dvd`: Mathlib's `localPolynomial` is
     `1 − a_p T + p T²` with `a_p = p + 1 − #C_d(𝔽_p)`.
   - `localPolynomial_cdLocal_of_dvd`: the local polynomial is `1`.

   `localPolynomial` uses Mathlib's minimal model, which is picked by `Classical.choice`.
   Generic lemmas over any DVR show that the result does not depend on that choice:
   - two minimal models differ by a change of variables with `v(u) = 1`;
   - such a change descends to the residue field (Mathlib's
     `variableChange_integral_of_u_integral`);
   - isomorphic curves have the same number of points.

   The residue field of the completion is identified with `ZMod p` through Mathlib's
   `padicIntEquiv` and `PadicInt.residueField`.
2. **Global results** (task item 2).
   - `LFunction_cd_apply_prime`: the coefficient of `(shortCurve (-(d:ℚ)^2)).LFunction` at a
     prime `p` is `p + 1 − #C_d(𝔽_p)` if `p ∤ 2d`, and `0` if `p ∣ 2d`.
   - `LFunction_cd_apply_prime_eq_sub_card`: the same coefficient is
     `p − #{(x,y) ∈ 𝔽_p² : y² = x³ − d²x}`.

   Going further than the task asked:
   - `LFunction_cd_apply_prime_pow` gives the coefficient at `p^k`.
   - `isMultiplicative_LFunction` holds for any curve over `ℚ`.
   - `LFunction_cd_apply` gives every coefficient.
   - `LSeries_cd_eq` and `LSeries_cd_eq_of_mod_eight` prove that `E.LSeries s`, the function in
     the CR3 Props, equals `LSeries (cdCoeff d) s`. That is the Dirichlet series of
     `∏_{p∤2d} (1 − a_p p^{−s} + p^{1−2s})^{−1}`, the standard `L(C_d, s)`. Its coefficients at
     bad primes and their powers are 0.

**What is not covered, and why**
- **Even `d`.** For even `d`, `v_2(Δ) = 6 + 6·v_2(d) ≥ 12`, so the `Δ ∉ 𝔪^12` test fails. Proving
  minimality at 2 would need Tate's algorithm, which Mathlib does not have. The CR3 Props only
  use `d ≡ 5 (mod 8)`, so this case is not needed.
- **Analytic facts.** These are not in Mathlib v4.35.0, and the task did not ask for them:
  - Hasse's bound, so absolute convergence for `Re s > 3/2` is not proved;
  - the analytic continuation.

  `LSeries_cd_eq` is an equality of the `tsum` values, so it holds for every `s`. It does not use
  convergence.
- **Nothing from item 3 was out of reach** for odd squarefree `d`. The completion, its residue
  field, the minimal model and the reduction were all handled with the existing API.

**Build.**
- `lake build ZInQKernel`: Build completed successfully (9923 jobs).
- `lake env lean scripts/print_axioms.lean`: 80 entries, including the 11 new ones. Every entry
  shows only `[propext, Classical.choice, Quot.sound]`.
- Logs: `scratch/lfun-cd/log.md` and `scratch/lfun-cd/print_axioms.out`.
