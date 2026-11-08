# rs-pattern: report

Deliverable: `docs/research/rs-pattern.md`. Scripts and outputs are in `scratch/rs-pattern/`.

## Summary

- **The only use of 22P.** `FixedPrimePattern` is opened only in `ZInQ.Mult.pattern_slopes`. That lemma is called with `B₀ = 0` (`Core.lean:22`), and its output is exactly: for every `A ∈ ℤ`, three slopes summing to `A` that satisfy `GoodSlope`.
- **Parts of the hypothesis that are never used:**
  - `B₀`;
  - `p ∤ d₁d₂` and `p ≠ 2`;
  - prime conditions on `v` and `u_j − v`: they need only congruence conditions at the old primes, so 18 forms matter, not 22;
  - the catalogue multipliers: multipliers in `{1, 2, 8P_s}` suffice;
  - a common denominator.
- **Further slack.** Square factors are allowed, and `gcd(d₁,d₂) = 4` can be weakened to `gcd(d₁,d₂) | c_*`.
- **What cannot be weakened:**
  - at most six odd-exponent primes per slope: the frozen variable count leaves no room for more test groups, since each extra multiplication witness costs more than 3.1 million variables;
  - each of those primes must be good individually, with exponent exactly 1;
  - bounded valuations at the old primes.
- **Translation-invariant form.** `t₃ = −10` is a valid slope with no new primes (checked). So 22P can be replaced, without changing the polynomial, by 22P₂: for every `A`, a homothetic copy `{u − c′v : c′ ∈ 𝒞 ∪ (A + 10 − 𝒞)}` of a 12-point set inside the good primes, with `v = 8P_s w`, `w` odd, `v_q(w) ≤ 3`. No multipliers are needed.
- **CAT can be removed without effective Dirichlet.** The catalogue exists in the construction only to supply the multipliers in the manuscript's proof of 22P. With 22P₂ or 22P′, the construction can drop it (`N_s = P_s`, `ℓ₀ = 12P_s^2916`, `S_b = S_ht`). CAT then disappears without the effective Dirichlet theorem. Soundness does not depend on the catalogue (checked by reading `not_mem_S_mul` and `S_mul_admissible`).
- **No Dirichlet-level route for 22P.** Within this architecture none exists:
  - by a genus count (`g = 1 + 2^{m−3}(m−4)`), at most 3 of the 6 contact values can be forced to be squares in a rational family;
  - every height theorem of this kind needs at least 5 contacts;
  - goodness requires `(7/p) = −1`, which no norm form can force, plus a gcd condition on the Frobenius element modulo every `ℓ`;
  - sieves cannot control the class of each prime factor;
  - so a single large good slope already needs a prime pattern of true complexity at least 3, and three coupled slopes need GTZ.

## Computations

- **Goodness criterion.** The point-count definition `GoodPatternPrime` agrees with the CM description (`p ≡ 1 mod 8`, `(p/7) = −1`, `gcd(a, p+1)` with no odd prime factor, where `p = a² + b²`) for all 17,980 primes up to `2·10⁵`. Good primes are 10.7% of all primes; within the class, 84.8% are good (87.7% if the orders of `P₀` are used instead of the group orders).
- **Catalogue-free local recipe.** The recipe for all 22 forms was checked exactly with the real `P_s = 324#`, for 30 values of `A`.
- **Small-scale configurations.** Configurations were found for the three-slope, difference and two-slope forms, for 14 values of `A` each, in a scaled-down model whose old primes are `{2, 3, 5, 7}`. Each was checked against the analogue of `GoodSlope`.

## Ranking

1. **R2 with R1/R3** (high chance): state 22P₂ and drop the catalogue. Removes CAT outright; 22P keeps the same depth (GTZ) but becomes much simpler. Cost: a construction refactor, and `P_*` no longer matches the manuscript's literal polynomial (the project lead's decision).
2. **R1/R3 only** (high chance): state 22P₂ with the construction unchanged. One Lean file.
3. **R4** (low chance): Green–Tao 2008 instead of GTZ for 22P₂. It is blocked by the need to control the small-prime valuations of the common difference: the difference must lie in a residue class that is not intersective.
4. Sieve methods, parametrizations, CM tricks and changes of curve or test do not lead to a Dirichlet- or Chebotarev-level proof.

## Open questions

- Is there a theorem giving arithmetic progressions, or homothetic copies of a finite set, in a dense subset of the primes with the common difference in a prescribed residue class, without the inverse theorem for the Gowers norms?
- The adaptation of the manuscript's GTZ argument to 22P′ and 22P₂ is routine (2 variables, 12 forms, fibers are lines) but has not been written out.
- Does the project accept a construction change (dropping the catalogue) in exchange for removing CAT?

## Suggested follow-up tasks

- **Lean.** Define `TwoSlopePattern` (22P₂) and prove `pattern_slopes` from it, using the constant slope `−10`; swap the hypothesis in the main theorem. Small task.
- **Lean, in a branch.** Remove the catalogue: `Syntax.Ns := Ps`, `ell := 12 Ps^2916`, `S_b := S_ht`. Redo the size numerals and delete `CatalogueBound`. Compare its cost with the effective-Dirichlet plan before starting either.
- **Writing.** Write out the GTZ proof of 22P₂, adapting manuscript lines 1291–1704 (blueprint chapter).
- **Literature.** Look for an R4-type theorem (restricted common difference in primes), or confirm that GTZ-type uniformity is needed.
