# Appendix E twist — results log

- Base: `1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2`.
- Required multiplier divisibility: `4m² ∣ c`. At modulus `m=N` use `M=N³` and `4 ∣ N`.
- `Cusps.lean`: `lake env lean` succeeded; rational translates preserve the all-cusp limit.
- Fourier inversion at the original modulus implements the imprimitive coefficient sieve.
- The Poisson comparison uses the unevaluated quadratic Gauss sum; its numerator shifts by a unit square.
- `Fourier.lean`: compiled; Fourier inversion, character covariance, primitive Gauss normalization, q-series and coefficient extraction, prime deletion, and the primitive-character sieve.
- `Fourier.lean`, `Cusps.lean`: `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- `Translation.lean`: compiled. Integral conjugate at level `N³` with new index `d²u` and unchanged bottom-right entry modulo `N`; differentiation and cusp limit for the sum.
- `ThetaGauss.lean`: compiled. Even frequencies by square completion, odd frequencies cancel, numerator changes by a unit square for `4m² ∣ c`.
- `Translation.lean`, `ThetaGauss.lean`: `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
- `ThetaNonvanishing.lean`: compiled. Theta duplication by parity separation and upper-half-plane nonvanishing by iteration; all four axiom checks are standard.
- `ThetaPoisson.lean`: compiled. Residue splitting and the two-variable Jacobi equation give the rational Poisson expansion; at denominators divisible by four the even modes reduce it to the original theta. All five axiom checks are standard.
- `Multiplier.lean`: compiled. Actual theta ratios agree for all signs of the bottom-left entry under `4m² ∣ c` and the rational matrix equality. All seven axiom checks are standard.
- `Twist.lean`: compiled. `halfIntegralTwist : AppE.HalfIntegralTwist` with witness `N³` and the original-modulus translation sum. `halfIntegralTwist`, the conditional construction, and the bridge to `thetaMultiplier` depend only on `propext`, `Classical.choice`, `Quot.sound`.
- `Twist.lean`: recompiled after extracting the covariance criterion and adding `primitive_twist` for every conductor `r ∣ N`. The primitive Gauss sum has the required character and coefficients at `N³` before the original-modulus sieve. All five axiom checks are standard.
