# Appendix E twist — results log

- Base: `1ddd7c2ac7a579baf80026a2f48bb8206ce6cdf2`.
- Required multiplier divisibility: `4m² ∣ c`. At modulus `m=N` use `M=N³` and `4 ∣ N`.
- `Cusps.lean`: `lake env lean` succeeded; rational translates preserve the all-cusp limit.
- Fourier inversion at the original modulus implements the imprimitive coefficient sieve.
- The Poisson comparison uses the unevaluated quadratic Gauss sum; its numerator shifts by a unit square.
- `Fourier.lean`: compiled; Fourier inversion, character covariance, primitive Gauss normalization, q-series and coefficient extraction, prime deletion, and the primitive-character sieve.
- `Fourier.lean`, `Cusps.lean`: `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
