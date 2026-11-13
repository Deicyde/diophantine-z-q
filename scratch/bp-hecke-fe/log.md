# bp-hecke-fe results log

## Theta.lean (VERIFIED: compiles, no sorry, `lake env lean`, 2026-11-12 ~17:40)
- `gaussTheta a b x = oddKernel a x · evenKernel b x + i · evenKernel a x · oddKernel b x`
  (= Σ_{(m,n)∈ℤ²} ((m+a)+i(n+b)) e^{−π((m+a)²+(n+b)²)x}), dual with sinKernel/cosKernel.
- `gaussTheta_one_div`: gaussTheta a b (1/x) = x² · gaussThetaDual a b x (x > 0).
- `gaussFEPair`, `isStrong_gaussFEPair`: strong FE-pair, k = 2, ε = 1.
- `differentiable_gaussLambda` (Mellin transform entire), `gaussLambda_two_sub`
  (Λ(2 − s) = Λ^dual(s)), `mellinConvergent_gaussTheta` (all s).
- (VERIFIED, compiled ~18:05) `hasSum_gaussTheta`: gaussTheta a b t = Σ_{p∈ℤ²} gz·exp(−π gq t)
  (product of Mathlib's 1-D kernel sums, absolutely summable).
- `gaussPeriodPair` (ℤ + ℤi as Mathlib `PeriodPair`), `summable_norm_gz_rpow` (r < −2, via
  `ZLattice.summable_norm_sub_rpow`).
- `hasSum_gaussLambda`: for Re s > 3/2, Σ_p π^{−s}Γ(s) gz/gq^s = gaussLambda a b s.
- `gaussL_continuation`: the shifted lattice series Σ_p ((m+a)+i(n+b))/((m+a)²+(n+b)²)^s has an
  entire continuation F(s) = π^s Γ(s)⁻¹ Λ(s) from Re s > 3/2.
- (VERIFIED, compiled ~17:45) `twistedL M c s = Σ'_{p∈ℤ²} c(p mod M)·(p₁+ip₂)/(p₁²+p₂²)^s`;
  `summable_twisted` (Re s > 3/2), `twistedL_eq` (block decomposition into M² shifted series,
  via `blockEquiv : (Fin M)² × ℤ² ≃ ℤ²`), `twistedL_continuation`: entire continuation for
  every c : (ZMod M)² → ℂ.
