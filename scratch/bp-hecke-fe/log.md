# bp-hecke-fe results log

## Theta.lean (VERIFIED: compiles, no sorry, `lake env lean`, 2026-11-12 ~17:40)
- `gaussTheta a b x = oddKernel a x · evenKernel b x + i · evenKernel a x · oddKernel b x`
  (= Σ_{(m,n)∈ℤ²} ((m+a)+i(n+b)) e^{−π((m+a)²+(n+b)²)x}), dual with sinKernel/cosKernel.
- `gaussTheta_one_div`: gaussTheta a b (1/x) = x² · gaussThetaDual a b x (x > 0).
- `gaussFEPair`, `isStrong_gaussFEPair`: strong FE-pair, k = 2, ε = 1.
- `differentiable_gaussLambda` (Mellin transform entire), `gaussLambda_two_sub`
  (Λ(2 − s) = Λ^dual(s)), `mellinConvergent_gaussTheta` (all s).
