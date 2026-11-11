# el-gadget log

Task: replace the pole gadget by one with elementary completeness (conics, quadrics, conic bundles,
Châtelet surfaces, sections) while keeping a soundness obstruction uniform in all primes > 324.

## Definitions

- Witness/data space `Y`: all construction witnesses feeding the pole call (t or n, q, tests C).
  `B = R/Θ²` with `R = R₀a²`, `a = 1 − R₀q²`.
- Gadget: a Q-variety `X` with a morphism `π : X → Y`; `Φ'(y) :⇔ X_y(ℚ) ≠ ∅`.
- Bad set at `p`: `Bad_p = {y ∈ Y(ℚ_p) : v_p(R) odd, 2v_p(Θ) ≥ v_p(R)}` (equivalently `v_p(B) < 0` odd).
- Local uniform soundness (LUS): for all `p > p₀` and all `x ∈ X(ℚ_p)`, `π(x) ∉ Bad_p`. Lemma 5.1 is LUS.
- `F = Q̄((t))` (Laurent series), `F_m = Q̄((t^{1/m}))`.

## Facts read from sources

- R0. Non-inflatable free factor: `v_p(a) ≤ 0` whenever `v_p(R₀)` odd > 0 (no cancellation in
  `1 − R₀q²`). Hence column property: if `(t, tests)` is bad at `p` for one `q` because a test is
  large (`v_p(RC²) < 0` odd), it is bad for every `q`. (VERIFIED: prime_dvd_of_test,
  TestDivisibility.lean:321 ff, pole_step:225, trace_val; testR_val.)
- R1. rs-global C2 covers only devices "abscissa of a point on y² = g(x,e)". Quadrics/norm forms/
  higher-dim RC gadgets were not covered (A5 only heuristically).
