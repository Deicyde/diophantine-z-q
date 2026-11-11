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

## Theorem G (the rationally-connected wall) — statement and proof

Setting: `Y` geometrically integral Q-variety, `g : Y ⇢ ℙ¹` (the badness coordinate, e.g. `1/B`, or a local
equation of a bad divisor `D` of `Y`), `π : X → Y` dominant, generic fibre geometrically integral.

(G-a) Dichotomy (for one variety `V` with `f : V → ℙ¹`, smooth proper model over `ℤ[1/N]`):
  LUS for "v_p(f) negative odd" at all but finitely many `p`  ⇔  every geometric component of
  `f⁻¹(∞)` has even multiplicity  ⇔  `V_η` has no point over `F_m` with `1/f = t^m`, any odd `m`.
  Proof. (⇐) near `f⁻¹(∞)`, `1/f = u·g²` with `u` a unit on the model; `F₀, F_∞` disjoint, so any
  `ℤ_p`-point has `v_p(1/f)` even when positive. (⇒) a component `C` of odd multiplicity `m`, defined
  over a number field `L`; for `p` split in `L`, `p ∤ N`, Lang–Weil gives a smooth `𝔽_p`-point of `C`
  off the other components; Hensel lift with `v_p(local eq.) = 1` gives `v_p(1/f) = m` odd.
  Chebotarev: such `p` have density ≥ 1/[L^gal:Q]. (VERIFIED as proof; uses STANDARD Lang–Weil, Hensel,
  Chebotarev.) The `F_m`-point form: a germ through a smooth point of `C` transversal to `C`.

(G-b) Transfer: if `Y` has an `F_m`-point `P` with `1/g = t^m` (m odd) and the fibre `X_P` (a variety
  over `F_m`) has an `F_m`-point, then `X` has bad `ℚ_p`-points (with `v_p(1/g) = m`) for a set of primes of
  positive density. Proof: Artin approximation puts the point over `L{t^{1/m}}` (algebraic series, number
  field `L`); algebraic series converge p-adically at `t^{1/m} = p` for almost all `p` (Eisenstein);
  take `p` split in `L`.

(G-c) Fibres with points over `F_m`: `F_m ≅ Q̄((s))` is C₁ (Lang 1952) and every RC variety over it has a
  point (Graber–Harris–Starr 2003 + Artin approximation; STANDARD). Elementary sub-cases needing only C₁:
  conics, quadrics of any rank ≥ 3 (and ≥ 2 if split), norm-form varieties `N_{K/Q}(x) = c` (K⊗F splits),
  Châtelet surfaces `y² − a z² = P` (a ∈ Q* is a square in Q̄), and towers of these.

Theorem G. If the generic fibre of `π` is RC (e.g. any tower of conic/quadric/norm/Châtelet fibrations,
coefficients ARBITRARY rational functions of the input `y`), and `Y` itself is not already LUS (i.e. has
bad `ℚ_p`-points at infinitely many `p`, hence by (G-a) an `F_m`-point with `m` odd), then `X` is not LUS:
there are bad `ℚ_p`-points of `X` for a positive density of primes.

Corollary (column form). If data `y` exists that is bad for every `q` (R0 column property) and the
gadget's completeness variety over `y` (all gadget witnesses incl. q) has RC generic fibre over the data
space, LUS fails. So any LUS gadget has non-RC fibres over the data: completeness needs points on non-RC
varieties (genus ≥ 1 fibrations), where no Hasse principle holds in general.

Remark (input-dependent coefficients). Theorem G is about the total space; letting the form's
coefficients depend on `y` (or on extra existential parameters) changes nothing, since C₁ applies over
`F_m` whatever the coefficients are.

## E1. Genus-0 gadgets with input-dependent coefficients: explicit soundness counterexamples

Script `g0_counterexamples.py` (PARI qfsolve, exact check of every witness in ℚ). Primes `331 ≤ p < 700`
(59 primes); inputs `B = u/(p s²)`, `u < 60`, `s ∈ {1,2,3}`, multiplier `m` among the 16 positive divisors of 2730
(the smallest ones). A witness = rational zero with `v_p(B) = −1` (negative odd, `p > 324`): violates LUS.
- G1 `x² + y² = m(m − B)`: witnesses at 28/59 primes = exactly the primes `p ≡ 1 (mod 4)` (28 of 59), i.e. the
  primes split in `L = ℚ(i)`, the field of the multiplicity-one components over `B = ∞`. Matches Theorem G.
- G2 `x² − m y² = m − B`: 59/59 (the existential multiplier covers every Frobenius class).
- G3 Poonen-type, algebra depending on input: `2/B ∈ S_{m, m−B}`: 59/59.
- G5 multi-input `x² − R₀y² = m(m − B)`, `B = R₀σ²`: 59/59, trivially (`m = 1`, `x = 1`, `y = σ`: a section).
Example (G1): `B = 1/337`, `m = 2`: `(−139/337)² + (−659/337)² = 2(2 − 1/337)`.
VERIFIED (exact). Outcome: as predicted, uniform soundness fails; with an existential parameter ranging over a
set whose square classes generate, it fails at every prime tested.

## E2. Column property (VERIFIED: derivation + exact check)

Derivation: for `p` odd with `v_p(R₀)` odd, `v(1 + RC²) = min(0, v(R) + 2v(C))` (no cancellation, odd vs 0), so
`v(B) = v(R) + 2Σ_j min(0, v(R) + 2v(C_j))` for rational tests (`Θ = 2/W`); `v(R) = v(R₀) + 2v(a)` with `v(a) ≤ 0`,
and `v(B)` is nondecreasing in `v(R)` (step 2). Bad at a `p`-integral `q` (`v(a) = 0`) ⇒ bad for all `q`.
Over `K₀` the trace bound only raises `v(Θ)`, so the same holds (trace_val).
Script `column_check.py`: 30 random bad data (`v_p(R₀) = 1`, one test with `v_p(C) = −1`, `p ∈ (349, 2741)`),
200 random `q` each (denominators up to `p³`): 6000 pairs, 0 not bad.
Consequence: the pole gadget must reject a whole column `{y} × ℙ¹_q`, so by Theorem G (column form) the
completeness variety over honest data cannot have RC generic fibre.

## E3. Genus of the trivial-witness curve on honest lines (current design; VERIFIED, `genus_trivial.py`)

Toy test site: `R₀ = 331·u`, six tests in `ℚ(√2)` with small coordinates, `Θ = Tr W⁻¹`, `B = R₀a²/Θ²`.
Curve `h² = m(m − B(q))`: degree 84–100 in `q`, 52–76 branch points, genus 25–37 (3 trials × m ∈ {1,2}).
(The slope site has 72 tests: larger.) So the double-cover gadget "m(m−B) ∈ ℚ²" (sound) needs a rational
point on a curve of genus ≥ 25 per instance: Faltings-finite, no uniform argument.
