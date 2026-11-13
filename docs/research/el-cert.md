# el-cert: redesigning the slope certificate and the test shift to avoid CR₃

Base: `e3612538` (main `50d1b05` plus the cr3-map notes). No Lean was run, and no file under
`ZInQKernel/` or `blueprint/` was edited. Scripts are in `scratch/el-cert/` and use PARI 2.17 via
cypari2. Every computation ran sequentially in under 10 minutes. The step-by-step record is
`scratch/el-cert/log.md`.

Marks: **VERIFIED** means checked against the Lean sources or by exact computation (script
named). **STANDARD** means a published theorem. **SPECULATIVE** means unproved.

## 0. Verdict

- **Does the angle eliminate CR₃? No.** Chance: **very low**.
- **What the angle does achieve.** One redesign, M1 ("frozen Θ"), is sound, needs no extra
  variables and costs nothing in the budget. Under M1:
  - the pole input `s` has degree 2 in the free parameter, instead of 50 (test site) or 518
    (slope site);
  - the θ = 1 locus drops from genus 49 or 517 to **genus 1**.
- **Explicit witnesses free us from the open set.** With an explicit witness (θ = 1, 2-torsion),
  completeness needs none of the open set U, the admissibility box or the square denominator.
  Only the guards are needed.
- **Strongest obstruction.** Three facts combine:
  - (L-A) Every soundness-admissible free parameter enters through a map of degree at least 2.
  - (L-B) Honest instances are Zariski dense among bad ones, so no algebraic (uniform) witness
    can exist. Completeness needs an arithmetic existence theorem.
  - The θ = 1 locus over any such family is therefore of Calabi–Yau type at best. M1 reaches the
    best case, a genus-1 curve. No theorem gives rational points on these curves. Locally, they
    are obstructed for most honest instances unless the multiplier group has about 67 bits
    (X3b). Globally, small points were found in 0 of 30 toy instances, and 25% of the Jacobians
    have rank 0 (X3c).
- **What completeness would need.** Rational points on genus-1 curves (2-coverings), i.e. a
  rank/Ш statement of the same kind as CR₃. Unlike CR₃, that statement is not even known to be
  true.

## 1. Why `s = ℓ₀a/Θ` has its current form (traced in Lean) — VERIFIED

**Data at the two sites.**
- Test site (`Assembly/Local/SixLocalTests.lean`):
  - `R₀ = η·2730⁶·F(t)`, `a₀ = 1 − R₀q²`, `R = R₀a₀²`;
  - `W = Π_j(1 + R·C_j²)`, `Θ = Tr W⁻¹`;
  - `Test` asserts the guards and `PoleSoluble(R/Θ²)`.
- Slope site (`Multiplication/Certificate/SlopePredicate.lean`):
  - `R₀ = ηF(t)/(t−1)⁸`, `R = ℓ²a²R₀`;
  - `W_g = Π_j(1 + R·C_gj²)`, `Θ = Tr Σ_g W_g⁻¹`.

**How soundness uses Φ.** Soundness uses Φ only through the pole step:
- `pole_step` (`TestDivisibility.lean:225`), and `Mult.pole_obstruction` inside
  `common_group_of` (`CommonGroup.lean`);
- from `Φ(R/Θ²)` and `r = v_p(R)` odd, they conclude `2v_p(Θ) < r`.

It then uses two more facts:
- `vp_one_add_mul_sq`: each factor `1 + RC²` has valuation `min(0, r + 2v(C))`;
- the trace bound `trace_val` / `vp_trace_ge`.

Together these give "tests small" at one place and group.

**Exactly what soundness needs from `a`.** It needs only `v_p(a) ≤ 0` at every contact prime.
- `testR_val` and `contact_valuations_of` prove this: since `v_p(R₀)` is odd, `1 − R₀q²` cannot
  cancel.
- So `r = v(R₀) + 2v(a) ≤ v(R₀)`, and a smaller `r` only strengthens the conclusion.
- No other property of `q` is used in soundness.

**What `q` does in completeness.** It only puts `B` into the PC-admissible box:
- the real place: `a ≈ 0`, so `B < 1/2`;
- `v_p(q) ≥ C_p` on `S_b`, or a Lemma P ball;
- the square denominator.

**Why `R`, not `R₀`, sits inside `W`.** Soundness does not need it. It is the reason `s` has
high degree in `q`: `Θ` depends on `q` through `R`.

## 2. Route M1: the frozen-Θ certificate

**Replacement statement.** At the test site, put
```
W₀ = Π_j (1 + R₀ C_j²),  Θ₀ = Tr W₀⁻¹,  B = R₀ a₀² / Θ₀²,  a₀ = 1 − R₀q²
```
At the slope site, put
```
W_g = Π_j (1 + ℓ²R₀ C_gj²),  Θ₀ = Tr Σ_g W_g⁻¹,  B = ℓ²a²R₀ / Θ₀²
```
In Lean terms: replace `poleW (testR η q t)` by `poleW (testR₀ η t)`, and
`groupW (slopeR ℓ a R₀)` by `groupW (slopeR ℓ 1 R₀)`. Keep the pole input's numerator.

**Soundness (VERIFIED by reading the proofs).**
- `Φ(B)` gives `2v(Θ₀) < v(R₀′) + 2v(a) ≤ v(R₀′)`.
- This is the inequality the existing proofs derive at `q = 0` (`a = 1`, `r = k`), and the rest
  of `tests_small` and `common_group_of` never sees `q` again.
- So M1 soundness is the existing soundness at `q = 0`, plus `v(a) ≤ 0`.
- X1 (`x1_genus.py`) enumerated `k` odd in 1..11, `v(Θ₀)` in −6..11 and `v(q)` in −12..11. It found
  0 counterexamples.

**Guards.**
- `η` makes `R₀ > 0`, and `K₀ = ℚ(√2)` is totally real.
- So every factor is at least 1 in both embeddings, hence `W₀ > 0` and `Θ₀ > 0`.
- The guards `W ≠ 0` and `Θ ≠ 0` therefore hold for every `q`. (VERIFIED, elementary)

**Budget.** The operation count is unchanged: `R₀` replaces `R` inside `W`. No new witness.
(VERIFIED from the formulas; the compiled template was not re-measured)

**Completeness via PC (CR₃ kept).**
- The real place and the square denominator go through as before.
- **Caveat** (SPECULATIVE): under field 2′ the Lemma P ball made `a`, hence `R`, `p`-adically
  small inside `W`. With `R₀` inside `W` that smallness is lost. So `W ≡ 1` at those primes must
  be re-checked. This matters only if CR₃ is kept.

**Completeness without CR₃ (θ = 1).**
- `Test` and `SlopePred` require only the guards and `PoleSoluble(B)`.
- If `m(m − B) = c²`, the 2-torsion witness gives Φ (rs-pole §2.2(2)).
- So U and admissibility are irrelevant. (VERIFIED from the definitions)
- The remaining requirement is a rational point on
  ```
  C_m :  Y² = m²Θ₀² − mR₀′(1 − R₀q²)²,
  ```
  which is genus 1.

**Experiments.**

| exp | input | outcome |
| --- | --- | --- |
| X2 (`x1_genus.py`) | random toy tests in ℚ(√2), `R₀ = 7/3`, `m = 3` | θ=1 curve: test original deg 100, **genus 49**; slope original deg 1036, **genus 517**; M1 both sites **genus 1** (squarefree, exact) |
| X3a (`x3_local.py`) | `p` = 11..23, 26 random cases | criterion below agrees 26/26 (brute force mod `p³`) |
| X3b (`x3_stats.py`) | 200 trials per row; obstruction primes `~ Poisson(½ log log N)` | P(some `m` locally unobstructed): `log₁₀N = 10³`: 0.43 / 0.79 / 1.00; `10⁶`: 0.12 / 0.43 / 1.00; `10⁹`: 0.015 / 0.12 / 1.00 for DL8 / signed divisors of 2730 / group `⟨−1, p ≤ 324⟩` |
| X3c (`x3_points.py`) | 30 toy instances `R₀ = |F(n)|`, random `Θ₀`, `m` ∈ DL8 (240 curves) | 0 points of height ≤ 2000; Jacobian rank bounds (0,0): 61, (1,1): 104, (0,2): 66, (1,3): 9 |

**Local obstruction lemma (VERIFIED: derivation and X3a).** Let `p` be odd with `p ∤ 2mR₀`,
`p ∣ num Θ₀` and `(R₀/p) = −1`. Then `C_m(ℚ_p) ≠ ∅` iff `(−m/p) = −1`.
- Honest `Θ₀` has astronomically large height: the deep multiples `κ` make `log₁₀ N` enormous.
- So with the present 6 multiplier bits, θ = 1 is locally impossible for most instances.
- The L7 multipliers `m₀k²` with `m₀ ∣ Π_{p≤324} p` clear this obstruction. The cost is about 61
  more bits per pole call, about `5·10⁸` variables that would have to be saved elsewhere.
- Even then the global question is a rank/Ш question for the 2-covering `C_m`. X3c shows rank-0
  Jacobians are common.

**Verdict M1.** It is a sound, budget-neutral simplification, and it gives the best genus
reachable (§4). It does not eliminate CR₃. Chance: very low.

## 3. Other routes tried

**R2: multiplier as a free square** (`m = m₀k²`, L7 of cr3-map-needs).
- Statement: `Φ(B)` via θ = 1 with `k = (u + m₀B/u)/(2m₀)`. This works for every `B` and `u`.
- Soundness needs `v_p(k) ≥ 0` at contact primes for every witness value.
- The available `p`-integral families are:
  - `1/(1 − R₀q²)`;
  - `ℤ[t]` (`t` is `p`-integral at its own contact primes, a new observation);
  - bit-integers.
- Each enters with degree at least 2 (L-A). The fibre product with the `u`-conic has genus 1, or is
  a K3 surface with two such parameters.
- A uniform Poonen-style quaternion definition `T_{a,b} = ∩_{p∈Δ_{a,b}} ℤ_(p)` (Poonen 2009,
  STANDARD) would need `(a,b)_p = −1` at every contact prime. No fixed `b` does this (L-C).
- Verdict: very low.

**R3: additive Θ shift** (`Θ = Θ₀ + R₀h`, `v_p(h) ≥ 0`).
- Soundness holds: in the bad case `v(Θ) ≥ min(v(Θ₀), k) > k/2`.
- With numerator 1, θ = 1 becomes the rational conic `m²T² − mR₀ = Y²`, with
  `T = (u + mR₀/u)/(2m)`.
- But `h = (T − Θ₀)/R₀` must be a value of a `p`-integral family:
  - with `h = 1/A(q₂)`: a bidegree (2,2) curve, genus 1;
  - with both `g = A(q₁)` and `h = 1/A(q₂)`: tridegree (2,2,2) in `(ℙ¹)³`, a K3 surface.
- (VERIFIED: algebra) Verdict: very low.

**R4: one-curve torsion target** (`t₁ = ∞`, rs-pole §2.2(3)).
- The condition `E_{B(m−B)}` has a point with `x ∈ mBℚ*²` is quartic in its parameter.
- The same counting gives genus at least 1 in each parameter. Verdict: very low.

**Test-shift freedom** (`κ`, `h = jκ`, `s₀`) and slope shifts.
- These change `Θ₀`, and so give infinitely many curves `C_m` per instance.
- No theorem guarantees a point on any of them. They only improve the heuristic odds.

## 4. Structural lemmas (why every thin/explicit redesign fails)

**L-A (degree; VERIFIED, elementary).** Let `f ∈ ℚ(R₀)(u)` be nonconstant with `v_p(f) ≤ γ` (or
`≥ γ`) on all of `ℙ¹(ℚ_p)`. Then `deg f ≥ 2`.
- Reason: a Möbius map is a bijection of `ℙ¹(ℚ_p)`, so it takes valuation `γ + 1`.
- Consequence: soundness forbids any free parameter entering `B` linearly.
- `1 − R₀q²` is the minimal example. Its non-cancellation comes from the parities of
  valuations: the binary form `x² − R₀y²` is anisotropic at every prime where `v_p(R₀)` is odd.

**L-B (no algebraic witness; VERIFIED as an argument).**
- The honest test instances `(t, V₀, V₁) = (n, [κ]P₀, [κn]P₀)` are Zariski dense in `𝔸¹ × E × E`:
  - the slices are graphs of `[n]`, of unbounded degree;
  - so no surface contains infinitely many of them.
- The bad instances contain `(p-adic open set of t) × (pairs of multiples)`, which is also Zariski
  dense.
- Suppose a witness is a rational map of the instance data that zeroes `polePoly` on the honest
  locus.
  - Then it zeroes `polePoly` generically.
  - So it also zeroes it at some bad instance, where `v_p(B)` is negative and odd for every `q`.
  - That contradicts Lemma 5.1.
- So completeness always needs an arithmetic, non-uniform existence theorem. This also explains
  why rs-pole §4.3 found no explicit family.

**L-C (uniform anisotropy is valuation-only).**
- Uniformly in the instance, the only information at a contact prime is that `v_p(R₀)` is odd.
- No fixed `b ∈ ℚ(t)*` is a nonresidue at every contact prime (Chebotarev, STANDARD).
- Forms that are anisotropic by valuations alone have at most `d` variables in degree `d`:
  their monomials must have distinct valuations mod `d`. Examples are `x² − R₀y²` and
  `N_{ℚ(R₀^{1/4})/ℚ}`.
- (The "at most `d` variables for every uniform form" claim is SPECULATIVE.)

**Consequence (Kodaira dimension; SPECULATIVE beyond `n = d = 2`).**
- The θ = 1 locus over such a family is the double cover of `ℙ^{n−1}` branched along
  `{F = ±cG}`, a divisor of degree `2d` with `n ≤ d`.
- So `K = (d − n)H ≥ 0`:
  - `n = d = 2` gives a genus-1 curve (M1 attains this);
  - `n = d = 3` gives a K3 surface;
  - `n = d = 4` gives a Calabi–Yau threefold.
- None of these is rational, so no Hasse-principle theorem applies, and L-B rules out uniform
  sections.

**Conic Φ′ cannot replace Φ.**
- Take a Hilbert-symbol obstruction `(a(B), b(B))_p` with coefficients polynomial in `B`. At
  `v_p(B)` negative it depends on the leading unit `c` mod `p` (`(B, cB^d)_p = ((−1)^d c/p)^{v}`).
  So it cannot be obstructed exactly when `v_p(B)` is negative and odd at every large prime.
  (VERIFIED for this shape; the general claim is SPECULATIVE)
- Hence a "fat" sound Φ′, complete on an open set, needs genus-1 fibres. Its completeness is
  then a Hasse principle for 2-coverings, which is CR₃'s class (cr3-map-literature).

**The sandwich.** This sharpens L9 of cr3-map-needs into two cases:
- **thin Φ′** (explicit witnesses): rational points on Calabi–Yau-type fibre products; genus 1
  at best, via M1;
- **fat Φ′**: a Hasse principle for genus-1 curves.

Neither is available without Heegner-point or Ш input.

## 5. What survives

1. **M1 as a cleanup.** It is sound, adds no variables, and makes `s = a/Θ₀` quadratic in `q`.
   If CR₃ is kept, the field-2′ Lemma P caveat (§2) must be checked first.
2. **A sharper target for any future elimination attempt.** One would have to prove, for every
   honest instance and some admissible `(κ, h, s₀, m)`, that the genus-1 curve
   `Y² = m²Θ₀² − mR₀′(1 − R₀q²)²` has a rational point. This is a statement about one 2-covering
   per instance. It is not implied by TYZ. It needs the L7 multiplier group to clear the local
   obstructions, and it is likely false for some instances with the present 6 bits (X3b).
3. **Observations that remove false constraints.**
   - `t` is `p`-integral at its own contact primes, so `ℤ[t]` is available as a source of
     `p`-integral factors in soundness.
   - Explicit witnesses do not need the admissible box.

## Scripts

- `x1_genus.py`: X1 valuation enumeration and X2 genus of the θ = 1 locus, original vs M1
  (under 3 min).
- `x3_local.py`: X3a local criterion, brute force mod `p³`.
- `x3_stats.py`: X3b local-obstruction probabilities for the three multiplier sets.
- `x3_points.py`: X3c Jacobian ranks and point search on 240 toy curves (about 8 min).
