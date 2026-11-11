# el-cert: summary

**Does the angle eliminate CR₃? No.** Chance: **very low**. Details are in
`docs/research/el-cert.md`, the step log in `scratch/el-cert/log.md`.

**What was found**

- **M1, a valid redesign ("frozen Θ").** Build `W` from `R₀` (`ℓ²R₀` at the slope site) instead
  of `R = R₀a²`, and keep `a²` in the numerator of the pole input.
  - Soundness is the existing proof at `q = 0`, plus `v_p(a) ≤ 0`. VERIFIED by reading
    `pole_step`, `common_group_of` and `testR_val`.
  - The guards hold for every `q` by positivity.
  - No extra variables.
  - The degree of `s` in `q` drops from 50 / 518 to 2, and the genus of the θ = 1 locus from
    49 / 517 to 1 (exact, X2).
- **Explicit witnesses do not need the open set.** With θ = 1 (2-torsion), `Test` and
  `SlopePred` need only the guards. The open set U and the admissibility box are irrelevant.
- **The remaining requirement fails, locally and globally.**
  - Completeness then needs a rational point on the genus-1 curve
    `Y² = m²Θ₀² − mR₀′(1 − R₀q²)²`.
  - There is an exact local obstruction at primes `p ∣ Θ₀` with `(R₀/p) = −1`: the curve has
    `ℚ_p`-points only if `(−m/p) = −1`. With 6 multiplier bits it kills most honest instances
    (X3b: P(some multiplier passes) ≈ 0.015 at `log₁₀ N = 10⁹`).
  - Clearing it needs the L7 group (about 67 bits, roughly `5·10⁸` extra variables).
  - Globally: 0/30 toy instances had a point of height ≤ 2000, and 25% of the Jacobians have
    proven rank 0 (X3c).
- **Strongest obstruction.** Three facts together:
  - L-A: every sound free parameter enters through a map of degree at least 2;
  - L-B: honest instances are Zariski dense among bad ones, so no uniform algebraic witness
    exists;
  - L-C: uniform anisotropy is valuation-only.

  So the θ = 1 locus over any sound family is at best Calabi–Yau, and M1's genus 1 is the
  optimum. A "fat" sound predicate would instead need a Hasse principle for 2-coverings, which
  is CR₃'s class.
- **Routes R2–R4 reduce to the same counting.** Free-square multiplier, additive Θ shift and the
  one-curve torsion target all give genus 1 or a K3 surface.

**Single next step.** If M1 is wanted as a cleanup, the one open soundness/completeness check
is: under field 2′ (Lemma P ball), does `W ≡ 1` still hold at those old primes when `R₀`
replaces `R` inside `W`? Read `PoleLocal.lean` / `PoleValuations.lean` for where `a`'s
smallness enters. If it does not hold, M1 must stay test-site-only. For eliminating CR₃, this
angle is closed. What would remain is a rank statement for one genus-1 curve per instance,
which is not known even conditionally on TYZ.
