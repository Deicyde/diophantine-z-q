# el-special — summary

**Does the angle eliminate CR₃?** No. **Chance: very low.**

**Findings** (details in `docs/research/el-special.md`; scripts and log in `scratch/el-special/`):
- **Slots and auxiliary primes of `n` are irrelevant to existence.** `∃N` with points on `C_N`
  and `C_{Nθ}` (abscissa in `βℚ*²`) holds iff `X_{β,θ}` has a rational point. So no prime
  configuration in `N` (prime APs, Dirichlet slots) can create points. Prime 3-APs give only the
  classical triangle points, with classes `±(a²−b²), ±ab` (C1).
- **Slope site under Proposition AP.** `β` = `m` times six AP primes, and `β = 7` at `t₃ = −10`
  (C2). Unbounded `ω(β)` happens only at the test site. `θ` stays uncontrolled at both sites.
- **Multiplier route.** `m = m₀k²` with `k` rational gives explicit witnesses for every `B`,
  through the Châtelet surface `x² − βy² = β²t⁴ − 1` (C3, 30/30). But then `v_p(k) ≤ −1` exactly
  at the bad primes, so Lemma 5.1 is lost.
  - With integral `k` the family yields nothing on 30 instance-like inputs.
  - A bounded search (`k ≤ 2⁸`, 8 values of `m₀`, 30 inputs) finds 0 explicit points out of 61440.
- **Barrier (Lemma G).** Any witness family that is uniform over the instances and given by
  formulas whose free parameters satisfy only genus-0 / rationally connected conditions
  contradicts the local proof of Lemma 5.1. The proof combines Graber–Harris–Starr or Tsen,
  Hensel and Chebotarev, along curves on which `B` has an odd pole (`B ~ λ^{15−52M}`, checked in C5).
  So completeness is necessarily a non-explicit rank/Sha statement, which is what CR₃ supplies.

**Single next step.** Stop pursuing explicit or elementary elimination. Split the CR₃ input
into two parts and state the slope-site part as a separate, narrower `Prop`:
- slope-site: `β` = six AP primes with residues fixed by the `(u, v)` choice, or `β = 7`;
- test-site: arbitrary `β`.

That separates the cost of the slope site from the test site, which is the only place where
`ω(β)` is unbounded.
