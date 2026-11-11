# el-gadget: can a genus-0 or elementary pole gadget eliminate CR₃?

**No. Chance: very low.** Full note: `docs/research/el-gadget.md`; log and scripts: `scratch/el-gadget/`.

- **Theorem G (proved, from standard inputs).** A gadget can keep a Lemma 5.1-style soundness obstruction,
  uniform in all large primes, only if the gadget's fibration over the bad locus has a geometric double fibre
  (all components of even multiplicity). Then its fibres have no point over `Q̄((t))`, so they are not
  rationally connected (Graber–Harris–Starr).
  - This rules out conics, quadrics, norm forms, conic bundles and Châtelet surfaces, even with coefficients
    depending on the input. Over `Q̄((t))` (a C₁ field) they always have points, and Chebotarev then gives a
    positive density of primes where soundness fails.
  - This generalizes rs-global C2, which covered only "abscissa on `y² = g(x, e)`" devices.
- **Exact counterexamples (E1).**
  - `x² + y² = m(m − B)` has rational witnesses with `v_p(B) = −1` at exactly the primes `p ≡ 1 (mod 4)` in
    `[331, 700)`, 28 of 59.
  - A multiplier-twisted conic, a Poonen-type quaternion gadget built from the input, and a gadget using the
    instance class `R₀` have them at all 59 primes.
- **Column property (E2, verified).** Since `v_p(1 − R₀q²) ≤ 0`, data that is bad because a test is large
  stays bad for every `q`. So the theorem applies to the whole completeness variety: any sound gadget needs,
  for completeness, rational points on non-rationally-connected varieties.
  - Explicit witness families are impossible, because the honest data are Zariski dense.
  - The best square-class gadget needs a point on a curve of genus 25–37 per toy instance (E3). A redesign
    with `q`-independent `Θ` reaches genus 1, a 2-covering quartic of CR₃'s kind: in 30 samples no point
    of height ≤ 2000 was found, though the Jacobians have rank ≥ 1 (E4).
- **Strongest obstruction.** Uniform soundness forces a double fibre, and a double fibre forces a variety
  that is not rationally connected. Points on such varieties over a Zariski-dense set of data need positive
  rank or finiteness of Ш, which is exactly CR₃'s content.

**Single next step.** Stop pursuing gadget replacement. Fold Theorem G (with the column corollary) into
rs-global §2.3 as the general form of C2, and put the elimination effort on the positive-rank statement
itself (CR₃^rk).
