# CM trace sizing and checks

- VERIFIED (base source): `HKGZ.PoleCMTraceDictionary` asks for an actual point
  satisfying `HKRefereed.IsHeegnerTrace` on the pole curve. Its unaveraged sum
  is over the automorphisms of Tau Ceti's actual `hilbertClassField K`. It
  asks for a rational parametrization scale and a non-CM period lattice.
- VERIFIED (base source): `modularToWeakWeil_of_printed` reaches
  `HasWeakWeilParametrization`; it keeps the periods and rational scale, but
  exports no algebraic map, specialization, or equality with its analytic
  evaluation. The newform-level equality in `HKGZAuxiliary` compares two Lean
  levels. It does not by itself compare either one with the conductor used by
  a canonical algebraic model.
- VERIFIED (base source): `GenuineHeegnerAnchor` assumes both field rationality
  over `D.H d` and the analytic image equation. `CCLThm2_15Applied` is
  conditional in its anchor; the projection at `d = 1` doesn't identify
  `D.H 1` with the actual Hilbert class field. The unconditional zero datum
  for its bare norm relations is in `RC/PrintsArith/Heegner.lean`.
- VERIFIED (base source): the existing rational modular function field and
  meromorphic q-expansion realization can be reused. They don't specialize
  at the normalized branch for a given `cmPoint`. The existing reciprocity
  statement for functions regular on the whole upper half-plane cannot be
  applied directly to Weierstrass coordinate functions with poles.
- VERIFIED (consumer audit): the unrestricted rank-zero adapter alone rules
  out a pole-only replacement. The old trace predicate rules out CM target
  lattices, which the unrestricted forward-rank premise does not exclude.
- SPECULATIVE (reading targets, locators UNVERIFIED): Gross 1984, §3, or
  Shimura 1971, Chs. 5–6, for conductor-one CM reciprocity; Gross–Zagier
  1986, Ch. V, or Gross 1984, §5, for the separate conjugation sign and
  cusp correction. No new leaf is rated.
- Sizing verdict: scoped stop. Keep the actual CM evaluation comparison
  and the normalized modular parametrization comparison separate. At
  least two unproved comparisons survive the proposed reading. Do not
  collapse them into a hypothesis that gives the analytic CM image.
