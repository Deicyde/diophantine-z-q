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
- VERIFIED (build audit): the first HKGZ dependency invocation picked the
  original Lean binary despite using `LAKE_OVERRIDE_LEAN`. The worker
  lock was invoked for toolchain detection only. The aggregate worker
  time (790.6 seconds in under five minutes) confirms overlap. The
  invocation was stopped. This violated the single-worker constraint.
  The correction selects a temporary toolchain directory whose
  `bin/lean` is the locking wrapper, and confirms the selected binary
  with `lake env printenv LEAN`. Both the entry script and the active
  worker check the stated load and memory thresholds. The working
  directory, sources, and dependency manifest are unchanged.
- VERIFIED (Lean): the assembly dependency target built successfully
  after reusing a local cache from the identical Lean sources, toolchain,
  and package manifest. No network access was used. The final module
  passed both its standalone `lake env lean` check and Lake module build.
- VERIFIED (Lean): the first scratch run reached the exact
  `IsHeegnerTrace` boundary but hit a definitional equality error in
  the Hilbert specialization. Making the coordinate equality
  instances parameters of the generic lemma lets the specialization
  use the same instances as the existing point maps.
- VERIFIED (Lean): the final `lake env lean` run on `Substitution.lean`
  passed. `axioms-output.txt` lists the five checked theorems; all depend
  only on `propext`, `Classical.choice`, and `Quot.sound`. The
  forward-rank assembly beyond the trace is a source dry run.
