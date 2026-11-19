# Results log

- Input convention: `IsXi` uses `γ_a ((a τ + b)/(n/a))` with the lower-right residue `a`; `IsDiamond` uses the same entry.
- Verified by Lake: `exists_reduce`, `reduce_unique`, `sumAt_covariant`, `sumAt_invariant`, `diamond_independent`, `sumAt_lifts`, `coprime_count_basis`.
- Coprime reindexing: divisor split by gcd; offsets `(a*e+b*f) % (d*f)`, with injectivity first modulo `f` and then modulo `d`.
- Good-prime reindexing: the last lower block has denominator 1; every other lower block reduces by scalar `p` and offset modulo the reduced denominator. `scalar_block` verified by Lake.
- Local package cache: `lean/.lake` was missing from the copied build. Lake restored `ZInQ.PoleValuation`, `ZInQ.NumericalTowerBounds`, and `ZInQ.ExplicitCutoffBounds` as dependencies.
- Open analytic input: `PointDictionary`; `HeckePin.X1TauPoints` is its existence half. `WeberField` provides the analytic extensions; restricted valuation, punctured limit, and stalk/residue comparison are pending.
- Verified by Lake: `good_count_basis`, `isXi_mul_coprime`, `isXi_good_step`, `shimuraHeckeRelations_of_pointDictionary`, and `shimuraThm1Af_of_printed_pointDictionary`.
- Build: `lake build +ZInQKernel.Contrib.OneProof.ShimuraOrbits` completed (12,942 jobs, including replayed imports).
- Axiom scan: 47 new theorems; every entry reports exactly `propext`, `Classical.choice`, `Quot.sound`.
- Focused `#discharges`: prior composition assumes `ShimuraThm1AsPrinted` and `ShimuraHeckeRelations`; new composition assumes `ShimuraThm1AsPrinted` and `PointDictionary`.
- No leaf, fold, or edits to existing files.
