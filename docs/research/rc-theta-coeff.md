# Genuine theta coefficients for the trace model

For one actual stage and a fixed finite pool of good primes, this lane connects the lifted theta coefficients and the constituent trace model. The analytic assertion at tex 9647–9654 that the indicated blocks have weight two and belong to the span of the chosen constituents is an ELLIOT (uncited) input.

## Known issues

- Tex 9660–9668: integrality of a good Hecke image does not by itself show that it lies in the module spanned by diamond translates. Close the generating set under both good Hecke and diamond operators, then use the finite Fourier-coordinate injection to establish finiteness for that module.
- Tex 9649 specifies a finite constituent space for fixed stage and set. The bounded cardinality of the sets does not give a finite union of level primes across all such sets. The finite pool in this lane gives a local family for a fixed set and its subsets (or any fixed finite collection of sets); it does not produce a simultaneous finite constituent space for every bounded good set.
- Existing constructor mismatch (tex 9745–9750): `buildConstituentModel` uses one `avoid` for both the good-operator tests and stationary Kummer support. The common-level good tests must omit the added level primes, but the text detects radicals at those primes using the added bits, separately from the stationary type. Adding a genuinely fresh prime to stationary `support` generally contradicts its independent bit. The coefficient construction keeps the good-test avoidance; the inherited `hlevel` and stationary radical condition remain explicit at the call site. An application to the manuscript's nonempty configurations needs a constructor with unramifiedness/support local to the active forms.
