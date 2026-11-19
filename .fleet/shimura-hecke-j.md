# Composite Hecke operators on the Shimura Jacobian

**Scoped stop.** `ShimuraSteps.ShimuraHeckeRelations` remains open. The
new Lean modules prove the exact prime-index formula, composition of
upper representatives, and the bad-prime power formula conditional on
the point dictionary. They prove that the composite actions pin the
endomorphisms as soon as the `AtTau` points exist. This uses two test
points over the rational curve and the existing pointed Albanese
argument. The assembly by prime-power and coprime induction proves all
the required conclusions once the remaining action identities hold.

`lake build +ZInQKernel.Contrib.OneProof.ShimuraHeckeJ` succeeded. All 26
new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The
focused `#discharges` run on the exact quotient row verifies that
`shimuraThm1Af_of_printed'` still requires `ShimuraThm1AsPrinted` and
`ShimuraHeckeRelations`. No leaf or fold was added.

What remains is unique realization of `AtTau` on the given model and
the coprime and good-prime counts on `Γ₁(N)` orbit divisors. The latter
must retain the diamond factor. The report records the smallest forms
of those inputs, the proof sketches, and the manuscript check. See
[the report](../docs/research/shimura-hecke-j.md) and
[the verification](../scratch/shimura-hecke-j/).
