# Shimura analytic point dictionary

**Complete.** `ShimuraPointDict.existsUnique_atTau` proves that every
upper half-plane parameter determines a unique complex point satisfying
the fixed `AtTau` predicate on each model in the proposition. The two
inputs for the existing assembly are `ShimuraPointDict.x1TauPoints`
and the per-model `ShimuraPointDict.atTau_unique`. The
`constOnTauPoints` input is also proved.

The proof takes the valuation of finite meromorphic limits in the
model's function field, centers it by properness, and compares the
limit map with the stalk and section evaluations. Separatedness gives
uniqueness. The comparison includes the exceptional Weber parameters.

All four new Lean modules and the scratch interface check compile.
The 40 theorem axiom checks report only `propext`, `Classical.choice`,
and `Quot.sound`. Only new files were added; nothing was folded and
no leaf was added. See [the report](../docs/research/shimura-point-dict.md)
for the statements and manuscript audit. No new source error was found;
the prior audit's misprint on Shimura p. 526 is outside this proof.

The two orbit counts remain the inputs for the coprime and good-prime
power action laws. Once those laws are supplied, the compiled theorem
`ShimuraPointDict.shimuraHeckeRelations_of_compositeActions` gives the
unchanged `ShimuraSteps.ShimuraHeckeRelations`.
