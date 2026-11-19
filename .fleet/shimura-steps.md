# Shimura 1973 Theorem 1: scoped stop at uniqueness

Steps (1) and (2) compile in `ZInQKernel/Contrib/OneProof/ShimuraSteps.lean`
given the composite Hecke operators on the same Jacobian and their laws. The
saturated annihilator and the kernel's I_f have the same scheme-theoretic image
family; their quotient universal properties agree. Two distinct Dirichlet
primes in each unit class give integral reverse generation by Bézout. The
coefficient laws then extend the prime and good-square intertwining tests to
every positive index.

For step (3), every competitor kills I_f J and factors through the constructed
quotient. `SameDimSurjectiveFinite` is the remaining geometric input: a
surjective homomorphism of equal-dimensional abelian varieties over ℚ is finite.
With it, the competitor's connected-kernel criterion turns the induced map into
the required isomorphism. `ShimuraHeckeRelations` separately names the missing
composite Jacobian action and its dictionary. The p. 526 conjugate-form misprint
is recorded in the report; it is outside the formalized clauses.

The reduction from the print form and these two GLUE inputs compiles. All 39
axiom checks use only the standard axioms. The stock `#discharges` command
matches the exact field type in the focused harness; the full assembly cache
predates the base and the full check was not run. The fold dry run rejected
5 LEAF / 24 GLUE → 6 / 25 in both counts. No fold was made. See
`docs/research/shimura-steps.md` for the source audit and
`scratch/shimura-steps/` for the checks and candidate spec.
