# Standalone all-level prime-Hecke rationality

`BridgeHeckeClosure.heckePrimeIntegralToRational` proves the unchanged predicate
`CoeffRational.HeckePrimeIntegralToRational` from
`ZInQKernel/Contrib/OneProof/CoeffRational.lean:69–74`, with no additional hypothesis.
It covers every nonzero level, integer weight at least two, actual Gamma-one cusp
form, prime away from the level, integral input coefficients, and rational output
coefficients for the original `diagCosetGamma1` slash endomorphism at every index.

## Proof

The twelve prerequisite modules construct the actual torsion orbit, its nonzero
Vandermonde-square level-one denominator, localized generation, level-one rational
spanning and coefficient-conjugate forms, and saturation of formal coefficient
fields without assuming a nonzero constant term.

Four bridge foundations derive cyclotomic coefficients of the denominator at
period one, construct the actual nonzero conjugate denominator, prove the raw
axis/diamond/Galois-unit laws, and derive finite same-weight field coordinates
using every Fourier row.

Three final modules keep the same coordinates throughout numerator transport,
coefficient conjugation and diamond transport. Cancellation uses the nonzero
power series of the conjugate denominator; it does not assume that denominator
equals the original one. Every coefficient is fixed by the full cyclotomic Galois
group and therefore rational. The actual prime-Hecke recurrence gives the target;
levels below three use the earlier concrete result through level six.

No rational basis, spanning premise, arithmetic model, supplied diamond closure,
pointwise automorphism of complex analytic values, or analytically divided form
is introduced.

## Verification and scope

Nineteen mathematical modules, 2,703 lines, and 175 named source declarations
were independently recompiled with the pinned Lean 4.35.0 toolchain and warm
imports. The seven bridge modules additionally have 71 unique type/axiom checks
and eight root-qualified literal examples, including the exact predicate and its
fully expanded original contract. The recorded axiom closures use only subsets
of `propext`, `Classical.choice`, and `Quot.sound`. Failed editions, warnings and
raw outputs are retained. Complete separate mathematical source reviews cover
the prerequisites, foundations, final closure, and independent exact-contract
integration.

This is ordinary pinned verification, not cold/native admission, Source/BASE
enrollment, or assembly adoption. It does not prove all-form integral Hecke
output, an integral basis, principal-product spanning, or the full Z-in-Q result.

**This is a standalone classical contribution.** The current proof chain already
obtains `DSCoeffExt.EigenformCoeffFieldFinite` from the Tau Ceti coefficient-field
fold (`EigenformCoeffFieldFiniteProof.lean`, used by the TailZ74 reroute). The
Hecke and integral-basis leaves are no longer current `frozenTarget` hypotheses.
Accordingly, this contribution is not claimed to reduce the current open-hypothesis
list. Original statements, assembly, pins, and published proof history are unchanged.
