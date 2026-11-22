# Prepared clause 4: abstract certificate and genuine source binding

## Verification status

The corrected abstract certificate, its prime-unit equivalence, the prepared
combinatorial clause, and the genuine-source bridges have been checked. Both
library sources and their exact-prefix verification copies compile with exit
code zero and no errors or warnings. All eighteen theorem axiom reports contain
only `propext`, `Classical.choice`, and `Quot.sound`; the four genuine-source
definitions have the same axiom reports.

An explicit application of the existing `auxFactor_of_prepared`, using the
direct genuine-source seed bridge in its seed-argument position, also compiled.
Verification diagnostics are not part of the library sources. The current
genuine-source verification record is distinct from the earlier certificate
verification records, whose stage-specific statements are preserved.

## What the abstract certificate says

`PreparedUnitCertificate` is an abstract prime-unit certificate. It freely
chooses a coefficient function and an index predicate. A singleton predicate
manufactures those data from a prime-configuration unit. Its exact content is:

```lean
PreparedUnitCertificate W T A ↔
  ∀ τ : L, PreparedType W T τ →
    ∃ D : ℕ, 0 < D ∧ Squarefree D ∧ D % 8 = 7 ∧
      (∀ p ∈ D.primeFactors, T.Good p) ∧
      (primeConfig D.primeFactors T.typ).total = τ ∧
      A τ (primeConfig D.primeFactors T.typ) = 1
```

This is the proved theorem `preparedUnitCertificate_iff_primeUnits`. Neither
implication needs coefficient rules, a modular form, or an analytic theorem.
The certificate is not a specification of the actual Appendix E sources.

`PreparedEvenSourceInput` remains only as a compatibility abbreviation for this
certificate. The two earlier theorem names remain compatibility wrappers;
the primary names are `preparedSeedInput_of_unitCertificate` and
`preparedClauseFour_of_unitCertificate`. Compatibility does not restore the
earlier source-level interpretation. Earlier verification records establish
their earlier abstract theorem types, not authenticity of the chosen source.

## Prepared combinatorial clause

For each prepared type only, every unit seed is nonempty, a minimum nonempty
seed exists with the prepared total type, its internal edge bits are
irrelevant, and matching all but one seed label with a nonempty remainder gives
a contraction certificate. `PreparedClauseFour` records these assertions.

A prepared type is witnessed by a negative squarefree parameter congruent to
one modulo eight, prime to the support, with analytic order zero. Its unsigned
index is seven modulo eight and its sign coordinate is one. This coordinate is
not the elliptic curve's root number.

`preparedSeedInput_of_clauseFour` has exactly the seed-argument type of
`auxFactor_of_prepared`, for the same support, type data and symbols. The other
arguments, including the semantic partitionability implication, are unchanged.
The unrestricted phrase "every total type" at lines 10131--10132 is not proved;
the clause concerns the prepared negative sources of lines 10057,
10096--10105, and 10139.

## Genuine source binding

`PreparedGenuineEvenSource` is separate from the abstract certificate. It binds
all of the following:

- A genuine `CentralNormalization` of the fixed curve, agreeing with `W.Lstar`.
- For each prepared type, actual `EvenPhaseData` at sign minus one, with a
  nonzero same-source central reference and reference index seven modulo eight.
- Exactly the original `S0Filter`, not an arbitrary predicate or subfilter.
- The rational phase-removed coefficients and attained depth supplied by the
  existing `EvenPhaseData.minimum_sieved` theorem with empty extra sieve.
- The type-filter dictionary, fixed-`U` factorization at every budget, and
  equality of the given symbol with that actual normalized dictionary symbol.

The existing minimum theorem uses the separate, explicit premises
`WaldspurgerCor2`, the genuine `EvenLowerBound`, and continuations of the actual
quadratic-twist L-series. The same-source coefficient-square identity is
returned by that theorem. No freely chosen central-valuation function replaces
these actual central values, and no unit or seed is an input of the genuine
binding.

The proved certificate bridge is
`preparedUnitCertificate_of_genuineEvenSource`; its compatibility bridge has
conclusion `PreparedEvenSourceInput`. The direct seed bridge uses the already
attained index of the existing even minimum. It does not call the abstract
certificate's generic minimum helper. The combinatorial clause follows from
that direct seed bridge and the unchanged coefficient-rule and off-filter
hypotheses. No even minimization argument is re-proved.

All six genuine-source theorems are compiled and axiom-checked. They give a
conditional genuine-source-to-certificate and genuine-source-to-seed reduction;
they do not construct the genuine source package for the actual symbols.

## What remains

A caller must supply the genuine source data for the actual symbols: the
central-normalization agreement, prepared actual form and nonzero reference,
whole-filter type dictionary, fixed-`U` factorization, and actual-symbol equality.
The printed Corollary 2, genuine even lower bound, actual twist continuations,
and ellipticity remain explicit premises. The coefficient-rule and off-filter
hypotheses, support specification, and semantic partitionability implication
remain the unchanged auxiliary-factor inputs.

The existing even minimizer, its actual coefficient phase and square identity,
its attained index, the original squareclass filter, and the seed/anchor
bridges are verified components of this conditional reduction. No new printed
leaf, source-construction theorem, unrestricted all-type seed theorem, or
unconditional auxiliary factor is claimed. No dependency build was performed
as part of this contribution.
