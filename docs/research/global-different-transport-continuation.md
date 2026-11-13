# Concrete global different localization: continuation addendum

Date: November 13, 2026. Status: preliminary proof contribution, not an independent
review, Astra acceptance, controller acceptance, or release. The contributor's
serving model identity is unknown.

This addendum preserves the original fourteen-module packet and its research note
unchanged. The original note's SHA-256 is
`f49b5c35c3191c62a3522cb958ed4877f05223c2b18a04e2f4349ad8581c349e`.
The new work closes concrete applications and the fixed-field scaffold that the
original note accurately left unfinished. It does not relabel the historical
working-prefix checks as final candidate validation.

Repository base: `a5937595cde3e3db00975b81e5171cdef92c801a`.
Lean: `4.35.0`, compiler revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
No compiler pin, package, root, target, registry, checker, manuscript, or acceptance
record is changed. No commit, push, PR, or landing is supplied by this contribution.

## Concrete number-field localization

For number fields `K ⊆ L`, a prime `q` of `𝓞 K`, and the same base submonoid
`T = q.primeCompl`, the new theorem
`GlobalDifferentTransport.NumberFieldLocalization.map_differentIdeal_eq`
proves the genuine identity

```lean
(differentIdeal (𝓞 K) (𝓞 L)).map
    (algebraMap (𝓞 L) (Localization (Algebra.algebraMapSubmonoid (𝓞 L) T))) =
  differentIdeal (Localization T)
    (Localization (Algebra.algebraMapSubmonoid (𝓞 L) T))
```

The full parameters are only the number-field/field structures, `Algebra K L`,
and `q.IsPrime`. There is no desired different-image equality, local integral
closure, `Fact` containing a comparison, or uniqueness premise. The extension
localization may be semilocal.

`CanonicalLocalization.lean` constructs the actual localized embeddings into the
original fraction fields using `IsLocalization.lift`. It proves their agreement
on global elements, their commuting square with the simultaneous localization
map, and the resulting scalar towers. `NumberFieldLocalizationDifferent.lean`
instantiates the original trace-dual/different supplier with those exact maps,
not with caller-supplied algebra structures. Localized integral closure is derived
by the original proved `IntegralClosureLocalization` supplier.

`NumberFieldPrimeLocalizationDifferent.lean` proves the corresponding genuine
single-prime equality and coefficient identity under the explicit structural
intermediary condition `Ideal.primesOver q (𝓞 L) = {P}`. The algebra is the actual
`Localization.AtPrime.algebraOfLiesOver q P`. The proof derives the required
same-base-submonoid localization using the proved unique-prime supplier; it does
not infer local finiteness in the split case. All prime-power tests of the mapped
ideal, including exponent zero and the zero ideal, are preserved by localization.

## The actual decomposition fixed field

For a finite Galois number field `M/ℚ` and an actual nonzero integer prime `P`, put

- `D = MulAction.stabilizer Gal(M/ℚ) P`;
- `F = M^D`, using the actual `decompositionFixedField`;
- `qF = P.under (𝓞 F)`.

`DecompositionFieldDifferent.lean` applies the single-prime comparison with its
uniqueness condition **proved**, not added as a premise. It identifies the actual
local different of `(𝓞 M)_P/(𝓞 F)_qF` with the mapped relative global different.
The original `FixedFieldLocalization` proofs supply the unique prime, genuine
local finiteness, nonzero contractions, and `qF`'s `e = f = 1` over `ℤ`.

Global different transitivity then identifies the local relative coefficient
with the coefficient of the genuine absolute different `differentIdeal ℤ (𝓞 M)`.
The base factor is removed because the **actual** `qF` is unramified and therefore
does not divide `differentIdeal ℤ (𝓞 F)`. The coefficient of its mapped ideal at
`P` is consequently zero. This is a global ideal argument, not a completion
identity. The source is instantiated at `ℤ/ℚ` explicitly; `𝓞 ℚ = ℤ` is not silently
substituted.

## The nongalois F/E/U scaffold is proved for the actual presentation

Let `H` be any subgroup of `Gal(M/ℚ)`; no normality of `H` is assumed. Define

```text
L  = M^H
H0 = D ∩ H
E  = M^H0
I  = P.inertia Gal(M/ℚ)
U  = M^(I ⊔ H0)
```

Every field is an actual `IntermediateField`, and all inclusion algebras and
scalar towers are constructed. `FixedFieldTransport.lean` proves `E = L ⊔ F`.
It proves that `qE = P ∩ 𝓞 E` has global ramification index and residue degree
one over `𝓞 L`, including when `L/ℚ` is nongalois.

`FixedFieldPrimeInvariants.lean` reads the actual Galois correspondence on
integer-ring elements and ideals. Its pullback equalities identify the actual
inertia and stabilizer over `M^H` with the intersections with `H`. Their orders
compute the genuine ramification index and local-degree product using pinned
Mathlib Hilbert theory. The E/L identities follow by comparing these
intersections and cancelling positive **proved** tower invariants. An abstract
isomorphism with the right order would not establish the required action.

`FixedFieldUnramifiedFactor.lean` proves `U = E ∩ M^I`, unramifiedness of the
selected U-prime over F, and residue degree one of the selected E-prime over U.
Inertia is proved normal **inside D**, not falsely normal in the whole global
Galois group. The finite subgroup product identity is proved there and transported
through D's injective subtype map. No cyclic-quotient or completion assumption
is needed for these conclusions. Normality or Galoisness of U/F is not asserted
as an extra supplier.

Uniqueness at the actual decomposition-field prime descends to E and U through
the proved integral-tower supplier. The E/U unique-prime property follows from
these actual contractions, not from the unrelated original L-prime fibre.

## The original absolute different is the actual localized coefficient

`FixedFieldDifferentTransport.lean` proves, with no additional comparison or
uniqueness hypothesis,

```lean
let A := Localization.AtPrime qF
let B := Localization.AtPrime qE
let _ := Localization.AtPrime.algebraOfLiesOver qF qE
multiplicity (IsLocalRing.maximalIdeal B) (differentIdeal A B) =
  multiplicity (P.under (𝓞 L)) (differentIdeal ℤ (𝓞 L))
```

Here `L = M^H`, `F = M^D`, and `E = M^(D ∩ H)` are exactly the fields above.
The only substantive presentation hypotheses are `M` a number field,
`IsGalois ℚ M`, `P.IsPrime`, and `P ≠ ⊥`; `H` is arbitrary.

The connecting derivation has three separately proved steps:

1. E/L is unramified at qE and has index one. Global different transitivity and
   genuine mapped-ideal multiplicity preserve the original L/ℚ coefficient.
2. F/ℚ is unramified at qF. Global transitivity removes the absolute base factor
   at qE and identifies the absolute E/ℚ coefficient with the relative E/F one.
3. Canonical single-prime localization of E/F identifies that genuine relative
   ideal with `differentIdeal A B`, and preserves its coefficient.

`NumberFieldLocalRamification.lean` proves the concrete localized maximal-ideal
ramification index equals the corresponding genuine global index. It explicitly
identifies the actual local image ideal with localization of the globally mapped
prime. No local module-finiteness premise is required for that generic index
comparison. The F/E case then has the original L/ℚ ramification index.

## The actual finite DVR factor supplied to the arithmetic owners

Put

```text
A  = (𝓞 F)_qF
U0 = (𝓞 U)_qU
B  = (𝓞 E)_qE
```

`FixedFieldLocalTower.lean` supplies the actual `algebraOfLiesOver` maps and proves:

- A, U0, and B are DVRs after proving each contracted prime nonzero;
- U0/A, B/U0, and B/A are genuinely finite modules;
- all maps are local and faithful, and the whole A/U0/B scalar tower commutes;
- U0/A is formally unramified and unramified at its actual maximal ideal;
- the **literal actual map** `(IsLocalRing.residue B).comp (algebraMap U0 B)` is
  surjective, not merely an abstract residue-field isomorphism;
- B/A's actual different coefficient and ramification index are those of the
  original L/ℚ prime.

The residue-surjectivity proof uses `Ideal.inertiaDeg_eq` on these very canonical
localizations, the proved E/U residue degree one, and the fact that a degree-one
field extension is spanned by one. Its output is the exact reduction of the
actual inclusion needed by a uniformizer-generation or given-factor argument.

`FiniteNormalFractionField.lean` and `FixedFieldLocalFractionFields.lean` discharge
additional structural inputs: actual characteristic zero, finite and separable
canonical fraction-field extensions for all three maps, their whole fraction-field
scalar tower, and `IsIntegralClosure B U0 (FractionRing B)` (also the base/factor
and base/upper integral closures). The upper ring's normality and the finite
integral extension prove integral closure; a desired different identity is not
an input. Cofinality of base nonzero denominators is proved using Mathlib's
existing algebraic denominator-clearing theorem.

The supplied raw tower matches the structural hypotheses of the existing
given-factor DVR interface.
This contribution does not duplicate the other authors' uniformizer generation,
rank/ramification degree, monogenic different, derivative, Hilbert counting, or
Serre inequality proofs. It does not construct a contributor-specific subalgebra
wrapper or a registered global proof provider.

## All exponents and the exact successor test

`FixedFieldLocalDifferentPowers.lean` proves, for **every** natural `n`,

```lean
IsLocalRing.maximalIdeal B ^ n ∣ differentIdeal A B ↔
  (P.under (𝓞 L)) ^ n ∣ differentIdeal ℤ (𝓞 L)
```

Both actual differents are proved nonzero, so finite multiplicity is established
on both sides before converting the coefficient identity into all power tests.
The local ideal is the **genuine different of B/A**, not only a mapped ideal.
The zero exponent is included. The same module preserves the exact
nondivisibility test at `n + 1`; it does not shift the bound or silently remove
the successor.

## Source-to-consumer and scope checks

The old and new proofs use the same pinned compiler and Mathlib revision. The
actual canonical maps, not unrelated algebra structures, are consumed downstream.
Fields and integer rings are never identified solely through a similar theorem
name. Integral statements are not inferred from a field tensor-product statement.
Every chosen-prime finiteness application has a proved unique-prime fibre.
The original split-prime counterexample to finiteness over `ℤ_(p)` remains valid;
the correct finite base here is `(𝓞 F)_qF`.

All allowed primes, including 2, and trivial-field/subgroup cases are covered.
P = zero is excluded only for the DVR/finite-natural-multiplicity conclusions
where it matters; the generic simultaneous localization statement admits any
prime. Ramification cancellations use proved positivity. No completeness or
Henselianity of A, U0, or B is a hypothesis of the localized route.

The following duties remain separate:

- Translating an externally supplied arbitrary number field and prime into this
  actual finite-Galois `M^H` presentation, and proving the ring/prime/different
  identifications for that wrapper, are not supplied here.
- Uniformizer generation, degree comparison and local arithmetic remain their
  owners' work. No registered T20/T21 provider is supplied by this lane.
- A localization decomposition-group map for any local Hilbert assembly must
  have its actual action/filtration comparison checked. The original completed-
  integer decomposition equivalence is retained as its separately verified scope.
- The original **completed-different** identity remains unproved by this packet.
  It is not used to justify the newly proved actual **localized-different** route.
- Full assembled-candidate CI, independent source coverage, designated Astra
  review and publication are not replaced by producer compilation or scoped replay.

No earlier verdict is overwritten or relabeled. The old note remains historical
at its stated scope; this addendum records which new connecting arguments are now
proved and which global-assembly duties it does not perform.

## Verification

Final same-source verification passed for all **13 continuation modules**
(**1,945 source lines**), together with scoped replay of the **27-module combined
packet** (**3,930 source lines**). The original fourteen source hashes and the
original note hash were identical before and after the checks.

- Fresh continuation-output compilation, with dependencies and frozen outputs
  cached: **56.858 seconds**.
- Same-source warm recompilation: **57.935 seconds**.
- Combined scoped kernel replay and full declaration-body axiom closure:
  **35.190 seconds**, **344 declarations**, 344 raw declaration occurrences,
  and no duplicate theorem bodies.
- Only `propext`, `Classical.choice` and `Quot.sound` occur in the complete
  used-constant closure of the new and frozen producer declarations.
- There were 18 style warnings per compilation pass and no compilation errors.
  The warning counts and exact diagnostics are retained in the verification log.
- The source lexical guard found no new axiom, `sorry`, admitted proof,
  `native_decide`, or owned unsafe/partial proof declaration.
- All 27 source hashes were unchanged throughout both compilation passes and
  replay. No package, pin, root, target, registry, checker or manuscript source
  was modified.

Every compiler and replay command used the supplied four-command resource gate,
with at most one compiler process in this lane and two Lean threads. The temporary
verifier replays actual serialized producer declaration bodies and walks their
actual dependencies; it changes no repository checker or protected policy.
External Mathlib/base declarations are imports, not part of this scoped replay.
This is not a cold dependency build, full-root audit, independent review or
protocol acceptance. All acceptance fields in the verification records are false.

The packet includes the portable verifier as `verification/ContinuationReplay.lean`
and exact bindings/timings in `verification/continuation-verification.json`.
It must be run in a pinned checkout with the supplied proof-resource gate applied
to the normal Lean commands. Machine-specific gate paths are intentionally not
part of this public note.

### Final continuation source bindings

Paths are relative to `ZInQKernel/Contrib/GlobalDifferentTransport/`.
The original fourteen bindings are retained unchanged in the verification record.

- `CanonicalLocalization.lean`: `f27e7ba1de97834a41b7729876469b521d01249efe7865e0cff1f73ff3d9323f`
- `NumberFieldLocalizationDifferent.lean`: `7cf1a0178025f96cd5c2fcaaadd7d7ced0c96aa65fb19d970a9a84bd3f3fdb51`
- `NumberFieldPrimeLocalizationDifferent.lean`: `933069e7582c7df2b1df7cb21dc1d9a9c172b097047270d3532802fda171427a`
- `DecompositionFieldDifferent.lean`: `6acf62d40360fd6e0bc93554148d8dc5bd3a15a7e0579f077155c33112226762`
- `FixedFieldPrimeInvariants.lean`: `bc7a6f4d625577997a5b0f372165bca00b0cbed9d2d70e410ed82855bab0c60e`
- `FixedFieldTransport.lean`: `480473df64678fedc35a295dc1148e846092c8447833b419aef729a6d4ea5dd8`
- `FixedFieldUnramifiedFactor.lean`: `cb154a26757d59ba957a2f066ef57ad801b2932cfebffea34453bd18a5913de5`
- `FixedFieldDifferentTransport.lean`: `810bffa0f4f418d11e0669902fc7a208d2a8e05e3bc3069089475f35ceb9a0bd`
- `NumberFieldLocalRamification.lean`: `9ef20878edaf0b72160c92b729439f110e71bef43c0b5ea6f197d8c117113707`
- `FixedFieldLocalTower.lean`: `ba1c4c8d7cb393f80a0e6209964d91a3d6fec80a69b0383d5f20f2150c5c0b74`
- `FiniteNormalFractionField.lean`: `ced22e1c8c8fbacf3f318bc54e25304fb88f77d3ae04129d7190c7b6140d994b`
- `FixedFieldLocalFractionFields.lean`: `d73bf8460b94147a00c34e9db41c183026678c17b099d8c027ae5f6e5fc34b8d`
- `FixedFieldLocalDifferentPowers.lean`: `5fc25e167d603c13ce26ea64b59958a7c60557fd469d31649fc7401d7ddc31d9`

### Failed attempts and repairs retained as history

The continuation journal preserves the initial unsuccessful compiler rounds and
source edits; they are not counted as final candidate validation. The mechanisms
were specific elaboration/compatibility problems:

1. Section variables used only in a proof body were pruned from declaration types;
   actual nonzero-prime premises were made explicit with `include` rather than
   fabricated as assumptions of the desired comparison.
2. Some 4.35 constants are in older namespaces or monolithic modules. Their actual
   source declarations were read before correcting names and imports.
3. Deep coercion normalization in the subgroup-cardinality proof exceeded the
   heartbeat budget. An explicit subtype equivalence replaced that route; the new
   proof body, not an axiom or a larger unreviewed port, was checked.
4. A dependent-prime rewrite in unramifiedness was not type-correct. Unramifiedness
   was derived again from the actual plain ramification-index-one equation and
   Mathlib's criterion, not by pretending two dependent instances were definitionally
   equal.
5. Local scalar-tower instance search exceeded its budget. The actual canonical
   localization-map composition was proved explicitly using the universal-property
   and composition suppliers.
6. The characteristic-zero transfer initially omitted a narrow import and the
   explicit ring-homomorphism `map_one` proof. It now uses the actual injective
   additive map with that proof, with no change to ring definitions or compiler pins.

The earlier false split-prime finiteness route remains rejected. No failed attempt,
compiler success, or author-generated record is an independent acceptance.
