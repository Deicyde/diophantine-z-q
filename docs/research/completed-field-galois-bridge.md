# Completed-field Galois and canonical padic-base transport

Date: November 13, 2026. Status: preliminary proof contribution, not independent
review, designated Astra acceptance, controller acceptance, or an official record.
The contributor's serving model identity is unknown.

This is an **additive field-model bridge**. The prior 27 transport source files,
their historical notes, and their existing evidence artifacts are unchanged.
The repository base is `a5937595cde3e3db00975b81e5171cdef92c801a`; Lean is 4.35.0
at compiler revision `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Mathlib is
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
No package, compiler pin, root, registry, checker, policy, manuscript, or protected
acceptance record is edited. No local Kronecker–Weber theorem or global
Kronecker–Weber conclusion is a premise or a result of this bridge.

## Exact input and output objects

The affine base is the literal `ℤ/ℚ` model. The extension affine ring is the actual
`NumberField.RingOfIntegers L`.

```lean
L : Type*
[Field L] [NumberField L]
v : IsDedekindDomain.HeightOneSpectrum ℤ
w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)
[w.asIdeal.LiesOver v.asIdeal]
```

The completed fields are exactly `v.adicCompletion ℚ` and `w.adicCompletion L`.
The algebra between them is the existing proved `completionAlgebra` in scope
`GlobalDifferentTransportCompletion`. Its actual map is
`completionRingHom ℚ L v w`, and the completed integer map is
`completionIntegersRingHom ℚ L v w`. The original scalar and valuation squares
are consumed without being redefined.

The new files are:

- `CompletedGalois.lean`
- `CompletedDecomposition.lean`
- `CompletedAbelian.lean`
- `PadicCompletionModel.lean`
- `PadicRamification.lean`

They are under `ZInQKernel/Contrib/GlobalDifferentTransport/` and retain the public
namespace `GlobalDifferentTransport`.

## Genuine completed Galoisness

`isGalois_numberFieldCompletion L v w` proves

```lean
[IsGalois ℚ L] → IsGalois (v.adicCompletion ℚ) (w.adicCompletion L)
```

on that actual algebra. There is no assumed completed normality, local degree,
cardinality identity, special field-model default, or desired Galois `Fact`.

The derivation is:

1. Pinned Mathlib supplies a **separable global splitting polynomial** for the
   actual finite Galois extension `L/ℚ`.
2. Its image over the actual completed rational base splits in the actual
   completed target, by the proved scalar squares and the global field embedding.
3. The completed root-generated subalgebra contains the entire actual global
   field image. This is the actual splitting-field range theorem, not an analogy
   between similarly named fields.
4. The immutable `moduleFinite_numberFieldCompletion` result makes this generated
   subalgebra finite-dimensional and closed. The actual global field image is
   dense, so the subalgebra is the whole completed field.
5. The resulting genuine separable splitting-field structure proves completed
   normality and separability, hence Galoisness.

A dense field image alone would not imply algebraic generation. The
finite-dimensional closure step is explicit. This avoids the substantially
larger local-degree/cardinality route of the referenced decomposition-group port.
The global ring of integers is not assumed monogenic.

## Actual field decomposition equivalence

Let

```lean
D := MulAction.stabilizer Gal(L/ℚ) w.asIdeal
```

`decompositionFieldMulEquiv L v w` proves

```lean
[Normal ℚ L] → D ≃* Gal(w.adicCompletion L / v.adicCompletion ℚ)
```

The weaker global-normality hypothesis suffices for this equivalence. The forward
function is **exactly the immutable** `decompositionFieldHom`; the inverse is
**exactly the named** `decompositionOfCompletedFieldAut`. This is not just an order
comparison or an unrelated isomorphism.

For an arbitrary actual completed-field automorphism, the inverse performs the
normal global-field restriction. It then proves membership in the selected
stabilizer:

- The actual global prime is precisely the set of global integers whose actual
  completed images have powers tending to zero.
- This uses the existing normalized valuation, its exact global-integer
  restriction, and Mathlib's norm-less-than-one/power-convergence criterion on
  the **same** completed topology.
- The completed automorphism is continuous by the already-proved finite
  completed extension. Continuity carries those powers to zero.
- The same argument for the inverse automorphism reflects membership in the
  global prime.

No valuation preservation of arbitrary field automorphisms is assumed. In
particular, no falsely isometric base-field normalization or spectral field model
is introduced. `valued_completedFieldAut` is proved **after** surjectivity from the
actual decomposition action's existing valuation theorem.

Density and continuity then recover the arbitrary completed field automorphism.
Both inverse identities and the global field/integer commuting squares are named
and proved. `decompositionFieldMulEquiv_apply` identifies the exact forward action,
and `decompositionFieldMulEquiv_symm_apply` identifies the exact inverse restriction.

## Integer/fraction compatibility

`completedIntegerFieldAutMulEquiv L v w` is an actual group equivalence between
completed-integer automorphisms over the completed base integers and completed
field automorphisms over the completed base field.

Its forward map is the original `fractionAutOfIntegerAut`, now packaged as a
proved group homomorphism. Its inverse is the actual integer restriction induced
by the proved field decomposition inverse. The field action on **every actual
completed integer** is the same action as its restriction, and both inverse
identities are proved using the actual fraction-field embeddings.

This consumes the original fraction-field/base-integer commuting square rather
than introducing an `IsIntegralClosure` or local-model assumption. All algebra,
field, and integer types are the concrete original completion types.

## Native abelian-Galois interfaces

`CompletedAbelian.lean` uses the native pinned Mathlib `IsAbelianGalois`, not a new
contributor-specific class. It proves:

- `isMulCommutative_numberFieldCompletion`: commutativity of the actual completed
  field automorphism group from commutativity of the actual global group;
- `isAbelianGalois_numberFieldCompletion`: native `IsAbelianGalois` on the actual
  completed extension from native global `IsAbelianGalois ℚ L`.

Commutativity is transported through the **proved actual group surjection**.
The completed Galois instance is the separate splitting-field proof above.
The scoped exports are in `GlobalDifferentTransportCompletedGalois`.
No nongalois different/Serre producer is changed or strengthened with a new global
Galois hypothesis.

## The rational completion is actually identified with Qp

Pinned native `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean` supplies, directly
at the affine base `R = ℤ`,

```lean
Rat.HeightOneSpectrum.adicCompletion.padicEquiv v
Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v
```

These are continuous `ℚ`- and `ℤ`-algebra equivalences to
`ℚ_[Rat.HeightOneSpectrum.primesEquiv v]` and its integer ring. Their exact forward
and inverse inclusion squares are proved in that supplier (183–197). Its
construction establishes equivalent valued uniformities; it does not identify
unrelated norms by an unsupported `rfl`.

`PadicCompletionModel.lean` names these actual native maps and defines

```lean
completionPrime v := Rat.HeightOneSpectrum.primesEquiv v
```

Only the native prime-tag `Fact` is synthesized, from the proved `Nat.Primes`
property. It contains no Galois, comparison, or local-model assertion.

The native integer equivalence uses `Ring.toIntAlgebra`, whereas the immutable
completed-integer affine model has its canonical `ℤ` algebra. These presentations
are **not treated as definitionally equal**. The same native ring equivalence and
homeomorphism are extracted under the native algebra and re-bundled with the
actual canonical integer algebra. Its integer-cast commutation is proved. The
underlying maps and both inclusion squares remain the native maps, not newly
chosen isomorphisms.

The named Qp and Zp scalar maps are the native inverse equivalences followed by
the existing canonical completion maps. Their exact map identities and all
rational/integer/field scalar squares are proved. The resulting finite Qp field
extension and continuous scalar action are derived, not assumed.

The scoped model is `GlobalDifferentTransportPadicCompletion`. It is a named,
proved base change, not a special field-model default. It supplies genuine native
Galois/abelian-Galois results on the same target field over that Qp base, and
`decompositionPadicFieldMulEquiv` preserves the exact original global action.

Neither `𝓞 ℚ = ℤ` nor an isometric normalization is silently substituted.

## The unchanged global ramification theorem is consumed

`PadicRamification.lean` proves the exact maximal-ideal image and contraction
through the native completed-base-integer/Zp equivalence. Consequently the actual
completed-ring ramification index is preserved by this integer-base change.

The resulting theorem

```lean
ramificationIdx_padicNumberFieldCompletion_eq L v w :
  (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
      ℤ_[completionPrime v] = w.asIdeal.ramificationIdx ℤ
```

then consumes the immutable `ramificationIdx_numberFieldCompletion_eq` unchanged.
Its original global/adic multiplicity argument is not duplicated. This
normalization theorem requires no global Galois hypothesis.

The precise ideal used for the base-change comparison is identified before
applying ramification/multiplicity. A bare topological field isomorphism would
not suffice for that application.

## Source and exception checks

The relevant pinned native suppliers were read at their actual proof bodies:

- `Mathlib/FieldTheory/Galois/Basic.lean`: separable splitting fields and Galois
  tower restriction;
- `Mathlib/FieldTheory/SplittingField/IsSplittingField.lean`: the actual
  splitting-field range and scalar-map identities;
- `Mathlib/Topology/Algebra/Valued/NormedValued.lean` and
  `Mathlib/Analysis/SpecificLimits/Normed.lean`: the actual valued norm and
  power-convergence criterion;
- `Mathlib/FieldTheory/Galois/Abelian.lean`: the native class and commutativity
  transport;
- `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean`: the actual affine
  rational/padic equivalences and both integer/field inclusion squares.

The older Tau Ceti decomposition source was inspected rather than assumed to
match the current pin. Its cardinality/local-degree route was not imported or
used as a premise here.

All rational primes, including 2, and trivial global extensions are within the
actual quantified source types. No odd-prime condition, nontrivial automorphism,
nontrivial extension degree, or monogenic integer-ring condition is introduced.
The new field bridge has no exponent parameter; the old zero-exponent/zero-ideal
transport is separately retained under the additive imports.

Focused controls check the literal affine `ℤ/ℚ` model without identifying `𝓞 ℚ`,
the trivial rational global extension, native rational prime 2, the normal-only
field decomposition inverse, and the retained zero-exponent/zero-ideal comparison.

## Remaining scope and acceptance boundary

This bridge supplies completed Galoisness, the actual field decomposition group,
integer/fraction compatibility, native abelian transport, and the actual Qp/Zp
base maps and normalized ramification. It does not prove local or global
Kronecker–Weber, a global compositum/conductor endpoint, a manuscript theorem,
or a registered global provider. It does not invent a normed-algebra isometry,
spectral norm, or additional local-field-model predicate. Any such predicate
required by a later arithmetic consumer must still be checked against that
consumer's actual constructed objects and proved source inputs.

## Failure history and corrected application scope

All unsuccessful compiler rounds remain in the contribution journal. They are
not counted as final candidate validation. The changes stayed inside new additive
sources or temporary controls:

- An attempted direct reuse of the native integer `ContinuousAlgEquiv` failed
  because its `ℤ` algebra was not definitionally the canonical affine one. The
  same native ring map and homeomorphism were extracted under their own native
  algebra, then re-bundled with proved integer-cast commutation. Both directions
  of the inclusion square, the actual scalar maps, and their Galois/ramification
  applications were rechecked together. No equality was installed as a `Fact`.
- Direct coercion rewrites in the power-convergence/global restriction proof
  did not expose the needed actual map. The immutable normalized global-integer
  valuation theorem and explicit function-composition form were consumed
  instead; the mathematical restriction/stabilizer proof was not weakened.
- A local-hom instance on the re-bundled integer equivalence was not synthesized.
  The needed exact contraction was proved by the native ring equivalence's
  maximal-ideal map/comap identity, rather than assumed as a local-model predicate.
- A focused equivalence-valued control initially lacked `noncomputable section`.
  Only that temporary test declaration was corrected. All 32 producer sources
  had already compiled before this control failure and were rebuilt for final
  same-source verification.

No old producer, historical note, package pin or review verdict was rewritten to
silence these failures. The final source bindings and verifier results refer to
the corrected current bodies, not earlier failed attempts.

## Final producer verification

The final fresh complete private prefix comprises **32 modules / 4,674 source
lines**, including **5 additive modules / 744 new source lines**. All 27 frozen
producer bindings and both historical note bindings were checked unchanged.
Every complete-prefix bitmap entry records a fresh source compilation, not an
inherited producer output counted as source evidence.

- Fresh complete-prefix source compilation: **136.467 seconds**.
- Focused repaired exception controls: **4.217 seconds**, passed.
- Combined actual serialized-declaration kernel replay and used-body axiom
  closure: **23.446 seconds**, **440 declarations / 440 raw occurrences**, no
  duplicate theorem bodies.
- Only `Quot.sound`, `Classical.choice` and `propext` occur in the complete
  used-constant closure of the selected producer bodies.
- All 32 source hashes were unchanged throughout final verification.
- The fresh prefix retained 18 historical style warnings; the same-source warm
  check of the five new sources had **zero warnings** and passed in 24.604 seconds.
- No new axiom, admitted proof, `sorry`, `native_decide`, or owned unsafe/partial
  producer declaration was introduced.

The earlier same-source fresh prefix took 158.786 seconds; it compiled all
producers before the temporary noncomputable-control error described above.
That failed control round is preserved separately and is not presented as a
passing complete verification. The repaired final round rebuilt every producer,
then passed controls and replay.

All compiler, control and replay commands used the supplied four-command resource
gate with one compiler process in this lane, `-j2`, and two Lean threads. Mathlib
and baseline dependency outputs were cached. This is not a cold dependency build,
whole-root audit, full assembled-candidate review, or independent acceptance.
All protocol/independent-acceptance fields in the verification record are false.

### New source bindings

Paths are relative to `ZInQKernel/Contrib/GlobalDifferentTransport/`.

- `CompletedGalois.lean`: `765ede7096e675f84b2564f1171e3cb7f8b26260c109ab07c9e6312505fd4823`
- `CompletedDecomposition.lean`: `469b2407c8b2e6552f15ac0ca35f5693c3c26b532c33e1de3d98f3ff4cffbf4b`
- `CompletedAbelian.lean`: `869f207fe42890696e87325612e5cd41892f5718eff52c59751ee09440426825`
- `PadicCompletionModel.lean`: `4ce858621ef303770748f426c8f53f350bd94b6edaf6b5795ed6b57a0dd11608`
- `PadicRamification.lean`: `bad0fb3b54e2ab4a777119c9f4b3ffa8ef6db15cef801b2f1d78daf135f9a023`

The private packet includes `verification/complete-prefix-verification.json`,
the portable scoped raw replay program, focused exception controls, and complete
verification logs. The existing 27 source bindings are retained unchanged in the
complete-prefix bitmap. Reproduction must use the pinned checkout and the
provided resource gate around normal Lean commands; machine-specific paths and
operational identifiers are intentionally excluded from this public-safe note.
