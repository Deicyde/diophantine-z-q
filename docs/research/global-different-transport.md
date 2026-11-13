# Shared global-different/completion transport

**Status: preliminary proof contribution; the actual completed-different identity remains open.**
This note concerns shared transport foundations for T20 and T21, not their local
Hilbert-counting or Serre derivative arguments. The contributor is an interactive
agent whose serving model identity is unknown. This is not independent review,
Astra acceptance, controller acceptance, manuscript incorporation, or release approval.

## Frozen setting

Repository base: `a5937595cde3e3db00975b81e5171cdef92c801a`.
Lean: `4.35.0`. Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`
(`v4.35.0`). No package, toolchain, root library, registry, checker, target, or
manuscript definition is changed.

Final contribution prefix: `ZInQKernel/Contrib/GlobalDifferentTransport/`;
module prefix: `ZInQKernel.Contrib.GlobalDifferentTransport`;
public namespace: `GlobalDifferentTransport`.
The earlier working import prefix was outside the CI-selected contribution
prefix. Its successful checks are retained only as historical working evidence;
they do not validate the final candidate. Final-prefix recompilation is separate.

For the target specialization, set

- `R = ℤ`, `K = ℚ`, `S = NumberField.RingOfIntegers L`;
- `v : HeightOneSpectrum ℤ`, `w : HeightOneSpectrum S`, with
  `w.asIdeal.LiesOver v.asIdeal`;
- `Kv = v.adicCompletion ℚ`, `Lw = w.adicCompletion L`;
- `A = v.adicCompletionIntegers ℚ`, `B = w.adicCompletionIntegers L`;
- `mA = maximalIdeal A`, `mB = maximalIdeal B`.

These are the concrete rings in the intended T20/T21 transport, not abstract
local-field integer rings supplied without an identification. The construction
uses `ℤ` directly: no identification of `NumberField.RingOfIntegers ℚ` with
`ℤ`, or of another presentation of `ℤ_p` with `A`, is silently assumed.

## Exact public sources actually read

Tau Ceti revision
[`a6027b1d24fcb935c53bd5b50d11b40991cda418`](https://github.com/TauCetiProject/TauCeti/tree/a6027b1d24fcb935c53bd5b50d11b40991cda418)
uses `v4.36.0-rc2`, not the project's pinned `4.35.0`. The read source headers
state Apache 2.0 and credit the Tau Ceti contributors; adapted headers retain
that attribution. This is a declaration-level adaptation, not a package installation.

1. `TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`,
   SHA-256 `32f17cdc947db6b4723eb82f85f706ca3f8782ea318b766fd99d8f80ab651850`.
   Its actual proof passes finite trace-dual expansions through the completed
   **field** tensor decomposition, lifts local integers through the **integral**
   semilocal decomposition, identifies the trace-dual fractional ideals, and
   then takes their inverses. The equality of differents is not merely ideal
   multiplicity preservation.
2. `.../Different/Exponent.lean`,
   SHA-256 `84468c122be7a950bd64c346aaba30ad3a6bab28e3c8212fb9f615a3cba5148e`.
   Lines 217–232 combine the actual different-image equality with single-place
   multiplicity preservation. The later Hilbert formula is not used for that comparison.
3. `.../LocalGlobal/RamificationGroup.lean`,
   SHA-256 `20739ca65f7cf555dd0de3686a64820d294f2c9abd11298b086cf971617aa6c8`.
   Lines 70–108 compare congruences for **all** nonnegative indices using exact
   prime-power contraction, approximation modulo every power, equivariance,
   and valuation preservation. Lines 123–146 use an actual decomposition-group
   equivalence before comparing cardinalities.
4. `TauCeti/RingTheory/DedekindDomain/AdicValuation/Completion.lean`,
   SHA-256 `8cc0058121b4cd590a7abf45db79904ac7a72ad325af81d7be8678fae290bd33`.
   Only the single-place prime, valuation-filtration, and approximation proofs
   are selected; the Henselian/local-field development is not imported.
5. `TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean`,
   SHA-256 `e632451aa3e55de2dc4836d5d62aa824f8415d9ec6a023c8b06e9f6921d7e7c0`.
   Lines 269–447 construct the compatible completed field and integer maps,
   their continuity, valuation restriction, and maximal-ideal contraction.
6. `TauCeti/NumberTheory/NumberField/LocalGlobal/DecompositionGroup.lean`,
   `TauCeti/RingTheory/DedekindDomain/AdicValuation/Transport.lean`, and
   `TauCeti/Topology/Algebra/Valued/WithVal.lean`: the forward action and
   valuation-compatible completion-isomorphism proofs are read and pruned.
   The proposed reverse integer-automorphism route instead uses normal-field
   restriction, not the source's local-degree cardinality argument.
7. `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean`,
   SHA-256 `627d7c5f31d10c577adab9f04f511ace8868d59a03323fc69e5731b6be7432ee`.
   It requires localization of the extension at the image of the **same base
   submonoid**. It does not directly identify a single-prime localization or
   its completion when several primes lie above the base prime.

The source's `Different/Basic` closure comprises 83 modules, approximately
18,000 lines; the ramification comparison closure comprises 125 modules,
approximately 28,000 lines. Those closures are not automatically ported.
In Mathlib 4.35 the needed adic-completion APIs already reside in the older
monolithic `Mathlib.RingTheory.DedekindDomain.AdicValuation`. The absence of the
4.36 split path does not justify duplicating those definitions.

## Supplied single-place transport

`Completion.lean` proves, for every Dedekind domain `R`, fraction field `K`,
height-one prime `v`, ideal `I`, and `n : ℕ`:

```lean
(maximalIdeal (v.adicCompletionIntegers K)) ^ n ∣
    I.map (algebraMap R (v.adicCompletionIntegers K)) ↔
  v.asIdeal ^ n ∣ I
```

There is no `I ≠ ⊥` premise here: `I = ⊥` and `n = 0` are included.
The proof identifies both the extension and contraction of **every** prime
power. Ideal divisibility is reverse inclusion (`J ∣ I ↔ I ≤ J`), so the
reflection follows from `Ideal.map_le_iff_le_comap`, not from an abstract
isomorphism of ideal monoids.

`Multiplicity.lean` derives finite multiplicity preservation for `I ≠ ⊥`,
proving finiteness on both sides. It separately proves that the chosen prime
has ramification index one in the single completion over its affine model.
That does not assert finite generation of the completion over the global ring.

`Approximation.lean` proves the exact all-power surjectivity needed by the
congruence transport:

```lean
∀ (n : ℕ) (x : v.adicCompletionIntegers K),
  ∃ a : R, x - algebraMap R (v.adicCompletionIntegers K) a ∈
    maximalIdeal (v.adicCompletionIntegers K) ^ n
```

The proof first approximates by a fraction-field element in an open valuation
ball, then uses Mathlib's proved integral-at-one-prime approximation by `R`.
It does not infer integral density from density of the fraction field alone.

## Canonical maps and the genuine ramification index

`Extension.lean` constructs `completionRingHom` by uniformly completing the
actual fraction-field map, and restricts it to `completionIntegersRingHom`.
Their squares with the global embeddings commute. The scope
`GlobalDifferentTransportCompletion` supplies only their induced algebras and
proved scalar-tower, continuous-action, injectivity, and lying-over properties.
Low-priority algebra instances avoid replacing the ordinary self-algebra.

`Ramification.lean` proves the exact concrete-ring equation:

```lean
(maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
    (v.adicCompletionIntegers ℚ) = w.asIdeal.ramificationIdx ℤ
```

The generic theorem works without Galois assumptions. Its derivation is:

1. `mA` is generated by `v.asIdeal`.
2. The canonical integer-map square identifies its image in `B` with the
   image in `B` of `v.asIdeal.map (algebraMap ℤ S)`.
3. Single-place multiplicity transport at `w` preserves the multiplicity of
   that genuine globally mapped ideal.
4. Mathlib identifies both length-defined ramification indices with those
   ideal multiplicities.

`NumberField.lean` applies these results to `ℤ ⊆ 𝓞 L` and proves finite
dimensionality of `Lw/Kv` using the closed, dense image of `Kv ⊗[ℚ] L`.
This proof uses the coherent `Valued` normed-field scope; a non-definitionally
compatible normed-field instance cannot be substituted in the closed-range step.

The same module proves
`valued_completed_globalInteger`: the completed normalized valuation of an
actual global integer equals its original `w.intValuation`. Composing it with
T21's separately proved global integer normalization, with its positive
ramification index, yields the required valuation of `(e : B)`; the arithmetic
normalization is not duplicated here.

## Decomposition-action scope

`Equiv.lean` supplies valuation-compatible completion isomorphisms.
`Decomposition.lean` constructs the genuine decomposition-group action on the
completed field and its integer ring, including agreement on global integers,
faithfulness, and preservation of every maximal-ideal power by local ring automorphisms.
`Restriction.lean` proves the inverse by fraction-field extension and normal-field
restriction. Under `[Normal ℚ L]`, `decompositionIntegersMulEquiv` is the genuine
group equivalence onto automorphisms of the actual completed integer extension.
The forward map to all completed **field** automorphisms is proved faithful;
surjectivity onto that whole field-automorphism group is not claimed here without
an additional integer-ring-preservation argument.

The relevant local group is the automorphism group of **this actual completed
integer extension**, over `A`. The T20 all-index comparison must consume the
constructed group equivalence, the actual equivariant map `S → B`, exact
contraction of all powers, preservation of all powers, and approximation modulo
all powers. An injective group map alone does not establish equality of orders.
No Hilbert formula, eventual-triviality argument, or counting proof is supplied here.

## Fixed-field and unique-prime localization foundations

`UniqueLocalization.lean` proves that a genuinely unique prime allows replacing
the simultaneous base localization by the single-prime localization, and proves
module finiteness over the localized base. Its denominator step now invokes the
existing, stronger Mathlib 4.35 theorem
`Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton`
(`Mathlib/RingTheory/Ideal/GoingUp.lean:395–412`), rather than retaining a duplicate
prime-disjointness proof. The criterion does not require a new local-finiteness
assumption. It uses the actual canonical `algebraOfLiesOver`.

`FixedFieldLocalization.lean` constructs the actual
`F = FixedPoints.intermediateField (stabilizer Gal(M/ℚ) P)` for a finite Galois
number field `M`. It supplies the unique-prime statement for
`Q = P.under (𝓞 F)`, the simultaneous-localization property for `S_P`, genuine
finiteness of `S_P/(𝓞 F)_Q`, and DVR properties after checking `P ≠ ⊥` and
`Q ≠ ⊥`. The base-index statement instantiates Hilbert theory at `ℤ/ℚ` explicitly.
It does not silently replace `𝓞 ℚ` by `ℤ`.

`UniqueLocalizationTower.lean` proves that uniqueness at the top of a faithful
integral ring tower descends to each intermediate ring, with the actual
contracted prime. Combined with global module finiteness it gives finite
single-prime localizations at the intermediate levels. This does not construct
`E = M^(D ∩ H)` or `U = M^(I H0)` or prove their ramification assertions.

`IntegralClosureLocalization.lean` derives the actual localized integral-closure
property from the global one and simultaneous localization. A local integral
closure is not assumed: one direction clears a base denominator, and the other
writes a local element as a global integral element times an inverse base unit.
The ambient fraction fields and every comparison map remain explicit.

`LocalizationDifferent.lean` proves
`map_differentIdeal_baseLocalization`, the genuine equality of different ideals
under simultaneous base localization. It first proves the trace-dual span
identity, derives localized integral closure using the preceding module, then
proves equality of the extended trace-dual fractional ideals and their inverses.
The statement requires the compatible global/local algebra maps, unchanged
fraction fields, and the structural domain/Dedekind/torsion-free properties of
the localized rings. These are meaningful structure inputs, not the desired
different equality as an assumption. At a concrete fixed-field application the
canonical fraction-field lifts and all scalar squares must still be instantiated
and checked; successful compilation of this generic supplier does not perform
that final application or the whole proposed `F/E/U` argument.

Compatibility inspection found that
`IsFractionRing.isFractionRing_of_isDomain_of_isLocalization` already exists in
4.35's `Localization/LocalizationLocalization.lean`; the missing import is not
a missing theorem. The DVR localization theorem likewise already exists under
`IsLocalization.AtPrime`. Neither foundational proof is duplicated.

## Remaining foundational assertion: the actual different

The following assertion is **not supplied**, even though its rings and maps
are now constructed:

```lean
(differentIdeal ℤ (𝓞 L)).map
    (algebraMap (𝓞 L) (w.adicCompletionIntegers L)) =
  differentIdeal (v.adicCompletionIntegers ℚ) (w.adicCompletionIntegers L)
```

The already proved exponent comparisons concern the **extended global ideal**,
not the right-hand actual relative different. Replacing one by the other would
silently assume the needed theorem. No axiom, `Fact`, or theorem taking that
comparison as an input is used to claim closure.

For the direct completion route, remaining suppliers include:

- integral closure/finiteness of the actual completed integer extension
  where the local arithmetic supplier requires them;
- a compatible integral semilocal tensor decomposition, not just the field
  tensor map's surjectivity;
- the componentwise trace pairing and the trace-dual-family comparison;
- the corresponding equality of trace-dual fractional ideals and their inverses.

Finite-dimensionality of `Lw/Kv` alone is not a formal proof of these integral
statements. The Basic source's exact field and integral decompositions and
trace-pairing identities must be transported to the actual `ℤ`-based objects.

A correct alternative for the Galois case is the decomposition fixed field
`F = L^D`, with `Q = P ∩ 𝓞 F`. Mathlib 4.35's
`IsDecompositionField.primesOver_eq_singleton` supplies uniqueness of `P` above
`Q`; `ramificationIdx_eq` and `inertiaDeg_eq` supply base index/degree one,
with their integral-closure and residue-separability hypotheses checked.
This permits a **properly proved** finite `S_P/(𝓞 F)_Q` route, simultaneous
base localization of the different, and tower transitivity. It still needs
explicit identifications of the completions and of the relative differents.
These suppliers are not newly invented assumptions and are not marked absent.
The alternative is Galois-specific; it does not by itself cover T21's arbitrary
number fields without an additional justified normal-closure/tower argument.

The tempting `S_P/ℤ_(p)` finite-module assertion is false when primes split.
For example, in `ℚ(i)` at `5`, the localization at `(2+i)` contains
`1/(2-i)`, which has negative valuation at the other prime `(2-i)` above `5`.
It is not integral over `ℤ_(5)`, so this localization is not finite over
`ℤ_(5)`. This is an informal adverse-case check, not a new Lean theorem.

## Source-to-consumer checks and exceptional cases

The supplied proofs use the actual canonical maps, not unrelated algebra
structures. They cover all ideal-power indices, not only the different exponent
or a terminal filtration index. Multiplicity statements explicitly exclude the
zero ideal where natural multiplicity loses the infinite exponent convention.
Uniformizers have multiplicative value `exp(-1)`; membership in the `n`-th
maximal-ideal power is value **at most** `exp(-n)`. No sign, ramification factor,
or natural `+1` endpoint is silently changed.

The generic ideal comparison includes zero and unit ideals and exponent zero.
The number-field different is nonzero. All primes, including `2`, are allowed.
The ramification comparison and valuation lift impose no Galois hypothesis;
normality is confined to the reverse T20 decomposition-action construction.
The unproved actual-different comparison remains required by **both** T20 and
T21; it is not retired by the partial mapped-ideal results.

This is a non-release proof contribution. Immutable audit history, current
manuscript, application registry and protected acceptance records are unaffected.
No historical argument is declared newly repaired or currently incorporated.

## Verification

Final-prefix verification on November 13, 2026 passed for all **14 modules**
(**1,985 source lines**). Lean `4.35.0`, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and the pinned Mathlib revision were used.
Every compiler and replay command ran through the four-command resource gate,
with `LEAN_NUM_THREADS=2` and Lean `-j2`.

- Fresh contribution-output compilation: **42.359 seconds**.
- Same-source warm recompilation: **42.631 seconds**.
- Scoped kernel replay and declaration-body axiom closure: **12.272 seconds**.
- **170 declarations** and 170 raw declaration occurrences were replayed.
  Serialized name/declaration tables and duplicate-body handling were checked;
  there were no duplicate theorem bodies in this packet.
- The complete used-constant closure of every new raw declaration uses only
  `propext`, `Classical.choice`, and `Quot.sound`. No additional axiom, `sorry`,
  admitted comparison, `native_decide`, or owned unsafe/partial declaration supplies a proof.
- All 14 source hashes were unchanged throughout both compilations and replay.
  The source lexical guard and public-note private-marker guard had no matches.

“Fresh” here clears only the private contribution outputs. Pinned Mathlib and
unchanged baseline dependencies were cached; this is not a cold dependency build.
The temporary verifier invokes `Lean.Replay` on the listed new modules and walks
actual serialized declaration bodies. It changes no repository checker or policy.
External Mathlib/base modules are imports, not part of the scoped replay.
Full assembled-candidate CI/replay, source-coverage review, concrete downstream
applications and designated independent Astra acceptance remain separate
parent/integrator duties. Both verification records explicitly deny protocol acceptance.

The proof packet includes `verification/ScopedReplay.lean` and
`verification/verification.json`; neither is a change to the repository's audit code.
The underlying portable commands, assuming the pinned dependencies are available,
are shown below. In the verification run they were launched inside the supplied
resource gate; its machine-specific path is intentionally not part of this public note.

```sh
export LEAN_NUM_THREADS=2
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/GlobalDifferentTransport
for name in Completion Multiplicity Approximation Extension Ramification \
    NumberField Equiv Decomposition Restriction UniqueLocalization \
    IntegralClosureLocalization FixedFieldLocalization UniqueLocalizationTower \
    LocalizationDifferent; do
  lake env lean -j2 \
    -o ".lake/build/lib/lean/ZInQKernel/Contrib/GlobalDifferentTransport/$name.olean" \
    "ZInQKernel/Contrib/GlobalDifferentTransport/$name.lean"
done
lake env lean -j2 --run verification/ScopedReplay.lean verification/replay.json
```

### Final source bindings (SHA-256)

All paths below are relative to `ZInQKernel/Contrib/GlobalDifferentTransport/`.
These bind the uncommitted contribution files, not an acceptance decision.

- `Completion.lean`: `4a16bb1445cc6619497bfbfd060e123a9af8564ca8401013a52d9aa77cdedb00`
- `Multiplicity.lean`: `ef208cb360af429046cd63d96319cd6fd57708cd2837f95366710511933d9075`
- `Approximation.lean`: `fbf3d5db7419629bcd57f8cbdc21b35d074d98c2fbf69c5feb3b2c47d2e47b38`
- `Extension.lean`: `49ff5572fe62b849f9025bcb9214c01c974068c29dbc17df20143b09b4097401`
- `Ramification.lean`: `2db413be3a4dead359b22d8656a9649bc2104763d536c74f2b47a0719f129c2e`
- `NumberField.lean`: `30ddb8bbc79660d6e378ac9278ce76e2aa8a1564190c38cc4dd637c8e4ecffa5`
- `Equiv.lean`: `e6c18760f0b7870d223c2cc5a56960f82aaa951c3ac2ed78ca941313d6a9237f`
- `Decomposition.lean`: `a345364a54dc024fd1704a5e4f168755c2fb335f4f69f45506e7c1a5f97c1005`
- `Restriction.lean`: `1ef9fcaf1c55b0f60e72327103247f61ed4afebea89fee14e01bebc820848588`
- `UniqueLocalization.lean`: `bc8b57b06086fcaa3a3f71db6588409eccb12139e8812f640ce17278438d1c5c`
- `IntegralClosureLocalization.lean`: `31589f21c3972b9d2f2a483302cdf792941b0c1a8fb4a84ed72d6fc3d84d1cc5`
- `FixedFieldLocalization.lean`: `2194aa841e0f2190bd3bb5311482923c25af33e6b2d2fde189e382105b3e5d1a`
- `UniqueLocalizationTower.lean`: `b222bbf9df0ca638b5d96163640d85887d1baf9d1e823a32b7659eb34cdc8053`
- `LocalizationDifferent.lean`: `54030254027e4931c87534e28ed5a39654cea6aaa7c74ff999b20c2825b41555`
