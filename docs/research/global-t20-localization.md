# GLOBAL T20 Hilbert different formula: localization proof packet

Status: compiled exact closed GLOBAL theorem with standard axioms and scoped kernel replay.
This is a preliminary author contribution by Metamate, with serving-model identity unknown.
It is not an independent review, Astra acceptance, controller acceptance or a research release.

## Exact declaration and unchanged source boundary

```lean
ZInQ.Contrib.HilbertDifferent.hilbertDifferentFormula :
  GlueConductor.HilbertDifferentFormula
```

The stored provider type is literally that main target constant, with **zero outer provider
binders and zero universe parameters**. An independently spelled full target body agrees with
the actual main body by `Iff.rfl` and `Kernel.isDefEq`. The target retains every original input:
`L : Type`, `[Field L] [NumberField L] [IsGalois ℚ L]`, and every prime
`P : Ideal (𝓞 L)` with `P ≠ ⊥`. It provides a witness `n` with the actual global lower group
trivial and both exact ideal-power tests:

```lean
∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
  P ^ (∑ i ∈ Finset.range n, (GlueConductor.ramCard L P i - 1)) ∣
    differentIdeal ℤ (𝓞 L) ∧
  ¬ P ^ (∑ i ∈ Finset.range n, (GlueConductor.ramCard L P i - 1) + 1) ∣
    differentIdeal ℤ (𝓞 L)
```

There is no added local, monogenicity, completion, comparison, literature-leaf or `Fact` premise.
The original prime-power definition `ramGroup L P i := (P^(i+1)).inertia Gal(L/ℚ)` is unchanged.
The different is exactly Mathlib's `differentIdeal ℤ (𝓞 L)`, with integral prime multiplicity
normalization; no ramification, residue-degree or ambient field-degree factor is removed.

The contribution consists of only these five **new** modules:

- `ZInQKernel/Contrib/HilbertDifferent/PrimeLocalization.lean`;
- `ZInQKernel/Contrib/HilbertDifferent/LocalizationModel.lean`;
- `ZInQKernel/Contrib/HilbertDifferent/LocalizationGroup.lean`;
- `ZInQKernel/Contrib/HilbertDifferent/GlobalFormula.lean`;
- `ZInQKernel/Contrib/HilbertDifferent/GlobalFormulaChecks.lean`.

Published PR55 head `daaa048f050f4a1236433ce87f7e4dde1718de63`, its ten Hilbert proof modules,
shared monogenic supplier and tracked research note are unchanged. Its original eight-module
partial, local result and global-open evidence remain historical evidence at their original
scope; they are not relabeled as earlier global closure. The current public branch/head is not
moved. No commit, push, PR, merge, registry, root, pin, package, checker, policy, audit-history,
controller or manuscript change is made here. Full assembled-candidate checks and integration
are the parent's separate work. This proof-only non-release packet promotes no polynomial record,
so manuscript/TeX/PDF release requirements do not apply to this scoped contribution.

## Exact frozen suppliers actually consumed

The additional transport is the frozen 27-module `GlobalDifferentTransport` packet over the
same Lean/Mathlib 4.35 pins. All its 27 source hashes and existing compiled companion hashes
were checked read-only and preserved. Its different-completion identity is not assumed or used.
Only the legitimate localization dependency slice is imported by this proof.

The key actual supplied assertion is
`GlobalDifferentTransport.multiplicity_absoluteDifferent_decompositionField_atPrime_eq` in
`DecompositionFieldDifferent.lean`, SHA-256
`6acf62d40360fd6e0bc93554148d8dc5bd3a15a7e0579f077155c33112226762`.
For the actual Galois number field `L`, prime `P`, decomposition subgroup
`D = MulAction.stabilizer Gal(L/ℚ) P`, actual fixed field `F = L^D`, and
`Q = P.under (𝓞 F)`, it proves

```lean
let _ := Localization.AtPrime.algebraOfLiesOver Q P
multiplicity (IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (differentIdeal (Localization.AtPrime Q) (Localization.AtPrime P)) =
  multiplicity P (differentIdeal ℤ (𝓞 L))
```

This is a proved equality on the actual localizations, not a caller-supplied identity. The
supplying proof first uses the actual unique-prime relative localization, then global different
transitivity and unramifiedness of the actual `Q` over `ℤ` to remove its base factor.

Other direct source interfaces were read in full before application:

- `FixedFieldLocalization.lean`, SHA-256
  `2194aa841e0f2190bd3bb5311482923c25af33e6b2d2fde189e382105b3e5d1a`:
  actual `decompositionFixedField`, unique prime over its contraction, simultaneous base
  localization, genuine finite module extension, nonzero contraction and actual DVRs.
- `CanonicalLocalization.lean`, SHA-256
  `f27e7ba1de97834a41b7729876469b521d01249efe7865e0cff1f73ff3d9323f`:
  the canonical localization-to-original-field maps as `IsLocalization.lift`, their agreement
  on original elements, fraction fields and scalar towers.
- `NumberFieldPrimeLocalizationDifferent.lean`, SHA-256
  `933069e7582c7df2b1df7cb21dc1d9a9c172b097047270d3532802fda171427a`:
  the canonical `algebraOfLiesOver`/original-field square, genuine single-prime different
  localization and all-exponent coefficient comparison.
- `IntegralClosureLocalization.lean`, SHA-256
  `31589f21c3972b9d2f2a483302cdf792941b0c1a8fb4a84ed72d6fc3d84d1cc5`:
  simultaneous base localization gives actual integral closure in the unchanged original
  top field, by clearing base denominators. This property is derived, not added as a premise.
- The relative localization/different argument in `NumberFieldLocalizationDifferent.lean`,
  `LocalizationDifferent.lean` and `UniqueLocalization.lean` was read with its actual
  same-base-submonoid and unique-prime conditions. Their exact hashes are in the supplied
  source manifest. No false finiteness of a selected split-prime localization over `ℤ_(p)` is used.

The existing monogenic Hilbert supplier is
`ZInQ.Contrib.HilbertDifferent.hilbertDifferentAt_integralClosure_of_monogenic` in the unchanged
`IntegralClosure.lean`, SHA-256
`4fd24372f93eea8afc855e5ae24036c2ae910b45f5efb96a638564e0ee471d52`.
It takes explicit integrally closed base domain, Dedekind top domain, original fraction fields,
actual integral closure, compatible maps/towers, module-finiteness/torsion-freeness and finite
Galois field extension. The needed generator is discharged by the unchanged proved
`ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top`, source SHA-256
`a2b761efd76e4ee50a00d277824f943ee34b4f617c273df0d17faf5a8b68e24d`.
It requires only finite torsion-free DVR extension and perfect downstairs residue field,
not completeness or a finite-residue-field assumption.

The original generator/derivative/counting provenance remains exactly as in PR55:
TauCetiProject/TauCeti at `a6027b1d24fcb935c53bd5b50d11b40991cda418`, minimally adapted onto
Mathlib v4.35. Source attributions and Apache-2.0 material in the existing supplier files and
research note are preserved. No large external dependency or updated pin is added.

## Source-first connecting derivation

### 1. The finite localized model is the actual one

`LocalizationModel` reuses `F = decompositionFixedField L P` and its actual prime contraction.
Its `baseRing` is `(𝓞 F)_Q`, its `topRing` is `(𝓞 L)_P`, and its scoped `localAlgebra` is exactly
`Localization.AtPrime.algebraOfLiesOver Q P`. The base embedding into `F`, top embedding into
`L` and base action on `L` are the frozen canonical lifts, not unrelated chosen algebras.
Their original-integer, original-field and local-ring scalar towers are supplied from the
proved commuting square. The true unique-prime result supplies simultaneous localization
and `Module.Finite baseRing topRing`; the field square proves faithfulness/torsion-freeness.
The actual localized integral closure inside the original `L` is derived with the same
submonoid, not assumed. Nonzero contraction gives the actual two DVRs. The finite quotient
at the actual base prime proves finite residue field and hence perfectness.

### 2. The correct decomposition-group equivalence is constructed

`localizationFieldEquiv` explicitly rebundles the same global decomposition automorphism as
an automorphism of the original `L` over the actual `F`, by Mathlib's
`IntermediateField.subgroupEquivAlgEquiv`. Its value on every `x : L` is unchanged, by `rfl`.
`localizationDecompositionEquiv` composes that map with
`galRestrict baseRing F L topRing` for the **true** integral closure just established.
Its inverse and surjectivity are Mathlib's actual restriction/extension constructions through
the fraction fields. No desired local automorphism map, equal-cardinality premise or
completion equivalence is assumed.

`localizationDecompositionEquiv_algebraMap` proves the exact commutative action square:
for every `σ : D` and `x : 𝓞 L`,

```lean
algebraMap (𝓞 L) topRing (σ • x) =
  localizationDecompositionEquiv L P σ (algebraMap (𝓞 L) topRing x)
```

The proof injects into the unchanged original `L`, uses the canonical tower, checks the
unchanged field value of the rebundled automorphism and applies
`algebraMap_galRestrict_apply`. Explicitly typed rebundling resolves the different transparent
presentations of the fixed field; no transparency/compiler flag is changed to hide a mismatch.

### 3. Every lower index uses the same integral congruence

Mathlib v4.35 `IsLocalization.AtPrime.under_maximalIdeal_pow` contracts **every** localized
maximal-ideal power to `P^n`. Its `equivQuotMaximalIdealPow` is the actual isomorphism
`𝓞 L/P^n ≃ (𝓞 L)_P/m^n`, and supplies surjectivity modulo every power, including `n=0`.
Every local algebra automorphism preserves the unique maximal ideal and its powers.
`PrimeLocalization` exposes these concrete facts. Applying the unchanged proved
`powerInertia_eq_comap_of_equivariant_dense` therefore gives
`ramGroup_localization_comap` inside the actual `D` for every `i : ℕ`.

The original global lower group lies in `D`; its restriction to `D` is a bijection on the
same elements. `ramCard_eq_card_localization` consequently identifies the actual global
`ramCard L P i` with the localized lower-group cardinality for every nonnegative index.
`ramGroup_eq_bot_iff_localization` identifies triviality at those same indices.
There is no shifted index, replacement ambient group or ramification/residue-degree multiplier.

### 4. Hilbert's formula concerns the exact local ideal being transported

A generator `β` is constructed in the actual finite DVR `topRing/baseRing` using the proved
monogenicity supplier and derived perfect residue field. The already proved generic Hilbert
argument is applied at **the unchanged original fields `F` and `L`**, with the canonical
localized integral closure and scalar towers. It computes exact divisibility of
`differentIdeal baseRing topRing` at the actual maximal ideal, including the successor test.
This is precisely the ideal in the frozen global/localized coefficient identity; no unrelated
power-basis order or unproved monogenic global ring is substituted.

The exact divisibility pair gives its finite multiplicity. The proved different coefficient
identity identifies that number with the exponent of `differentIdeal ℤ (𝓞 L)` at the original
`P`. The all-index cardinality identity identifies the finite range sums, and the triviality
comparison gives `ramGroup L P n = ⊥`. The unchanged global finite-multiplicity/divisibility
interface supplies the main target's exact `P^s` divisibility and `¬P^(s+1)` nondivisibility.
The closed provider abstracts exactly the original main quantifiers.

## Hypotheses, exceptions and scope

- Every original Galois number field and every nonzero prime is covered, with no odd-prime,
  tame-prime, residue-characteristic or extra local/Galois-subgroup condition.
- The decomposition fixed field need not be Galois over `ℚ`; the actual `L/F` Galois
  correspondence, not global normality of `D`, is used.
- A selected split-prime localization is not asserted finite over `ℤ_(p)`. Finiteness is over
  the actual decomposition-field localization, and its unique-prime condition is proved.
- All powers and all nonnegative indices are covered. The empty quotient/range, exponent zero,
  trivial group, and successor nondivisibility are explicitly checked.
- The exact formula is proved for any eventual-triviality cutoff, not only a preferred positive
  witness. The rational trivial extension gives witness zero for **every** nonzero rational prime.
- No completion, Henselianity, computed valuation normalization or completed-different identity
  is a premise of the new global proof.
- The T21 arbitrary-field presentation/arithmetic, Serre bound, T31 normed embedding and T22
  Herbrand theorem are not duplicated or inferred from this work.
- The source-use reconstruction here is the author's direct comparison of the actual suppliers,
  maps and consumers. It is not a blind/non-author source-first coverage decision or Astra acceptance.

Bounded consistency scope is the five new modules, their exact global/endpoint checks, the actual
main target, the frozen localized different and monogenic Hilbert supplier slice, and the
preserved PR55 sources/note. The earlier monogenic/local-only versus global mismatch and the
split-prime finiteness error are not used in the new proof. Historical sources remain unchanged.
Future headline/H integration, full candidate CI, reviewer completeness and publication are
separate responsibilities, not claims made by this producer packet.

## Verification already completed

Pins are unchanged: Lean `4.35.0`, compiler `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

- All five new modules directly compiled over the frozen baseline/supplier outputs in a complete
  private canonical import overlay. No supplier/dependency build or shared-cache write was done.
- Full target spelling, zero cutoff, successor, arbitrary cutoff and rational/trivial-group
  endpoint checks compiled and printed only `propext`, `Classical.choice`, `Quot.sound`.
- The literal stored-type test, zero outer binder/universe test and full independent-body
  `Kernel.isDefEq` checks passed. The portable checker is included in this packet.
- The unchanged `scripts/audit_kernel.lean` passed scoped replay of all **five new modules /
  55 actual declarations / 55 raw occurrences**. It traversed actual dependency bodies, reported
  only the three standard axioms, no duplicate bodies, no unsafe/partial declarations, target
  `proved_exact_type`, and `protocol_acceptance: false`. Replay took 95.65 seconds, maximum
  RSS 15,317,684 KiB. Only the new modules were replayed as owned; previously frozen producers
  and Mathlib/base are imports, not a claim of newly completed full-scope audit.
- Twelve nonfatal unused-section-variable style warnings were present in the structural/group
  modules, and no final compilation error. No compiler option was changed to suppress them.
- All protected PR55 source/note bytes and all 27 frozen supplier source/cache companion hashes
  were rechecked and unchanged. Current HEAD/public branch are untouched. New modules are uncommitted.

The parent's full assembled-source audit remains separate. No acceptance or release is inferred
from these scoped checks. Source hashes, direct import closure and final repeated verification
are recorded in the packet's verification manifest.

### Final repeated verification and immutable bindings

The same five source files (526 lines) were directly recompiled again without editing any source.
Times in module order were 41.68, 8.98, 9.79, 4.46 and 4.29 seconds (69.20 seconds total), with
maximum RSS 6,662,920 KiB and the same twelve nonfatal style warnings. Latest scoped serialized
replay passed on those repeated outputs: five modules, 55 actual declarations/raw occurrences,
no duplicate bodies, no unsafe/partial declarations, and exactly the standard three axioms.
It took 38.25 seconds, maximum RSS 15,931,144 KiB. The latest separate literal stored-type/full
body/binder/universe check passed in 5.06 seconds, maximum RSS 8,428,420 KiB.

The actual contribution-source import closure is 21 modules: these five new modules, the existing
Hilbert/monogenic slice and only **eight** of the frozen localization supplier modules. None of
the completed-integer/decomposition/completion supplier modules is imported by this new route.
The full 27-module frozen source/cache preservation is still checked, not silently reduced to
the eight consumed modules. The source dependency graph, full 27 source bindings, protected PR55
bindings and literal expected target are included in the packet.

Final UTF-8/LF source SHA-256:

- `PrimeLocalization.lean`: `5cde4b6c2fc9e1a93f9e32d125bc0b99f7029506ed60069ccedf037e75957c4b`.
- `LocalizationModel.lean`: `03081130c9f925f243acb56ca27985b9dc4093ee0b5c874208bf7426159c013d`.
- `LocalizationGroup.lean`: `f2b889ccee518447bb94d4944db80dc245b24932d33f845dee70efc6dd1cd1c6`.
- `GlobalFormula.lean`: `eddc3026ed0a627c73bc03e053e0fa234cc3db4da5fe8c5a93288b6e6a65566f`.
- `GlobalFormulaChecks.lean`: `8034f93be3564958989ecdc570131a2a4243dac923141b18d35934617bd5112a`.

### Failed attempts retained, with the precise repairs

The original producer journal retains each unsuccessful compiler/checker round. None is counted
as final candidate validation. The following failure mechanisms and their final dispositions
are preserved alongside the unchanged earlier split-prime/monogenic-global failure evidence:

1. A rewrite at an explicit `toRingHom` did not match the maximal-ideal image theorem's ring-
   equivalence coercion. An explicitly typed maximal-ideal equality supplies the same theorem,
   then `Ideal.map_pow` is used. No mathematical assumption or compiler flag is changed.
2. A private verification mirror initially copied only `.olean` and omitted the frozen module's
   `.olean.server` companion. Existing compiled companions were mirrored read-only and hashed;
   no supplier/dependency rebuild or shared-cache modification was performed.
3. Unqualified names in a `scoped[...] attribute` command were resolved outside the intended
   namespace. Fully qualified new-instance names repair the scope; old/global source is unchanged.
4. An expanded fixed-field rewrite exposed incompatible presentations at implicit transparency.
   The same correspondence is instead rebundled into the **actual supplied fixed field's typed
   interface**, its unchanged value is proved by `rfl`, and the commuting action square is derived
   by an explicit `calc` through the original field. No transparency override is added.
5. The positional call to `algebraMap_galRestrict_apply` was incorrect because K/L/B are implicit.
   The actual pinned source signature was read; those objects are now explicit named arguments.
6. A line-broken private verifier record was syntactically invalid. Record formatting was repaired;
   the independently spelled target and all owned proof sources remain mathematically unchanged.

These are producer elaboration/verification repairs, not independently accepted judgments.
No historical verdict or protected approval is changed, and no adverse inference is dismissed
because compilation happened to pass. The final source-to-consumer argument above is the one
actually compiled and replayed.
