# T20: Hilbert different formula — proved partial and global transport obligations

**Status: preliminary author contribution; the closed GLOBAL T20 target is not proved by this packet.**

Date: November 12, 2026 (verification completed November 13 UTC). Base:
`a5937595cde3e3db00975b81e5171cdef92c801a`. The changes are eight new modules in
`ZInQKernel/Contrib/HilbertDifferent/` and this note, left uncommitted. No root import,
registry, existing source, pin, audit record, policy, manuscript or acceptance record is changed.
This is a proof-only, non-release contribution, not a record promotion; manuscript/TeX/PDF release
maintenance does not apply to this scoped packet. Future integration and release require their
own review. The author is Metamate; serving-model identity is unknown. This is not an Astra review.

## Exact target and statement fidelity

The actual main declaration is `GlueConductor.HilbertDifferentFormula` in
`ZInQKernel/HDecomp/Conductor/Breaks.lean`, lines 341–345 at the base above. It quantifies over
every `L : Type` with `[Field L] [NumberField L] [IsGalois ℚ L]` and every prime
`P : Ideal (𝓞 L)` with `P ≠ ⊥`. Its conclusion is

```lean
∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
  P ^ (∑ i ∈ Finset.range n, (GlueConductor.ramCard L P i - 1)) ∣
    differentIdeal ℤ (𝓞 L) ∧
  ¬ P ^ (∑ i ∈ Finset.range n, (GlueConductor.ramCard L P i - 1) + 1) ∣
    differentIdeal ℤ (𝓞 L)
```

Here `ramGroup L P i := (P ^ (i + 1)).inertia Gal(L/ℚ)` and `ramCard` is `Nat.card` of that
subgroup. The different is Mathlib's integral ideal defined through the inverse trace dual,
not an independently supplied numerical exponent. Natural subtraction is intentional.

The frozen statement reference
[`ZInQKernel/Targets/H/T20.lean`](https://github.com/elliotglazer/diophantine-z-q/blob/2757349fbd8ca613340b679bbd149f78c2baba6b/ZInQKernel/Targets/H/T20.lean)
at draft PR41 head `2757349fbd8ca613340b679bbd149f78c2baba6b` was read, and its bytes were compared
with the pinned public source. They match. It is reference-only, unregistered and not accepted.
It is not imported. An independently spelled copy of the full target was checked against the
actual main proposition by `Iff.rfl`. A separate kernel full-type comparison confirms that the
proved monogenic wrapper is **not** this closed target. Neither the proposed
`ZInQ.Contrib.H.T20_holds` nor a closed `HilbertDifferent.hilbertDifferentFormula` provider is
exported. No `[Fact HilbertDifferentFormula]` is used.

Frozen SHA-256:

- Main `Breaks.lean`: `7742365fd985fda83c733324394cb4a59db3f083e246dad63279924ce790306d`.
- Draft T20 reference: `bceda7cbe75f920699d76a9295fb7208a19bbfd3209ac49856554de35183aa4b`.

### Why the other local leaf is not the target

The actual `PkgI6.HilbertDifferentFormula` is in
`ZInQKernel/HDecomp/Conductor/I6Base.lean`, lines 368–376. It concerns module-finite, torsion-free
extensions of DVRs `A → B`, with complete base, perfect base residue field, separable and Galois
fraction fields. Its conclusion is an **ideal equality**
`differentIdeal A B = maximalIdeal B ^ Σ (|lowerRam A B i| - 1)`.
`lowerRam` at lines 315–316 acts through `B ≃ₐ[A] B`, on powers of the local maximal ideal.
These are not the main global fields, rings, primes or quantifiers. A proof of this local leaf
alone cannot be renamed as global T20. The generic monogenic theorem below is suitable algebraic
input for that local route, but the actual completed rings and comparison maps must still be built.

## Precisely what is proved

All names below are in `ZInQ.Contrib.HilbertDifferent`.

1. **Actual global eventual triviality.**
   `exists_forall_ramGroup_eq_bot L P` proves
   `∃ N, ∀ i, N ≤ i → ramGroup L P i = ⊥` for every prime of a number field.
   This separation statement needs neither `P ≠ ⊥` nor `IsGalois ℚ L`.
   `ramGroup_antitone`, `ramCard_antitone`, `ramCard_pos`, and
   `ramCard_zero_eq_ramificationIdx` supply the genuine filtration/order normalization;
   the last theorem does require the main Galois and nonzero-prime hypotheses.
2. **Exact ideal exponent interfaces.** `different_finiteMultiplicity` and
   `multiplicity_different_eq_iff` prove that the multiplicity in the actual nonzero global
   different is exactly its prime-power divisibility. No finiteness assumption is hidden.
   `finsum_ramCard_sub_one_eq_sum` identifies the finite range with the full support after a
   triviality witness. `exists_ramGroup_eq_bot_and_exact_differentPower` proves existence of
   a triviality witness and an exact exponent **without asserting their Hilbert identification**.
3. **Global monogenic Hilbert formula.**
   `hilbertDifferentAt_of_monogenic L x hx P hP` proves the exact main conclusion at every
   nonzero prime, provided the additional hypothesis is explicitly supplied:
   `x : 𝓞 L`, `hx : Algebra.adjoin ℤ {x} = ⊤`.
   No tame-prime, odd-prime, residue-characteristic or other restriction is added.
   `Checks.exact_global_shape_with_generator` independently spells all these quantifiers and
   the original finite-range conclusion. This is a genuine partial result, not global T20:
   not every number-field ring of integers is globally monogenic.
4. **Global unramified and degree-one cases.**
   `hilbertDifferentAt_of_isUnramifiedAt` proves the main conclusion with `n = 0` at every
   unramified nonzero prime. The checks prove the same conclusion for every nonzero prime
   of `𝓞 ℚ`, construct the needed generator of `𝓞 ℚ/ℤ`, and prove its different is `⊤`.
5. **A generic monogenic integral-closure Hilbert theorem.**
   `hilbertDifferentAt_integralClosure_of_monogenic A K L B x hx P hP` has explicit AKLB data:
   integrally closed domain `A`, Dedekind domain `B`, `K = Frac(A)`, integral closure
   `B` of `A` in `L`, finite/Galois `K → L`, the two compatible scalar towers,
   `[Module.IsTorsionFree A B] [Module.Finite A B]`, and `hx : Algebra.adjoin A {x} = ⊤`.
   It concludes eventual triviality and exact prime-power divisibility of `differentIdeal A B`
   using the explicitly named group `B ≃ₐ[A] B`.
   It uses only the existing Mathlib pin, not Tau Ceti's local-field package.
   With a proved finite-DVR monogenicity theorem it can provide the algebraic Hilbert step
   for genuine completed rings. It never asserts that a chosen global-prime localization
   is automatically module-finite over the base localization.
6. **Proved comparison primitives.**
   `powerInertia_eq_comap_of_equivariant_dense` takes a named group homomorphism `φ`, ring
   homomorphism `f`, equivariance, all power-ideal preimage equalities, preservation of target
   powers under `φ`, and surjectivity modulo every target power. It proves the exact subgroup
   pullback. `card_powerInertia_eq_of_equivariant_dense` upgrades this to card equality when
   the group map is a specified equivalence. `ramCard_eq_card_powerInertia_stabilizer`
   identifies the actual global lower-group cardinality with its realization inside the
   decomposition group. It introduces no ramification, inertia-degree or field-degree factor.
7. **The base-ring identification is proved.**
   `differentIdeal_ringOfIntegersRat_eq L` proves
   `differentIdeal (𝓞 ℚ) (𝓞 L) = differentIdeal ℤ (𝓞 L)` for every number field.
   Both trace pairings use the same field `ℚ`; the two base-ring images in `ℚ` agree through
   `Rat.ringOfIntegersEquiv`. This is an equality of ideals in the original `𝓞 L`, not merely
   equality after rationalization. It does not itself prove the completion comparison.

`hilbertDifferentAt_of_multiplicity_finsum` is only an assembly helper. Its explicit input is

```lean
multiplicity P (differentIdeal ℤ (𝓞 L)) =
  ∑ᶠ i : ℕ, (GlueConductor.ramCard L P i - 1)
```

It converts that identity to the target's witness and exact divisibility. It is not a closed
provider, and its input has not been discharged in arbitrary global number fields here.

## Source-first reconstruction and provenance

The actual supplier is [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti),
immutable revision `a6027b1d24fcb935c53bd5b50d11b40991cda418`. Its toolchain is Lean
`v4.36.0-rc2`; its manifest pins Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`.
The source headers name **The Tau Ceti contributors** and **Apache-2.0**. The source license
has SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and is reproduced below.
The local Hilbert source is byte-identical to that at the earlier T13 source revision
`61090fff281d0c6cece0176aa8436ab748b53048`; this does not assert that the complete two trees agree.

The advertised proof was actually located and read:

- [`NumberTheory/LocalField/Different/Hilbert.lean`](https://github.com/TauCetiProject/TauCeti/blob/a6027b1d24fcb935c53bd5b50d11b40991cda418/TauCeti/NumberTheory/LocalField/Different/Hilbert.lean),
  lines 65–101: monogenic different derivative, product over nonidentity automorphisms, and
  double counting. Lines 105–117 provide truncation at any triviality witness.
- [`NumberTheory/NumberField/LocalGlobal/Different/Exponent.lean`](https://github.com/TauCetiProject/TauCeti/blob/a6027b1d24fcb935c53bd5b50d11b40991cda418/TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Exponent.lean),
  lines 220–232 compare global/completed different multiplicities; lines 239–249 prove the
  genuinely **global** Hilbert identity by that comparison and global/local filtration transport.
- `NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`, lines 88–223: semilocal trace
  expansion, integral semilocal decomposition, trace-dual family and different completion.
- `NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean`, lines 73–146: density and
  equivariance at the actual decomposition homomorphism, then global/local card comparison.

Following every explicit Tau Ceti import from the global exponent module inventories a closure
of **171 modules, 37,300 lines, 1,932,103 bytes**, with 262 distinct direct Mathlib imports.
Two imported Mathlib module paths do not exist at v4.35:
`Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion` and
`Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification`.
This is a path/API compatibility observation, not proof that the corresponding mathematics is
absent: some older completion definitions are in the unsplit `AdicValuation.lean` and number-field
completion modules. The unpruned roots are 83 Tau Ceti files/18,623 lines for global
`Different/Basic`, 125/28,746 for global `RamificationGroup`, and 60/11,763 for local Hilbert.

No large package, umbrella Tau Ceti import, new pin or missing Mathlib module is added.
Only the read proof fragments below are retained and adapted to v4.35. The complete import
**graph** was inventoried; this author does not claim manual proof coverage of all 171 files.
Every retained substantive proof passage and its supplying hypotheses was read. This is the
author's comparison, not a blind/non-author completeness review or an Astra coverage decision.

### Direct proof inventory and derivation

- **Filtration.lean:** finite subgroup chain stabilization from
  `Algebra/Group/Subgroup/FiniteFiltration.lean` 39–48; ideal-power antitonicity and Krull
  separation from `RingTheory/Ideal/RamificationGroup.lean` 92–94, 124–156.
  It directly consumes Mathlib's `WellFoundedLT.antitone_chain_condition` and
  `Ideal.iInf_pow_eq_bot_of_isDomain`. The action-kernel argument is written directly through
  `FaithfulSMul`, without porting extra action-representation machinery.
- **Generators.lean:** generator inertia criterion from `RingTheory/Ideal/Inertia.lean` 47–69;
  ring-to-fraction-field generation from `FieldTheory/IntermediateField/Adjoin/EqTop.lean`
  268–293; primitive-element derivative factorization from `FieldTheory/Galois/Minpoly.lean`
  50–79. The fraction-field proof writes every element as a ratio of two ring elements.
  Galois normality/separability and generation make the orbit map injective and its image
  exactly the roots, each once. Differentiating the product leaves precisely the identity term.
- **Counting.lean:** adapts `RingTheory/LocalRing/RamificationGroup.lean` 469–514 from a DVR's
  additive valuation to Mathlib prime-ideal multiplicity in any Dedekind domain.
  It directly uses the generator criterion, finite prime multiplicity, and Mathlib's bipartite
  double count. For `σ ≠ 1`, its displacement is nonzero, its finite multiplicity is `dσ`, and
  `σ ∈ G_i ↔ i + 1 ≤ dσ`. A triviality witness bounds `dσ ≤ N`, so the filtered range is exactly
  `range dσ`. Counting the same pairs in the other direction gives `|G_i| - 1` by erasing the
  identity, including when `G_i` is trivial. The two ideal-product helpers also explicitly
  handle empty products and nonzero factors.
- **Global.lean:** directly proves faithful restriction to `𝓞 L` using its fraction-field
  surjectivity; invokes the generic separated filtration; proves multiplicity finiteness from
  the nonzero different; and uses the actual Mathlib inertia/ramification-index and unramified
  different theorems. Its finite-support truncation adapts local Hilbert 105–117. The `𝓞 ℚ/ℤ`
  comparison directly uses `coeIdeal_differentIdeal`, `FractionalIdeal.mem_dual`, and the
  integer-ring equivalence to compare the same trace-dual condition.
- **Monogenic.lean:** adapts `RingTheory/DedekindDomain/Different/Monogenic.lean` 68–78 and local
  Hilbert 65–101 directly at the actual global objects. Its direct inputs are ring-to-field
  generation, the Galois derivative product, the proved count, and Mathlib's
  `conductor_mul_differentIdeal` / `conductor_eq_top_of_adjoin_eq_top`.
  Injectivity of `𝓞 L → L` pulls the product identity back to integral elements. The two
  displacement signs generate equal ideals, so there is no dropped unit or valuation factor.
- **IntegralClosure.lean:** gives the same algebraic argument for arbitrary explicit AKLB
  integral-closure data. It directly uses the preceding generic polynomial/counting helpers
  and Mathlib `galRestrict`. A fully checked finite-product bijection through `galRestrict`
  preserves the identity and all nonidentity factors. Nonzero displacements prove that the
  product, hence the different, is nonzero before multiplicity is converted to exact divisibility.
- **Transport.lean:** adapts `RingTheory/LocalRing/RamificationGroup.lean` 692–712 and the
  ideal/subgroup restriction and global card arguments at the cited sources. Its approximation
  proof splits a displacement into the displacement of an approximating global element and
  two controlled errors in the same target ideal power. The reverse implication is exactly the
  supplied ideal-power preimage equality. The actual global lower group lies in the stabilizer
  because it lies in inertia; subgroup restriction is a bijection on these elements.
- **Checks.lean:** directly consumes the global monogenic theorem, finite-exponent/truncation
  interfaces, the rational integer-ring equivalence, and the degree-one derivative product.
  It checks fully quantified global shape with the extra hypothesis exposed, exponent zero,
  different cutoffs, the excluded zero prime's filtration, all nonzero rational primes and
  the unit different. It prints the generic and global API types and their actual axioms.

Selected upstream SHA-256, all at the immutable current supplier revision:

- `Algebra/Group/Subgroup/FiniteFiltration.lean`: `70179517034f4ec9f057e57fc7d9878a7d723a817525e64a0d24ebfc91279bd1`.
- `RingTheory/Ideal/RamificationGroup.lean`: `794fa3a702b816550bfb940617cc5f20540075c201e80db3b53f2093b370050b`.
- `RingTheory/Ideal/Inertia.lean`: `23d2a28af75dbbc18bb326c3c28bd2582c6ef10b2dde07079557e7f0785ca165`.
- `FieldTheory/IntermediateField/Adjoin/EqTop.lean`: `588a280d235cd9f68f16d69fd10d7d6b24645f61be8fc98501406c5cdb336bbe`.
- `FieldTheory/Galois/Minpoly.lean`: `be5253509a59c7fec47739bbb5dcae1451a3370f456bf99ad04e10f5d6ec13ad`.
- `RingTheory/DedekindDomain/Different/Monogenic.lean`: `cd685f72f5b4857d25bc32050ab2c41dfcd03c0990881bd2a1fedfaa57cbc818`.
- `RingTheory/LocalRing/RamificationGroup.lean`: `a4996fc47f3760d111c1c131febdc86ca62c812dffbeb4d4191688ada09113c4`.
- `NumberTheory/LocalField/Different/Hilbert.lean`: `94f10eeb2202025d0b6ae974c6d1c19ff4b1d51292a10486133f764ab83e5892`.
- `NumberTheory/NumberField/LocalGlobal/RamificationGroup.lean`: `20739ca65f7cf555dd0de3686a64820d294f2c9abd11298b086cf971617aa6c8`.
- `NumberTheory/NumberField/LocalGlobal/Different/Exponent.lean`: `84468c122be7a950bd64c346aaba30ad3a6bab28e3c8212fb9f615a3cba5148e`.
- `NumberTheory/NumberField/LocalGlobal/Different/Basic.lean`: `32f17cdc947db6b4723eb82f85f706ca3f8782ea318b766fd99d8f80ab651850`.

## Remaining GLOBAL implication — exact interfaces

The full upstream global route is located, not being declared a new mathematical gap or a false
theorem. What remains unported/undischarged in this contribution is its realization on the actual
global objects. For each nonzero `P` of `𝓞 L`, take `w` to be that height-one prime and `v` the
prime of `𝓞 ℚ` below it. Write `A = v.adicCompletionIntegers ℚ`,
`B = w.adicCompletionIntegers L`, `Q = IsLocalRing.maximalIdeal B`.
The required arithmetic realization must supply:

1. **Actual finite completed rings and fraction fields:** their algebra structures/towers,
   `[Module.Finite A B]`, torsion-freeness, integral-closure and finite/Galois fraction-field
   data, and a proved generator of `B/A`. A separate finite-DVR monogenicity supplier can
   provide the last item once these inputs and separable residue extension are established.
2. **Different coefficient comparison:**
   `multiplicity P (differentIdeal ℤ (𝓞 L)) = multiplicity Q (differentIdeal A B)`.
   Equivalently for exact power transport, for every `k : ℕ`,
   `P^k ∣ differentIdeal ℤ (𝓞 L) ↔ Q^k ∣ differentIdeal A B`.
   Upstream `map_differentIdeal_eq_differentIdeal_adicCompletionIntegers` and
   `multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal` supply the
   completed comparison, after the now-proved `𝓞 ℚ/ℤ` identification. Base localization alone
   is not this lemma; the semilocal trace-dual argument is substantive.
3. **The correct group and filtration maps:** a group equivalence from
   `MulAction.stabilizer Gal(L/ℚ) P` to `B ≃ₐ[A] B`, compatible with the completion embedding
   `f : 𝓞 L →+* B`, and the hypotheses of `card_powerInertia_eq_of_equivariant_dense` for every
   power. Combined with `ramCard_eq_card_powerInertia_stabilizer`, this gives
   `ramCard L P i = Nat.card ((Q^(i+1)).inertia (B ≃ₐ[A] B))` for every `i : ℕ`.
   The entire global Galois group is not the group of one selected completion.

With these inputs, the generic algebraic Hilbert theorem supplies the local exponent, the
coefficient/card comparisons identify the same global exponent and sum, and
`hilbertDifferentAt_of_multiplicity_finsum` supplies the exact main conclusion. This composition
is not asserted here before those arithmetic inputs are proved. The exponent is the integral
prime multiplicity with a uniformizer having exponent one; no `e`, `f` or degree scaling is
silently removed. The separate Serre-bound and Herbrand targets are not proved or duplicated.

### Concrete finiteness obstruction

Do **not** supply `[Module.Finite ℤ_(p) (𝓞 L)_P]` merely because `𝓞 L` is finite over `ℤ`.
For example, let `L = ℚ(i)`, `P = (2+i)` above `5`, and use the localizations
`A = ℤ_(5)`, `S = ℤ[i]_P`. The other prime is `(2-i)`. Since `2-i` reduces to `4` modulo `P`,
`S` contains `x = (2-i)⁻¹ = (2+i)/5`. Its field trace is `4/5`, which is not in `A`.
An element integral over the integrally closed `A` has integral trace in `A`; hence `x` is not
`A`-integral and `S` cannot be module-finite over `A`.
This adverse-case calculation explains the failed finiteness inference; it is not an additional
Lean theorem of this packet and is not a counterexample to Hilbert's formula. Completing the
base and using the finite semilocal decomposition is a valid upstream route. An alternative
through a decomposition fixed field and a unique prime would need its own full comparison proof;
none is supplied by a bare claim that the localization is finite.

## Application obligations and bounded consistency check

- **Source hypotheses:** global formula/product uses finite Galois `L/ℚ`, the actual ring of
  integers and explicit monogenicity. The generic version includes all AKLB maps, towers,
  integral closure and finiteness. Counting alone is not used as a different formula without
  the separately proved derivative/conductor identity.
- **Constructed objects:** the original global `L`, `𝓞 L`, `P`, `Gal(L/ℚ)`, polynomial generator
  and different are retained. Generic/local comparison objects are named explicitly, not
  silently substituted for global ones.
- **Domain/index coverage:** every nonzero global prime is quantified in the proved monogenic
  case; every automorphism except the identity occurs once; every `i < N` is counted; all
  later summands vanish. The generic transport hypotheses cover every ideal power, including zero.
- **Transition maps:** integral inclusion is injective; trace-dual base images agree; generator
  field extension and the `galRestrict` bijection are proved. Completion/decomposition maps
  and their arithmetic realization remain explicit unresolved inputs.
- **Consumed object:** all global different/divisibility conclusions concern exactly
  `differentIdeal ℤ (𝓞 L)`. The source's local different or a generic monogenic theorem is not
  identified with the global one without the missing comparison.
- **Conventions:** `G_i` uses `P^(i+1)`, with inertia at zero; sums use `range N` and natural
  `|G_i|-1`, with positive finite group cardinalities. Sign reversal of a displacement does not
  change its principal ideal. Prime exponent normalization is unchanged under the proved base map.
- **Local conditions:** global monogenicity is an extra hypothesis, not a universal fact.
  Completed rings must actually be finite and compatible with the trace/filtration maps.
- **Exceptions:** nonzero different and finite multiplicity are proved before exact divisibility;
  identity factors, empty products/ranges, zero exponent, trivial Galois group and the excluded
  zero prime are explicitly checked. No denominator or characteristic restriction is introduced.
- **Downstream:** `GlueConductor.D1_genuine` still requires the full `hH` input. No unchanged
  consumer is declared discharged by a partial result or an assembly helper.

Bounded related-use/repetition scope is the eight new modules, their shape/endpoint checks,
main `Breaks.lean` target and D1 consumer, the distinct local leaf in `I6Base.lean`, the cited
upstream supplying passages, and this note. The rejected inference is localization-implies-
finiteness or local/monogenic proof-implies-global-T20. None is used in the retained proofs;
all stronger unproved conclusions remain explicitly open. This is not a review of other
workers' proof routes, the complete H assembly, historical manuscript incorporation or a new
non-author acceptance. Prior source and draft evidence are preserved, not relabeled accepted.

## Verification and reproducibility

Pinned Lean: `4.35.0`, compiler commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Pinned Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Manifest SHA-256: `f7ce830d517bfbcb4cdcc90bef299da854c9b28653b9accc2b13df2822233779`.
Toolchain-file SHA-256: `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.

- All **eight modules / 880 source lines** were directly recompiled successfully with
  `LEAN_NUM_THREADS=2`, `lean -j2`, over existing pinned dependencies. Compiler times in module
  order below: 2.29, 5.59, 2.60, 2.88, 5.42, 5.19, 3.04, 5.29 seconds; sum 32.30 seconds;
  maximum RSS 6,962,220 KiB. This is an actual scoped rebuild, not a Lake no-op and not a cold
  Mathlib/full-root build.
- Printed full API types expose the extra monogenic/arithmetic hypotheses.
  Every printed axiom report uses only `propext`, `Classical.choice`, `Quot.sound`.
- Unchanged `scripts/audit_kernel.lean` replayed **63 actual declarations / 63 raw occurrences**
  from all eight modules, rechecking one duplicate theorem body and traversing actual dependency
  bodies. Result: `status: passed`, `runtime_declarations_not_replayed: []`, allowed axioms exactly
  the three above, `protocol_acceptance: false`. The actual global target was reported **open**
  with the proposed provider absent. Replay: 19.24 seconds, maximum RSS 16,170,712 KiB.
- The separate statement test checked the independently spelled frozen target by `Iff.rfl`,
  checked that it is a closed `Prop`, and used `Kernel.isDefEq` to reject the monogenic partial
  as a proof of that type. It also checked both closed-provider names are absent.
  Result: passed; 18.01 seconds, maximum RSS 14,927,824 KiB.
- All eight proof SHA-256 hashes were checked again after compilation/replay and remain frozen.
  Existing tracked-source diff and whitespace checks pass. No shared dependency source/build
  write, pin update, root build, commit, push, PR, merge or protected acceptance is performed.

From the repository root with the pinned Mathlib cache already present:

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/HilbertDifferent
for m in Filtration Global Generators Counting Monogenic Transport IntegralClosure Checks; do
  LEAN_NUM_THREADS=2 lake env lean -j2 \
    -o .lake/build/lib/lean/ZInQKernel/Contrib/HilbertDifferent/$m.olean \
    ZInQKernel/Contrib/HilbertDifferent/$m.lean || exit 1
done
```

The standalone replay spec lists exactly those eight modules. Its exports list the actual
partial/bridge/check theorem names above. Use `targets` containing
`GlueConductor.HilbertDifferentFormula` with proposed provider `ZInQ.Contrib.H.T20_holds`;
its expected status is **open**, not proved. Its `headline.declaration` and
`headline.type_declaration` both name `Checks.rational_exact_zero_case`; that self-type check is
not an independent global statement lock. Run the unchanged auditor with a spec and report file:
`LEAN_NUM_THREADS=2 lake env lean -j2 --run scripts/audit_kernel.lean SPEC.json REPORT.json`.
Independent spelling/full-type rejection is a separate check, as described above. Resource
coordination used at most two compiler processes for this work, with two Lean threads each.

Proof-source SHA-256, UTF-8/LF, relative to `ZInQKernel/Contrib/HilbertDifferent/`:

- `Filtration.lean`: `90d48ac43694425a114fa92b83a8e9ec3a113d286aefa26d3e51736800b461ab`.
- `Global.lean`: `465c359d3ca4ca6e1ac0ac42f7003eda14b7919e78c6cb5cecdbc49ec4dd3696`.
- `Generators.lean`: `597cc229fe21f66a3d4cef0ce36d10b01bb188bc93dc0761d0f5b8475f4cadda`.
- `Counting.lean`: `129654953099e6bec28819a8f74f3b5c378d9ebbc0fc3bd8fa2ec624c7221632`.
- `Monogenic.lean`: `9255143279971a0f7df7bae1d1c3640576f165c58d077bb681e2ea8680206045`.
- `Transport.lean`: `4344802b2fbe86d9d3328c50aaeff9d6be9f4741fd6ec8aa47d3fe9d79352922`.
- `IntegralClosure.lean`: `4fd24372f93eea8afc855e5ae24036c2ae910b45f5efb96a638564e0ee471d52`.
- `Checks.lean`: `4a441c98b04a2856492cffe66a504940af2c3afc64a62a151bca80efb4f90acb`.

The exact arithmetic completion/filtration comparisons remain the blocker to a closed global
provider. Successful compilation, type checks and replay of this partial packet do not establish
Astra acceptance, complete inventory coverage, assembled H, or closure of issue37.

## Source Apache-2.0 license

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```

## Addendum — exact closed LOCAL Hilbert leaf (November 13, 2026)

**The LOCAL leaf is now proved; GLOBAL T20 remains open.** The preceding 581-line packet is
preserved byte-for-byte as the original eight-module global partial, with SHA-256
`3adefdd8e0a2a9fd4d954b38b2b30e8d43d1e88e19489673ff0d88cc675f4e08`.
Its eight proof files, 880-line/63-declaration verification and global-open status are unchanged.
This addendum adds only `Local.lean` (93 lines) and `LocalChecks.lean` (59 lines) under the same
owned contribution directory. It does not reinterpret the original partial as a global proof.

### Exact provider and dependency boundary

```lean
ZInQ.Contrib.HilbertDifferent.localHilbertDifferentFormula :
  PkgI6.HilbertDifferentFormula
```

This is a theorem of the exact closed LOCAL proposition at `I6Base.lean` 368–376, with no
extra explicit, implicit, section, monogenicity or `Fact` hypotheses and no universe parameters.
The baseline file examined has SHA-256
`3a2688e5271203cb1d28663fefe3c017426a43dd4c5f4a710f0dabe6de96ce2d`.
The independent definition `LocalChecks.expectedLocalHilbert` includes all original DVR,
complete-base, perfect-residue, finite/torsion-free, separable-fraction-field and Galois-fraction-
field hypotheses. Its body is checked against the actual baseline by `Iff.rfl` and separately
by `Kernel.isDefEq`.

The stronger helper `hilbertDifferentDVR` has the same finite/torsion-free DVR, perfect base
residue field and Galois fraction-field setting but does not require completeness. It concludes
an actual ideal equality, not merely a lower bound or a conditional Hilbert assumption.

One separately authored **shared supplier** is required:

- Module: `ZInQKernel.Contrib.Herbrand.Monogenic`.
- Actual export: `ZInQ.Contrib.Herbrand.exists_dvr_adjoin_eq_top` (not inside the `Monogenic`
  namespace).
- Frozen source SHA-256:
  `a2b761efd76e4ee50a00d277824f943ee34b4f617c273df0d17faf5a8b68e24d`.
- Actual hypotheses: finite torsion-free extension of DVRs, perfect downstairs residue field.
  Neither completeness nor a finite residue field is assumed.
- The full 260-line supplying source was read and freshly compiled without changing its bytes.
  It retains the Tau Ceti/public Mathlib source attribution and the immutable upstream version
  in its header. All its printed axiom reports use only the standard three axioms.

The shared source is **not copied into this production source tree**. Verification used a private
canonical import overlay containing the baseline and original eight-module outputs, plus a fresh
compilation of the frozen supplier at its original module name. The existing project import-root
entry was replaced by that complete overlay; a partial namespace root was not naively appended.
Only private verification outputs were written. The integrator must track the explicit shared
source or establish a proper stack dependency before claiming a production-tree/CI build.
No production CI, registry/provider adoption, commit, push, root build or protocol acceptance is
claimed by this addendum.

### Author's connecting derivation and exact hypotheses

1. **Finite DVRs supply the generic integral-closure data.**
   `integralClosure_of_finite_integrallyClosed A B` is proved using
   `IsIntegralClosure.of_isIntegrallyClosed B A (FractionRing B)`.
   Module-finiteness supplies `Algebra.IsIntegral A B`; the upstairs DVR is integrally closed
   in its canonical fraction field. An `A`-integral element is also `B`-integral, hence lies in
   `B`; conversely every `B` element is integral over `A`. Thus
   `IsIntegralClosure B A (FractionRing B)` is a derived structural input, not a new leaf axiom.
   This does not assert module-finiteness for an arbitrary global-prime localization.
2. **The fraction-field extension is finite with the actual maps.**
   `finite_fractionRing_extension A B` explicitly invokes
   `isAlgebraic_of_isFractionRing`, `IsIntegralClosure.isLocalization` at the downstairs
   nonzero divisors, and `Module.Finite.of_isLocalization`. The canonical fraction-field
   algebra/towers use the same local `FractionRing.liftAlgebra` conventions as the baseline.
   The conclusion is `Module.Finite (FractionRing A) (FractionRing B)`; no completion or new
   field object is substituted.
3. **Monogenicity is discharged, not assumed.**
   The exact frozen shared theorem supplies `β` and `Algebra.adjoin A {β} = ⊤` from the original
   finite/torsion-free DVR and perfect-residue hypotheses. This supplies the extra input of the
   already verified generic `hilbertDifferentAt_integralClosure_of_monogenic`.
4. **Use exactly the local maximal ideal and acting group.**
   Set `P = IsLocalRing.maximalIdeal B`. It is prime and nonzero by the DVR's `not_a_field`
   theorem, and nonunit because it is proper. The generic theorem is applied at
   `K = FractionRing A`, `L = FractionRing B`, and acts through `B ≃ₐ[A] B`.
   `lowerRam_eq_powerInertia` is `rfl`: the actual `PkgI6.lowerRam A B i` is precisely
   `(P^(i+1)).inertia (B ≃ₐ[A] B)` for every natural index. There is no index shift,
   Galois-group replacement, normalization factor or omitted prime.
5. **Exact divisibility gives the LOCAL ideal equality.**
   The generic theorem supplies `N`, triviality at `N`, `P^s ∣ differentIdeal A B`, and
   `¬ P^(s+1) ∣ differentIdeal A B`, where `s` is the full finite range sum.
   The last assertion proves that the different is nonzero. Mathlib's
   `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible` writes it as `P^k`.
   `pow_dvd_pow_iff` for the explicitly nonzero/nonunit `P` turns the two divisibility
   assertions into `s ≤ k` and `¬ s+1 ≤ k`, hence `k=s`. This is the required equality of
   integral ideals, not just equality after passing to the fraction field.
6. **Close only the correct leaf.**
   The final theorem abstracts the exact baseline local quantifiers and invokes this stronger
   helper. It consumes no assumed Hilbert formula. It does not provide
   `GlueConductor.HilbertDifferentFormula`, a number-field completion comparison, a
   decomposition-fixed-field transport, Krasner's lemma or the assembled global D1/H argument.

This is the author's source/application comparison. The two new modules and the frozen shared
supplier were checked against their actual hypotheses and consumers; it is not a non-author
source-first coverage decision or a designated Astra acceptance. The original global consistency
scope and unresolved global transport remain as recorded above.

### Local validation and endpoints

- Both new modules compile cleanly on the unchanged Lean/Mathlib v4.35 pins, through the
  resource gate with `LEAN_NUM_THREADS=2` and `lean -j2`.
  `Local.lean`: 5.86 seconds, maximum RSS 6,960,936 KiB.
  `LocalChecks.lean`: 4.98 seconds, maximum RSS 6,942,184 KiB.
- Full local body comparison and exact provider-type/universe checks pass.
  A separate negative full-type check imports the actual global target and proves the local
  provider does **not** have the GLOBAL T20 type; the global provider remains absent.
  This final check took 7.74 seconds, maximum RSS 8,378,832 KiB.
- `zero_witness_of_trivial_autGroup` checks the trivial automorphism-group case under the
  original Galois fraction-field hypotheses: the different is the unit ideal and `N=0` is
  an exact witness. The subgroup-subsingleton assumption specifies this endpoint case; it is
  not an extra premise of the closed provider. No generator is assumed in the test.
  This validates the empty range, zero exponent and trivial group. The original global
  nonzero-prime, zero-prime-filtration, eventual-triviality and rational endpoint checks remain
  unchanged.
- The unchanged serialized-declaration auditor replayed the **combined 11-module closure**:
  the original eight Hilbert modules, the one frozen shared supplier and the two new local
  modules. It checked **87 actual declarations / 87 raw occurrences**, rechecked one duplicate
  theorem body, and traversed the actual dependency bodies. Result: passed, only `propext`,
  `Classical.choice`, `Quot.sound`, `runtime_declarations_not_replayed: []`,
  `protocol_acceptance: false`. Time 16.52 seconds, maximum RSS 16,200,128 KiB.
  Diagnostic target statuses are `PkgI6.HilbertDifferentFormula: proved_exact_type` and
  `GlueConductor.HilbertDifferentFormula: open`. These are private component diagnostics,
  not registry recognition or a protected acceptance check.
- The original eight proof hashes were checked again and remain unchanged. The frozen shared
  supplier and its private compilation snapshot have identical source hashes. No shared
  package source/build or other contributor's source was modified.

New UTF-8/LF source SHA-256:

- `ZInQKernel/Contrib/HilbertDifferent/Local.lean`:
  `c182655d5f1e346f64ad719c880d352ba090679da88df7ca0db3b94ae73b3b91`.
- `ZInQKernel/Contrib/HilbertDifferent/LocalChecks.lean`:
  `0853551b953c1397a0ea6f02157535e5e8571c08237c939dfa3c774279f74e68`.

After proper shared-source/stack integration, build the shared module first, then these two
modules with the normal project import root. Until then, a reproducibility packet must include
exactly the frozen supplier source above and mirror the complete baseline/own namespace in
its private import overlay. The combined auditor's spec names those eleven modules and the two
actual local/global propositions and providers; the local provider is checked against the
independent local shape, never against a self-comparison or the global target.

**Remaining GLOBAL blocker is unchanged:** the actual local/global different and filtration
transports on the constructed number-field objects must be proved before closing global T20.
The proposed decomposition-fixed-field localization route is being assessed separately and is
not duplicated or assumed by this local proof. Serving-model identity remains unknown;
this is a preliminary author contribution, not Astra acceptance.

## Integrator addendum — explicit shared-source availability

The production candidate now includes the exact shared
`ZInQKernel/Contrib/Herbrand/Monogenic.lean` source proposed in
[PR48](https://github.com/elliotglazer/diophantine-z-q/pull/48), with unchanged
SHA-256 `a2b761efd76e4ee50a00d277824f943ee34b4f617c273df0d17faf5a8b68e24d`.
Its header, proof bodies, namespace and imports are byte-identical to that
source. This is an explicitly included dependency, not a private-overlay or
unregistered-target import. No other Herbrand module is copied.

The current candidate therefore adds ten HilbertDifferent modules, the one
shared monogenic module, and this note. The complete preceding producer note
is retained as a byte-identical prefix, with prior SHA-256
`6492465e241c48e904f6a3bd2b24bad5d6f18265c36556ee8056f6dbd185eadb`.
Its earlier 'not copied into this production source tree' and private-overlay
statements describe the producer verification phase before this integration.
The original eight-module and subsequent local verification records remain
bound to their actual executed snapshots, not relabelled as new full CI.

This addition resolves the concrete source-availability boundary only. Full
normal validation, independent source/application review, and any required
Astra acceptance remain separate. GLOBAL T20, the number-field comparison,
registry/root/policy/pin/manuscript integration and H remain unclaimed. No
mathematical helper or original HilbertDifferent proof source was altered.
