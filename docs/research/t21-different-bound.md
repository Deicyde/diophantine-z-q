# T21: Serre's exact global different bound

**Global status: unclosed.** The exact global proposition
`GlueConductor.SerreDifferentBound` has not been proved by this contribution.
The local DVR theorem is proved, and the pointwise global conclusions below are
proved **conditional on the displayed genuine model/ideal comparisons**.

Role: proof author. Serving model identities are unknown. This note and its
source packet do not provide Astra acceptance, independent inventory coverage,
assembled-proof acceptance, or a release decision.

Scope: new modules under `ZInQKernel/Contrib/DifferentBound/` and this focused
note. No baseline definition, root import, registry, dependency pin, manuscript,
historical acceptance, or controller record is changed. No commit or publication
of a repository revision is part of this packet.

## 1. Frozen global contract

Baseline commit: `a5937595cde3e3db00975b81e5171cdef92c801a`.
The actual definition is at
`ZInQKernel/HDecomp/Conductor/Breaks.lean:350–354`, SHA-256
`7742365fd985fda83c733324394cb4a59db3f083e246dad63279924ce790306d`:

```lean
∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime →
  ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 +
        P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)
```

The intended closed declaration remains **absent**:

```lean
theorem ZInQ.Contrib.DifferentBound.serreDifferentBound :
    GlueConductor.SerreDifferentBound
```

PR41 reference: head `2757349fbd8ca613340b679bbd149f78c2baba6b`,
`ZInQKernel/Targets/H/T21.lean:48–55`, SHA-256
`78341e3fcee4dcb382b739981f3b8171c6619546ae3b6650f863ab15631f81f8`.
This frozen engineering extraction is unregistered and unreviewed. Its
`T21_iff_baseline : T21 ↔ GlueConductor.SerreDifferentBound` is a definition
comparison, not a proof of either proposition. It is not imported as a proof
supplier.

## 2. Actual proved components

All names below are in `ZInQ.Contrib.DifferentBound`.

### Closed local leaf — not global T21

`SerreLocal.lean` supplies the closed theorem

```lean
theorem localDifferentBound : PkgI6.DifferentBound
```

The baseline local definition is
`ZInQKernel/HDecomp/Conductor/I6Base.lean:356–363`. It quantifies over **all**
finite torsion-free extensions of DVRs with complete base, perfect base residue
field, and separable actual fraction-field extension, and concludes

```lean
differentIdeal A B ∣
  maximalIdeal B ^ ((maximalIdeal B).ramificationIdx A - 1) *
    Ideal.span {((maximalIdeal B).ramificationIdx A : B)}
```

No Serre bound, Hilbert formula, monogenicity, uniformizer generation, or degree
equality is assumed in this closed theorem. The upper integer ring's completeness
is derived when constructing the unramified factor; it is not an added premise.
This closes the **local** definition only. The global definition is different.

### The inequality does not require completeness when its factor is supplied

Two additional proved interfaces in `SerreLocal.lean` have **no completeness or
perfectness hypothesis**:

- `differentIdeal_bound_of_factor A B F`, where `F` is an actual
  `UnramifiedDVRFactor A B`. Its remaining context is DVRs, finite/torsion-free
  `A → B`, and separable `FractionRing A → FractionRing B`.
- `differentIdeal_bound_of_residue_surjective_unramified_tower A U B hres`.
  Its full context is DVRs `A,U,B`; the actual algebra maps and
  `IsScalarTower A U B`; finite modules and torsion-freeness for `A/U`, `U/B`,
  and `A/B`; separable `FractionRing A → FractionRing B`;
  `Algebra.IsUnramifiedAt A (maximalIdeal U)`; and
  `hres : Function.Surjective ((residue B).comp (algebraMap U B))`.

Both conclude the same ideal bound for the **original** `differentIdeal A B` and
`(maximalIdeal B).ramificationIdx A`. No bound is stored in the factor record.
No completeness is used to prove these inequalities. Completeness and
perfectness occur only in the factor-existence wrapper.

### Constructed unramified intermediate DVR

`UnramifiedFactor.lean` proves

```lean
UnramifiedFactor.nonempty_of_perfect
  [IsAdicComplete (maximalIdeal A) A]
  [PerfectField (ResidueField A)] :
  Nonempty (UnramifiedDVRFactor A B)
```

The complete common context is DVRs `A,B`, `Algebra A B`,
`Module.Finite A B`, and `FaithfulSMul A B`. The finite-residue specialization
replaces perfectness by `Finite (ResidueField A)`. A separable-residue version is
also proved. These are existence proofs, not existence premises.

The record contains:

```lean
carrier : Subalgebra A B
isDvr : IsDiscreteValuationRing carrier
finiteBase : Module.Finite A carrier
faithfulBase : FaithfulSMul A carrier
finiteTop : Module.Finite carrier B
etale : Algebra.Etale A carrier
residue_surjective :
  Function.Surjective ((residue B).comp carrier.val.toRingHom)
```

The carrier is literally `A[b]` inside `B`, with `b` obtained by Hensel lifting a
primitive residue element's lifted monic minimal polynomial. The proof supplies
upper completeness from finite base change and cofinal ideal-power filtrations,
then proves the local, finite, faithful, etale DVR and residue-surjectivity facts.
Canonical locality, residue-field equivalence, maximal-ideal-map equality,
unramifiedness and completeness interfaces are also proved.

### Uniformizer, degree and derivative — no fake power basis

- `Generator.lean` proves that every upper uniformizer generates in the finite
  residue-surjective DVR case. It constructs truncated residue digits for every
  natural power, uses the actual equality `m_A B = m_B^e`, and applies the pinned
  Nakayama theorem `Submodule.le_of_le_smul_of_le_jacobson_bot` with the proved
  maximal-ideal/Jacobson hypothesis.
- `Degree.lean` reduces Mathlib's finite-flat `e·f = rank` identity to the single
  maximal prime of a DVR. A generating uniformizer reduces to zero and makes the
  residue map surjective, hence `f = 1`. The ring rank is identified with the
  actual fraction-field rank, and the actual minimal polynomial has degree `e`.
  Degree equality is derived, not supplied to the final local inequality.
- `Monogenic.lean` derives fraction-field generation from ring generation by
  writing every fraction as a ratio of two elements of the generated ring. The
  actual order conductor is then the unit ideal, so Mathlib's conductor/different
  identity proves that the actual different is generated by the derivative of
  the actual minimal polynomial.
- `Valuation.lean` proves normalized valuation restriction by `e`, distinct finite
  term valuations modulo `e`, and the finite-sum minimum formula. Zero terms have
  infinite additive valuation; empty and all-zero families are covered.
- `Local.lean` includes every derivative index in `Fin e`. Distinct finite
  valuation residues prevent cancellation. The leading derivative term gives
  `v_B(f'(π)) ≤ e - 1 + v_B(e)`. This is transported to the actual different ideal.
- `Tower.lean` uses actual unramifiedness to prove that the lower different is the
  unit ideal, and then proves that the unramified intermediate DVR changes
  neither the actual different nor the actual ramification index.

The fraction-field implementation explicitly chooses the canonical composite
`U → B → FractionRing B`, avoiding an algebra-instance diamond with an alternate
subalgebra instance. Scalar-tower and integral-closure arguments concern these
actual maps; this is not a target-definition change.

### Actual global normalization and exceptional cases

`Global.lean` proves, for every nonzero natural `n` and every `P | p` in the exact
number-field setting,

```lean
multiplicity P (Ideal.span {(n : 𝓞 L)}) =
  P.ramificationIdx ℤ * padicValNat p n
```

It also proves that lying above a natural prime excludes `P = ⊥`, that the global
ramification index is positive, that the global different is nonzero, that
prime-power divisibility is the characteristic property of its multiplicity,
and the complete `e = 1`/unramified case of the exact global nondivisibility.
There is no Galois hypothesis.

The integer normalization excludes `n = 0` explicitly: multiplicative valuation
of zero is zero and additive valuation is infinite, whereas `padicValNat p 0`
uses a finite junk convention. It is specialized to `n = e` only after proving
`e > 0`.

`Comparison.lean` proves the local/global **ramification-index equality** from
actual prime images: if the base maximal ideal is generated by `p` and the upper
maximal ideal is the image of `P`, then

```lean
(maximalIdeal B).ramificationIdx A = P.ramificationIdx ℤ
```

This follows from ideal multiplicities and the global integer normalization;
a Tau Ceti local-field normalization wrapper is not an input.

## 3. Conditional global reductions and precise remaining interface

`Transport.lean`, `Comparison.lean` and `GlobalReduction.lean` contain genuine
proved comparison/reduction lemmas, but they do **not** construct local models
for every allowed number field and prime.

The final `GlobalReduction.lean` interfaces are:

```lean
serreDifferentBound_atPrime_of_factor_model
serreDifferentBound_atPrime_of_unramified_tower_model
serreDifferentBound_atPrime_of_completeDVR_model
```

All conclude exactly

```lean
¬ P ^ (P.ramificationIdx ℤ - 1 +
    P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
  ∣ differentIdeal ℤ (𝓞 L)
```

Their common **unproved model-construction inputs** are genuine finite faithful
DVRs `A → B` with separable actual fraction fields, a faithful actual algebra map
`𝓞 L → B`, and these exact facts:

```lean
maximalIdeal A = Ideal.span {(p : A)}
P.map (algebraMap (𝓞 L) B) = maximalIdeal B
(differentIdeal ℤ (𝓞 L)).map (algebraMap (𝓞 L) B) = differentIdeal A B
```

The factor interface additionally takes a genuine `UnramifiedDVRFactor A B`.
The tower interface instead takes an actual finite faithful unramified,
residue-surjective DVR tower `A → U → B`, with all algebra/scalar-tower inputs
listed above. These two interfaces need no completeness or perfectness. The
complete-model interface needs completeness and perfect base residue field only
for its **local** rings and invokes the proved factor construction.

The proof then derives `e_local = e_global`, the integer valuation normalization,
the correct ideal multiplicity, and the exact `+ 1` nondivisibility. No global
bound is an input.

**To close T21**, a supplier must construct such a model and prove these facts
for **every** `L,p,P` in the frozen global contract, including nongalois `L`.
There is no theorem supplying that family in this contribution, and no axiom,
`Fact`, unsupported field map or existence hypothesis is used to call it closed.
In particular a Galois-only Hilbert formula cannot close this nongalois target.

### Two globalization routes remain open

1. **Completions.** Construct the actual base and upper completed integer rings,
   prove their finite faithful DVR structures and base completeness/residue
   properties, and prove the global different's actual image equals their
   different. Simultaneous base localization alone does not prove this completion
   comparison. Direct `B_P / ℤ_(p)` is not generally module-finite when several
   primes lie over `p`.
2. **Algebraic decomposition/localization proposal — not formalized here.** In a
   Galois closure `M` of a nongalois `L`, let `D,I,H` be decomposition, inertia,
   and the subgroup fixing `L`; let `H₀ = D ∩ H`, `F = M^D`,
   `E = M^H₀`, and `U = M^(I H₀)`. Proposed comparisons would make `F/ℚ` and
   `E/L` unramified with residue degree one at the selected primes, and make
   `U/F` unramified with `E/U` residue degree one. One must actually construct
   the fields, maps and primes, prove unique-prime coverage and genuine finite
   base localizations, and identify the global/local differents via towers and
   localization. The supplied-tower inequality then applies without a complete
   base. This proposal is **not** a supplying theorem, fixed-field diagram, or
   proof of the required model maps in this packet.

Global different/localization and fixed-field comparisons are coordinated as a
separate foundation. They are neither duplicated nor assumed here. The local
inequality does not depend on an assumed T20/Hilbert formula.

## 4. Source-first nine local/global application obligations

These are authored source comparisons, not independent acceptance. Each records
what is available, what the target needs, why the proved side matches, and where
the remaining construction/identification is open.

1. **Source hypotheses.** Available: the proved complete-DVR local theorem and
   the no-completeness supplied-factor/tower inequalities. Required by T21:
   models derived from only the number-field/prime-above hypotheses. Constructed:
   generic DVR factor witnesses when the local hypotheses hold, not an additional
   global-field hypothesis. Why they match locally: all finite, faithful,
   separable, unramified and residue-surjective inputs are proved or explicit in
   the compiled types. Evidence: `UnramifiedFactor.lean`, `SerreLocal.lean` and
   `Audit.lean`. **Global model construction remains unresolved.**
2. **Constructed objects.** Available: the actual carrier `A[b] ⊂ B` and canonical
   inclusions, or a supplied actual DVR tower. Required: the rings associated
   with the specific global `L,p,P`, not unrelated rings. The factor's DVR,
   finite/faithful and etale properties are genuine instance proofs; no bound is
   a record field. Evidence: `UnramifiedFactor.lean` record and constructor,
   `SerreLocal.lean` consumers. **Their identification with each global prime's
   model is unresolved.**
3. **Domain and index coverage.** The derivative proof uses all `Fin e`, covers
   zero coefficients and derives degree `e` from the actual finite-module rank.
   The residue-digit generation proof covers every element and every natural
   power. Evidence: `Valuation.lean`, `Degree.lean`, `Generator.lean`,
   `Local.lean`. T21 requires all number fields and every prime above `p`, with
   no Galois restriction. **That entire global model family is not supplied.**
4. **Transition/comparison maps.** Local maps are the actual subalgebra/field
   inclusions, with canonical fraction-field scalar towers. Available global
   reductions extend ideals along the actual `𝓞 L → B` map and prove
   multiplicity preservation when `P` maps exactly to the maximal ideal.
   Required: prove the three model equalities displayed in §3, with the actual
   base `ℤ`, not merely `𝓞 ℚ`. Evidence: `Monogenic.lean`, `SerreLocal.lean`,
   `Transport.lean`, `Comparison.lean`. **The global different-image equality
   and full model-construction maps are open.**
5. **Identity of the consumed object.** The target consumes exactly
   `differentIdeal ℤ (𝓞 L)`. The local proof computes the derivative of the actual
   minimal polynomial of an actual generator, not an order different. The global
   adapter consumes the literal image equality of this exact global different
   with the actual local different. Evidence: `Monogenic.lean`, `Local.lean`,
   `GlobalReduction.lean`; Mathlib `Different.lean:481–483,533–564`.
   **That literal global/local identification is not proved for all `L,p,P`.**
6. **Coefficient/normalization conventions.** Available and proved:
   multiplicative adic valuation is `exp(-v_P(x))`; ideal divisibility is reverse
   inclusion; `v_P(n) = e·padicValNat p n` for nonzero `n`; local `e` is the actual
   `Ideal.ramificationIdx`, and `+ 1` means one power above the allowed exponent.
   Why they match: normalized valuation restriction, prime images and ideal
   multiplicities are proved, not substituted by a proportional quantity.
   Evidence: `Global.lean`, `Valuation.lean`, `Comparison.lean`,
   `Transport.lean`. **Normalization is discharged for a matched model; the
   existence/identification of every global model is still open.**
7. **Local conditions.** Perfectness and completeness occur only in proved
   factor existence, with upper completeness derived. The supplied-factor/tower
   inequalities require neither. For number-field completions these properties
   must be consequences of their construction, never extra target assumptions;
   for the proposed algebraic localization route genuine finite unique-prime
   localizations must be proved. Evidence: `UnramifiedFactor.lean`,
   `Generator.lean`, `SerreLocal.lean`. **The global-to-local construction side
   remains unresolved.**
8. **Exceptional cases.** Proved: `P = ⊥` is excluded by lying above nonzero `(p)`;
   `e = 0` is excluded by positivity; `e = 1` gives the full global unramified
   nondivisibility; zero coefficients/all-zero/empty sums have infinite additive
   valuation; zero image of `e` makes the ideal-form local bound empty. There is
   no excluded prime, including `2`, in these arguments. Evidence:
   `Global.lean`, `Valuation.lean`, `SerreLocal.lean`, `Audit.lean`.
   **The arbitrary ramified global case, including dyadic fields, is not closed
   without the open model comparison; small examples do not close it.**
9. **Downstream consumption.** `GlueConductor.D1_genuine` at
   `Breaks.lean:398–403` needs the exact global nondivisibility to bound the global
   Hilbert exponent. `GlobalReduction.lean` delivers that precise conclusion
   under its explicit model facts, but no closed global provider or registration
   is supplied. Its Galois-specific consumer does not weaken T21's nongalois
   quantifier. Evidence: baseline `Breaks.lean:360–404`, the frozen T21 reference,
   and `GlobalReduction.lean`. **Downstream global discharge and full assembly
   remain pending, not accepted.**

## 5. Exact sources, versions and attribution

Pinned Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (`v4.35.0`).
Lean: `4.35.0`, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
No pins are updated; no dependency tree is installed or modified.

Read Mathlib sources include:

- `RingTheory/DedekindDomain/Different.lean`: actual different, derivative,
  conductor, tower, unramifiedness and nonvanishing facts; SHA-256
  `d128a5d3a339a6f096d97511e27e8948c2db1b3e8c330775bdd64121f6e7d014`.
- `RingTheory/RamificationInertia/Ramification.lean`: actual index, positivity,
  index/multiplicity comparison; SHA-256
  `21f8b46d93925fdbae8c5ced0bcf78049d5be305a34ca9602c7b34df20aebe02`.
- `NumberTheory/RamificationInertia/Valuation.lean`: normalized valuation
  restriction; SHA-256
  `b3c5e18ee2e522127dff5f40a94d487758e77e874959c2c76ad843eaa0b4a0c5`.
- `RingTheory/RamificationInertia/Basic.lean`,
  `RingTheory/LocalRing/Length.lean`, `RingTheory/PowerBasis.lean`,
  `RingTheory/Adjoin/PowerBasis.lean`, `RingTheory/Nakayama.lean`,
  `RingTheory/IntegralClosure/IsIntegralClosure/{Defs,Basic}.lean`,
  `RingTheory/Localization/FractionRing.lean`,
  `RingTheory/DedekindDomain/AdicValuation.lean`, and the pinned p-adic valuation
  sources. Actual statements were read before application/compatibility fixes.

Actual Tau Ceti source was read at
`TauCetiProject/TauCeti@a6027b1d24fcb935c53bd5b50d11b40991cda418`, whose toolchain
is `v4.36.0-rc2`. Its source headers and `LICENSE` identify Apache-2.0. This is not
an installed dependency. Minimal extracts and shorter ring-level proofs compile
on the unchanged 4.35 pin, with attribution and modified-file notices retained.

Read supplying proofs include:

- `TauCeti/NumberTheory/LocalField/Different/{Wild,Eisenstein,Monogenic,Tower}.lean`:
  actual local upper bound, unramified reduction and derivative no-cancellation.
- `TauCeti/NumberTheory/LocalField/Eisenstein/{PowerBasis,TotallyRamified}.lean`,
  `LocalField/Monogenic.lean`, and `LocalField/Unramified/{Existence,Factorization}.lean`.
- `TauCeti/RingTheory/Valuation/Orthogonality.lean`,
  `DiscreteValuationRing/Basic.lean`,
  `DedekindDomain/Different/Monogenic.lean`,
  `FieldTheory/IntermediateField/Adjoin/EqTop.lean`, and
  `RingTheory/LocalRing/Monogenic.lean`. The latter's general monogenic-existence
  port is not duplicated; the needed DVR uniformizer case is proved directly
  from truncated digits and pinned Nakayama.
- `TauCeti/RingTheory/Henselian/Basic.lean`, `AdjoinRoot/Basic.lean`,
  `LocalRing/Etale.lean`, `Etale/AdjoinRoot.lean`,
  `DiscreteValuationRing/Etale.lean`, and
  `AdicCompletion/{Pi,Finite,Pow}.lean`: the short ring-level factor-construction
  and completeness suppliers, with exact provenance retained in
  `UnramifiedFactor.lean`.
- `TauCeti/NumberTheory/NumberField/LocalGlobal/Different/{Basic,Exponent,Wild}.lean`
  and `TauCeti/RingTheory/DedekindDomain/Different/Localization.lean`: actual
  prior global/local source routes were read, but their global transport closure
  is not ported here. Exponent's later Hilbert/Galois section is not needed by
  the Serre arithmetic. Simultaneous base localization must not be substituted
  for a completion or unsupported single-prime localization.

The baseline's Serre book numbering remains unverified in this contribution.
The kernel proofs use identified Mathlib proofs and the ported/project proofs,
not a bare published-theorem citation or additional arithmetic axiom.
Historical status: prior related formal proof routes located; the exact pinned
project global comparison is still unresolved. This is not a claim of a new
mathematical gap or of manuscript incorporation.

## 6. Reproduction and trust boundary

Compile only the owned modules on the pinned baseline, with `LEAN_NUM_THREADS=2`
and no more than two compiler processes. A dependency-safe order is:

```text
Global, Valuation, Monogenic, Degree, Local, UnramifiedFactor, Generator,
Tower, SerreLocal, Transport, Comparison, GlobalReduction, Audit
```

For each module, use `lake env lean` on its repository-relative source and, when
needed for its later imports, emit its `.olean` to the private build tree. This
is not a request to update pins, build the whole root candidate, or modify shared
packages. The private immutable review packet includes complete source bytes,
checksums, a manifest, this public-safe note, and a captured focused audit.

The final focused `Audit.lean` run exits `0`, without compiler warnings/errors.
It displays complete selected types, verifies the closed local leaf, and reports
only subsets of

```text
[propext, Classical.choice, Quot.sound]
```

for the audited entry points and dependencies. It also checks unramified dyadic
and odd-prime specializations, empty/all-zero sums, and the zero integer-image
ideal bound. No source uses `sorry`, an additional axiom, `Fact` containing a
bound, `native_decide`, unsafe/extern/implemented-by replacement, or a target
redefinition. The forbidden-keyword scan's sole hit is the word “axiom” in the
`Audit.lean` documentation heading, not a declaration.

This is focused compilation/type/axiom evidence, not the full candidate kernel
replay or an independent mathematical/encoding acceptance. Those reviews must
bind the exact frozen source bytes and all eventual global comparisons. The
registry, manuscript and bound historical sources are unchanged; no historical
hash refresh or independent approval is generated. This is a non-release proof
contribution, not an official-record or manuscript release.

## 7. Source fingerprints

All paths below are relative to `ZInQKernel/Contrib/DifferentBound/`; hashes are
SHA-256 of the exact UTF-8 source bytes, with no normalization:

```text
e84b006e9e6189536ddcf2f6eb51cadcda0365f258d8fa7756f4b833f39e5f1a Audit.lean
5fc32b6844dfda47b6a43d2757d5d0691d3082327081444d8102b0deb31d5cc7 Comparison.lean
0d2973610e8ef83ff4e37f665e4d4a71b591b0777a7c6c2240984843d225fe56 Degree.lean
33bc239d9a7c3feaccb8d8d20757d69309b10f455c4fc048734a095a933308a0 Generator.lean
f514cc392c4f22ef609fa477b11fb7fe0245dda62a9aff22187b843ed5f30ae4 Global.lean
c9796dc4e185381bba3aba3fe6e45dbd55be9bc0667a6dc094ba6c47bf203314 GlobalReduction.lean
8a8fb6c288445930fed399d8ff12a391c772bf6462026138e76822ad7d43af39 Local.lean
13a674b9940e2c63409591c99b8206d10a4389f65def05360fcc1c58f4dbd88e Monogenic.lean
6ba72e78bbf889039e850e29ac7c3a597dbd2ec8101954a869fb6a74bf5a6790 SerreLocal.lean
884884b21be4e67579d7170ccc7734f72f70e013092df0d259476937d2037315 Tower.lean
3850489c08febfa9c543e8df4ca7cc27c1749c326d21cd6dfc29a80febbad7e4 Transport.lean
53b92457110b1684e10af48383f8bf11de1017ddc991d4a042dd2c56a6ce4d1b UnramifiedFactor.lean
36d9f87de5960e69eadc165e644236d708878cb086dbd96db4321a2cbb10ee3f Valuation.lean
```

This note's own hash belongs in the packet manifest rather than a self-reference.
The global-open qualification applies to the entire packet, even though the
local theorem and the conditional pointwise reductions compile.
