# T18: closed Frobenius-density proof with finite-set avoidance

## Result and scope

On main base `a5937595cde3e3db00975b81e5171cdef92c801a`, this contribution
provides the **closed, kernel-checked** theorems
`ZInQ.Contrib.FrobeniusDensity.frobenius_dense_avoiding_finite_set` and
`ZInQ.Contrib.FrobeniusDensity.t18_holds` in `ClosedProof.lean`.
Their exact conclusion includes every open subgroup of the absolute Galois
group, every absolute automorphism, every finite exclusion set, an actual
valuation above an actual rational prime outside that set, an absolute
**arithmetic** Frobenius at that valuation, and `tau⁻¹ * sigma ∈ U`.

`AxiomAudit.lean` compiled successfully and printed only `propext`,
`Classical.choice`, and `Quot.sound` for the full T18 theorem, the actual
natural-density supplier, the finite Chebotarev provider, and every new
transport and finite-set lemma it audits. No Chebotarev premise or `Fact`
instance for Chebotarev is assumed.

This is a focused formal contribution, **not** target registration, independent
Astra acceptance, manuscript incorporation, an assembled proof of H, or a record
release. The draft H-target extraction remains unregistered and unreviewed at
its frozen version. Root imports, compiler/package pins, target/contract files,
audit/check scripts, review policy, and other workers' sources are unchanged.
No commit, push, pull request, merge, human outreach, or protected-controller
operation is part of this contribution.

The only source outputs are `ZInQKernel/Contrib/FrobeniusDensity/*.lean` and this
note. Derived compiler outputs remain separate from source. The unmodified
frozen-headline checker passed with `python3 -B scripts/check_target.py`.

## Exact statement reference and minimal faithful definitions

The reference is public draft PR 41 at revision
`2757349fbd8ca613340b679bbd149f78c2baba6b`:

- `ZInQKernel/Targets/H/T18.lean`, SHA-256
  `f2d4b41813a27a0b2178f9b0416ef9a5dcf2edfb9ada80516dd51b5f5c0fa751`;
- `ZInQKernel/Targets/H/Defs/HSyn.lean`, SHA-256
  `180072ef6d408586f281c7f25ff7f78fbcafd45383f61c9d5269ba696d252402`.

`Defs.lean` faithfully copies only the needed declaration bodies, under the
contribution's own namespace: `Qbar := AlgebraicClosure ℚ`, its absolute
algebra-automorphism group `GQ` with Mathlib's Krull topology, `LiesOver`,
`IsArithFrob`, and the exact closed T18 proposition. No unregistered target is
imported, and no unrelated representation or modular-form definitions are
introduced. `AxiomAudit.lean` checks the local proposition against the fully
expanded reference-shaped statement by definitional equality.

`LiesOver v p` means that `p` is in `v.nonunits`. `IsArithFrob tau v p` requires
stabilization of `v` and `tau x - x ^ p ∈ v.nonunits` for **every** `x ∈ v`.
The exponent is forward `p`-power residue Frobenius, not its geometric inverse.
The proof never substitutes a conjugacy-class count for the required valuation
and absolute-automorphism witnesses.

## Actual external proof, version, and port closure

The actual supplier is
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti), revision
`1f9b4414105d86e487a4ac4c3d3397076a44d0d2`:

- `TauCeti/NumberTheory/Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean`,
  declaration `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`;
- SHA-256 of that original source file:
  `18174e14acb8c8ef59ccb1224e9326f2cca85ef5fadb3aa7fa38582e8cd2fe68`;
- its actual theorem has an actual proof and no extra Chebotarev premise;
- source toolchain: Lean `4.35.0`; source Mathlib revision
  `074063781836922cb02701cd12943c9f51731afa`;
- this contribution instead compiled it against the **unchanged project pin**,
  Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean `4.35.0`.

The exact transitive Tau Ceti **module-import closure** of that supplier contains
285 Lean modules and 55,972 original source lines. Only that closure is copied,
not the full Tau Ceti library. Each `TauCeti.X.Y` module is relocated to
`ZInQKernel.Contrib.FrobeniusDensity.Tau_X_Y`; corresponding Tau Ceti imports are
rewritten to those owned flat modules. Original mathematical declaration bodies
are retained, with original copyright/author headers and an added port notice.
Mathlib sources are not copied or edited. All 285 modules compiled successfully.
This is the minimal closure at the retained upstream module interfaces, **not a
claim of declaration-level minimality**; unused declarations within those files
could be further pruned in a separately checked refactor.

A separate producer check fetched the immutable upstream archive again and
verified all 285 local port files byte-for-byte against the deterministic import
relocation and added-notice transformation. No mathematical declaration body
differed. That check binds the producer snapshot before the two publication EOF
normalizations documented in the final addendum below.
The earlier 295-file owned Lean-source snapshot (before adding the separate
frozen-reference check module) has sorted-path manifest SHA-256
`45a369f1d0c24ebc4521a48df53502f18510940ad5264ce3a825dedc1283f2e9`.
Its serialization is sorted repository-relative lines
`path SHA256(raw-file-bytes)\n`, hashed as UTF-8; derived outputs and this note's
self-reference are excluded.

The producer's pre-publication 296-file owned Lean-source snapshot, including
`ReferenceCheck.lean`, has sorted-path manifest SHA-256
`ac2ebd359c546e00f2a9e05dfbaca306ddedd046ff415b5d62271f7804c86761`.
`ReferenceCheck.lean` itself has SHA-256
`0e6d93b7d397c2419682c6526df61b5385c1a5cf83f27a446dec3007d24708b1`.

The producer's source-only module/source/upstream-version map has SHA-256
`68041bcf1017358133e75ad66d3e611ebd94da8ca8caa0f2646c32cafe9217f7`;
it covers 296 local modules, with all 285 upstream port paths identified.
The cold-sequence summary SHA-256 is
`4399ea3ec60b9b219b72fb4a09fd519a8ba09d949194c299b6b71f155046ee95`;
the forced-warm per-module report SHA-256 is
`bc28391247d66d6b9f8630e2c02ca3327204e879cece4e33d4d2080a82428730`.
These are preserved producer source/evidence records, not compiled artifacts;
the current publication formatting has its own binding below.

For comparison, the newer inspected snapshot
`30f41378f0cb1d569f51d8a4d0cb74aea8a80e44` uses Lean `4.36.0-rc2` and Mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`; its enumerated import closure has
366 Tau Ceti modules and 82,621 source lines. That newer density snapshot is
**not** the port used here. Its density source SHA-256 is
`27728827336428472e9f677c6ca2dfaa3ccdd94a7be9b90383282e8d84a83801`.
Two small valuation-power lemmas in `ValuationAction.lean` are separately adapted
from `TauCeti/RingTheory/Valuation/FrobeniusElement.lean` at that newer revision,
lines 43–74; their 4.35 compilation and standard-axiom reports also passed.

The density proof's substantive chain is analytic/cyclotomic weighted
Chebotarev and the crossing argument, `frobeniusPsi_asymptotic`, removal of
higher prime powers to obtain `frobeniusTheta_asymptotic`, Abel summation and
logarithmic-integral transfer to prime counting, the trivial-extension theorem
supplying the all-prime denominator, and the natural-density ratio
`card(class) / card(Gal)`. `DensityAxiomAudit.lean` printed the supplier's full
elaborated type and only the three standard axioms. Its parameters are genuine
number fields, a Galois extension, and a conjugacy class, not an assumed
Chebotarev fact.

## From actual finite density to the exact T18 witnesses

### 1. Positive density and arbitrary finite exclusions

`FiniteDensity.lean` invokes the actual proved natural-density theorem for the
class of the specified finite automorphism. The class is nonempty and the finite
Galois group has nonzero cardinality, so the density is strictly positive.
A finite prime-ideal set has density zero; hence the Frobenius prime set is
infinite. Northcott finiteness of bounded absolute norms makes its norms
arbitrarily large, without invoking a separate prime ideal theorem in this
last elementary implication.

Over `ℚ`, `Rat.HeightOneSpectrum.absNorm_asIdeal` identifies that norm with the
actual rational prime. Choosing it above `S.sup id` excludes **every** entry of
`S`, including any nonprime entries. Empty `S` is covered by the ordinary bottom
value of the supremum, rather than an undefined maximum.

The Tau Ceti prime-set membership theorem
`exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk` realizes the **specified
representative itself**, not merely some conjugate, at a prime above the base
prime. `ArtinSymbol.lean` supplies the exact conjugation-and-prime-transport
argument. `IntegersRat.lean` identifies the base ideals, residue cardinalities,
and Frobenius conditions over `𝓞 ℚ` and `ℤ`. Formal unramifiedness composes
through the bijective structure map `ℤ → 𝓞 ℚ`.

This proves `exists_finite_arithFrob_avoiding` and discharges the exact baseline
finite propositions `PkgI6.ChebotarevExists` and `GlueC10.ChebotarevExists`, via
`chebotarevExists` and `chebotarevExists_C10`. Those baseline propositions were
unproved interfaces; they are not treated as proof suppliers.

### 2. The same integral prime gives an actual valuation

The existing, closed `GlueC10.frobLift` in
`ZInQKernel/HDecomp/C10/C10.lean` supplies an absolute automorphism with the
specified finite restriction and Frobenius congruences on the integral closure
of the integers. Its integral-only `IsFrobAt` is **not** the valuation-level
`IsArithFrob` of T18, so a further transport is required.

`ValuationLift.lean` proves that the integral closure of the integers in the same
algebraic closure, localized at the supplied prime above `p`, is a valuation
ring. For an arbitrary algebraic number, put it in a finite number field,
contract the prime, and use that field's Dedekind-domain DVR localization.
Either that number or its inverse lies in the local ring, and the localization
map commutes with the actual field inclusions.

`ValuationRealization.lean` constructs `valuationOverIntegralPrime` at this
**same** integral prime. Mathlib's Frobenius-localization theorem extends the
integral congruence to every local fraction. It supplies the forward `p`-power
congruence on the entire valuation ring, not just on global algebraic integers.
`ValuationAction.lean` proves that a nonzero power-residue congruence forces
stabilization, preserves maximal-ideal membership along restriction, and
transports Frobenius as `g * tau * g⁻¹` at `g • v`.

The resulting closed `valuation_frobLift` has the exact output
`LiesOver v p ∧ IsArithFrob tau v p ∧ restrictNormal tau E = sigma`.
The absolute automorphism is retained from the integral lift; it is **not
chosen again** after constructing the valuation.

### 3. Every open subgroup, with the correct orientation

`Topology.lean` proves that every open subgroup `U`, including nonnormal ones,
contains the fixing subgroup of a finite Galois subfield. This uses the normal
closure of a finite field in the Krull neighborhood basis; it does not assume
that `U` itself is normal.

Apply finite Chebotarev to the restriction of the original absolute `sigma` to
that finite Galois field. Apply the valuation lift to the resulting specified
finite Frobenius. Matching restrictions means `tau x = sigma x` for every
member of the finite field, so `tau⁻¹ * sigma` fixes that field and belongs to
`U`. `ClosedProof.lean` composes exactly these witnesses and these maps.

## Source-to-consumer application obligations

This is an author-side reconstruction of the changed route, not independent
protocol acceptance:

1. **Source hypotheses.** The density supplier's number fields and finite Galois
   extension are instantiated at `ℚ` and the constructed finite Galois field;
   the class is the class of the actual restricted `sigma`. The finite prime's
   unramifiedness is retained for the existing lift's uniqueness step.
2. **Constructed objects.** All fields, integer rings, prime ideals, valuation
   subrings, automorphisms, and counts are the actual Mathlib/Tau Ceti objects.
   No abstract Frobenius label or replacement automorphism is consumed.
3. **Domain and index coverage.** All open subgroups are covered by the finite
   normal fixing-subgroup lemma. All elements of the valuation ring are covered
   by Frobenius localization; each algebraic number is covered by a finite-field
   localization. All members of the exclusion set are bounded by its supremum.
4. **Transition maps.** Integer-base identification, ideal contraction,
   localization maps, algebraic-closure inclusions, and normal restriction are
   explicit in the cited helper files. The prime norm equals the rational prime;
   Frobenius retains exponent `p` and restriction takes no inverse or power.
5. **Consumed-object identity.** `valuation_frobLift` retains the same absolute
   `tau` and its exact finite restriction. The final coset computation consumes
   that equality, not equality of conjugacy classes.
6. **Coefficient and normalization conventions.** The base integer rings
   `𝓞 ℚ` and `ℤ` are identified by their actual ring equivalence. Density is the
   inclusive-cutoff prime-count ratio. Frobenius is forward arithmetic Frobenius;
   the target difference is specifically `tau⁻¹ * sigma`.
7. **Local conditions.** Finite unramifiedness is used exactly where required.
   The valuation is above `p` because `p` remains in its maximal ideal. The
   local congruence covers denominators outside the same prime.
8. **Exceptional cases.** Prime positivity excludes zero exponents and zero
   contracted primes. Nonempty conjugacy classes and finite nonempty Galois
   groups exclude zero density denominators. Empty/nonprime exclusion entries,
   zero algebraic numbers, and nonnormal subgroups are included in the proved
   statements; no exceptional case is silently discarded.
9. **Downstream consumption.** The final theorem is exactly the closed local
   T18 statement. The finite baseline interfaces are also discharged. No claim
   is made that H, T19, the headline theorem's remaining premises, or manuscript
   incorporation are thereby completed.

## Verification and reproduction

The producer compilation/replay records in this section and the scoped replay
section below bind the pre-publication source snapshot `ac2ebd35...4c86761`.
They are preserved as executed, not relabelled as post-formatting reruns. The
separate publication formatting check and its current source binding are in
the final addendum.

The exact contribution is 285 port modules and 11 local definition, proof, and
report/check modules. `ReferenceCheck.lean` separately copies the frozen draft
T18 body verbatim into a closed local proposition, without importing the draft
target. The port closure and the complete proof chain compiled under
Lean 4.35.0 with `LEAN_NUM_THREADS=2`, never more than two contribution compiler
processes, and only scoped module invocations. Shared Mathlib and baseline
sources/pins were read-only. No whole-project build was run.

Each module was checked with the scoped form
`LEAN_NUM_THREADS=2 lake env lean -o .lake/build/lib/lean/<module>.olean <module>.lean`,
using the owned dependency order. `AxiomAudit.lean`, `LocalAxiomAudit.lean`, and
`DensityAxiomAudit.lean` provide reproducible type and axiom reports. The expanded
T18 statement has no extra explicit, implicit, typeclass, or section hypothesis.
The unchanged `python3 -B scripts/check_target.py` printed an exact frozen-target
match. Source scanning found no forbidden proof/runtime mechanisms or
unregistered target imports in the owned modules.

Critical source SHA-256 bindings:

- `Defs.lean`: `1f527e38e479484fa367ca3191becbf5ad8c2a2fd27e3ca703c38d171deaea34`;
- `ValuationAction.lean`: `1355d2761e392165e62361aff0a40fb831e771fe279d09d4932cbfa93c4bf231`;
- `ValuationLift.lean`: `b431ee9e658d3b599c43081cb7673a508fbcf5421361ecafcb6c421b26693017`;
- `ValuationRealization.lean`: `3d802d2011350c52c6dca73b44d5f266a3fd57b875df05d5816acc08669fc866`;
- `Topology.lean`: `290188e01b47ea7a7fa61a7bcb9d59bac6a7bfaad10e828a8eef290d57a76870`;
- `FiniteDensity.lean`: `0bac12285589880bf434d42c930bc69fc5aef24ed975c34ac75f7d897cfd3f87`;
- `ClosedProof.lean`: `8dd3794ce7adba453182ef21398a8175502527929a706cb26f45052e971911ad`;
- `AxiomAudit.lean`: `500e3964259cdfc2113f691fc1a40f44edf163b37e11546281bfac5857875e38`.

The port also passed a separate **fresh derived-cache rebuild** of all 285
modules: 759.64 seconds wall clock, including resource-gate wait. Every owned
port dependency was supplied from that fresh cache in dependency order; Mathlib
and baseline project imports remained cached and read-only.

A separate forced **warm rebuild of all 296 current owned modules** also passed,
including all 285 port modules: 588.306 seconds wall clock, including resource-gate
wait, with zero cached-output skips. All 285 port outputs were present before the
sequence and every module was explicitly recompiled from the frozen current
source. `LEAN_NUM_THREADS=2` and one contribution compiler per sequence were used;
scoped commands passed through the four-slot resource gate. Baseline and pinned
Mathlib imports remained cached/read-only. Whole-closure aggregate CPU time and
peak memory were not separately measured; they are not inferred from the
single-proof measurement below.

A warm recompile of `ClosedProof.lean` exited successfully: 14.76 seconds wall
clock, including resource-gate/Lake overhead, with maximum resident size
6,968,708 KiB. Baseline and Mathlib dependencies were cached; this is not a
measurement of a complete clean Mathlib build.

## Verification attempt history

Intermediate proof-development compiler errors were not completion evidence.
In particular, dependent algebra/localization structures initially constructed
through unrelated local aliases failed raw kernel type checking; the final proof
instead declares them at the actual dependent valuation type. Subsequent kernel
compilation and the reported type/axiom checks passed on the bound sources.

An early frozen-headline command used bare `python`, which was unavailable.
A trailing cleanup command made that shell invocation return zero; it was **not**
a successful checker run. The actual rerun used
`python3 -B scripts/check_target.py`, executed the unchanged checker, and reported
a token-for-token frozen-target match. The initial failure and corrected pass
remain distinct evidence.

One incremental dependency invocation reached its 600-second bound with no
Lean diagnostic; that bound included resource-gate wait. No mathematical
impossibility or missing theorem was inferred. The same unchanged module later
compiled successfully. Incremental/retry outputs were not presented as a clean
cold-build timing; the separate 285-module fresh derived-cache sequence is the
cold evidence identified above.

A standalone fresh-cache helper check first could not find a cached baseline
module under the selected package root. Referencing the existing baseline
compiled objects in that derived cache fixed the layout; baseline sources and
outputs were not changed or rebuilt. All 10 then-current local helper/report
modules passed against the fresh port cache, in 49.93 seconds including gate
wait, and the full T18 type/standard-axiom report passed there too.

The first scoped raw-replay specification mistakenly used the module-name
prefix for declaration names and failed its pinned-type lookup. That failed
specification was preserved; declaration names and module names are distinct.
It is not a passed raw-audit result. The corrected specification uses the actual
`ZInQ.Contrib.FrobeniusDensity` declaration namespace and the copied frozen
reference proposition.

## Scoped raw kernel replay

The complete current 296-module contribution passed actual scoped raw replay,
not only elaboration or cached axiom summaries: 4,630 owned declarations,
4,639 raw serialized declaration occurrences, and 27 duplicate theorem bodies
checked separately. The verifier walks actual dependency bodies, including opaque
bodies, and found only `propext`, `Classical.choice`, and `Quot.sound`.
The runtime-skip list is empty; unsafe or partial owned declarations were rejected.
Both the local T18 proposition and the independently copied frozen reference
received `proved_exact_type` for `t18_holds`, with no extra universe, section,
explicit, implicit, or typeclass hypothesis.

The **unmodified original CI raw auditor** was also run independently with the
same corrected 296-module scope specification, against the fresh-cache owned
objects and cached pinned baseline. It passed 4,630 declarations, 4,639 raw
occurrences, 27 duplicate-body checks, both exact-type targets, only the standard
axioms, and an empty runtime-skip list. This invocation took 37.24 seconds wall
clock including the gate; its report SHA-256 is
`a5316819efae9bba27436db2a5db638987f5588a5e5b18295ac8d7a07f794c85`.
Its command was `lean --run scripts/audit_kernel.lean <scope-spec.json> <report.json>`
under the scoped pinned environment and resource gate. No root build or original
checker modification was used. The metadata-enhanced private invocation below is
additional evidence, not a substitute for this original CI replay.

The original `scripts/audit_kernel.lean` was not changed; its SHA-256 is
`673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc`.
A private generated verifier preserves its replay, raw-duplicate-body, exact-type,
and body-axiom logic, adds declaration-source reporting, and strictly rejects
runtime skips. Its SHA-256 is
`e5b182c212a90cef36009663e5d5f1c6e1290deacd9e28be8bd2a94a3d4922ef`.
The corrected scope specification SHA-256 is
`d4daee3ff71c6e2d4e17bc574d4d53dc557a12cfdd079de4f11135732d69aee7`;
the passing raw report SHA-256 is
`229e1ebf568decdb41afd21c07235209337ead56cd916fc531d567bb4514f30b`.
Raw replay took 40.25 seconds wall clock, including resource-gate overhead,
against the scoped fresh-cache objects and cached pinned dependencies.

The actual serialized declaration-source map has SHA-256
`29a157b175011f33519902e08da054bd5b20f1288c880b9a25d85453e7ac593b`.
Module paths are relocated, while upstream public declaration namespaces are
retained. The combined baseline/pinned-Mathlib environment and owned duplicate
copies passed the audit. Integration with other parallel ports must compare their
actual declaration-source manifests and deduplicate or remap any shared upstream
names; unseen parallel manifests are not asserted collision-free. None of this
is target registration or protected Astra/Protocol_D acceptance.

## Preliminary semantic review

A separate read-only reviewer reconstructed the source-to-consumer obligations
from the frozen statement and seven primary proof files before reading the
authored note. They found no substantive mathematical objection to the inspected
definitions, critical supplier interfaces, or assembly. The inspected twelve-file
packet (seven primary files, four critical port suppliers, and the existing C10
supplier) has manifest SHA-256
`e1c14a0cb2a526d2c6b657177b1d0da5fd822bc925d97a0b0551df3c218bb2e3`.
The algorithm is sorted repository-relative lines
`path SHA256(raw-file-bytes)\n`, hashed as UTF-8.

The reviewer specifically reconstructed the full local-fraction transport, same
prime and absolute automorphism, finite exact restriction, positive-density
finite exclusion, arithmetic exponent, and nonnormal-open-subgroup orientation.
They did not re-run compiler/axiom checks, inspect all 285 external modules, or
certify port-wide correspondence or inventory completeness. This is a
**preliminary semantic review**, not protected Astra or Protocol_D acceptance.

The reviewer also preserved a reporting discrepancy: an earlier version of this
note still described only local partial scope. That wording was stale relative
to the completed proof, not a mathematical gap. The current note now consistently
reports the closed theorem and standard-axiom evidence; the original review and
its limitation remain historical evidence. The reviewed proof/supplier sources
were not changed by that reporting correction.

## License, provenance, and review limits

The chosen Tau Ceti snapshot's complete root `LICENSE` has SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and specifies Apache-2.0. Its archive has no separate root `NOTICE` file.
A complete Apache-2.0 license copy is distributed in this repository at
[`ThirdParty/GreenTao/LICENSE`](../../ThirdParty/GreenTao/LICENSE), SHA-256
`c95bae1d1ce0235ecccd3560b772ec1efb97f348a79f0fbe0a634f0c2ccefe2c`.
Copied modules retain original copyright, author, and embedded attribution
notices, including references to earlier formalizations; each added port notice
identifies its exact source version and modifications. Original-project
licensing is not asserted to relicense those sources.

AI assistance contributed source research, port construction, and Lean proof
construction. Serving model identity is not asserted. Kernel/type/axiom checks
establish the stated formal proof relative to the named definitions and standard
trust base. They do **not** establish independent source-inventory completeness,
Astra eligibility, protocol acceptance, or acceptance of an assembled manuscript.
Eligible, non-author review and any registration/integration remain separate
maintainer work. This non-release helper contribution leaves the manuscript,
current acceptance records, release profile, TeX/PDF artifacts, and headline
premises untouched; record-release duties therefore do not apply here.

## Publication formatting addendum

The first parent publication preflight stopped at `git diff --cached --check`:
`Tau_Analysis_PSeries.lean` and
`Tau_NumberTheory_NumberField_Cyclotomic_IrreducibleOfUnramified.lean` each
retained one extra blank line at EOF from the port snapshot. That attempt did
**not** commit the candidate or start its full normal build/audit. The original
two files, original producer note, old source freeze and failed-gate evidence
are preserved as history; the failure is not counted as a successful audit.

Exactly one final LF was removed from each of those two files. The entire
preceding byte sequence, including every import, header, statement, proof and
namespace, is identical to its preserved producer source. All other 294 owned
Lean files retain their producer raw-byte hashes. This is an EOF-formatting
change, not a mathematical repair or a new source hypothesis.

The current 296-source sorted-path manifest, using the same serialization
specified above, is
`2ba3a24d9bb71c5ebabeba330ce290799d7a52c1cec60d187b3a90b27dd8611d`.
The two exact new source hashes are:

- `Tau_Analysis_PSeries.lean`:
  `4ff3d86f0ea9222961d836e8b72850e0cca10b88340765223d655001b5f4ade1`;
  preserved producer hash
  `24d338fb42b6fb1db08460de7654ab58f2c237658051cbc1bded86f74dff4add`.
- `Tau_NumberTheory_NumberField_Cyclotomic_IrreducibleOfUnramified.lean`:
  `82e666f0ad2fe1ee86f6763622e3fc9a618a0f5b78509d2ef5a47f0474fdcf85`;
  preserved producer hash
  `cbae98eadc19c7f760d821529ee5b17512ce84294a40fa24df4293afded64cd1`.

Both exact post-format sources were freshly compiled successfully into separate
owned scratch outputs with pinned `lake env lean -j2`, `LEAN_NUM_THREADS=2`, and
the unchanged resource gate. Their complete compile-log SHA-256 is
`c7c7b0062037a44990092718e9269b46cd5933df76fd7ec764863197b63a497c`.
This two-file check is not a fresh 296-module replay, a whole-project run,
Astra acceptance, or a new semantic review. The earlier producer cold/warm and
raw-replay reports remain bound to their original source snapshot. During this
addendum's preparation, a second publication preflight found one extra EOF LF
in the note itself; it was removed before commit. That second attempt likewise
did not start a full normal run, and its diagnostic is preserved separately.
Full normal validation and any review acknowledgment must be tied to the
post-format candidate's actual bytes; they are separate parent integration
steps.
