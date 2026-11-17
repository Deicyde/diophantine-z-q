# Scalar-ratio milestone verification

**Development profile: MET for the stated algebraic scope.** Four new Lean
modules compile; all 39 combined selected declarations pass the native type and
transitive axiom audit. A local structural comparison also passes. Protected
Linux comparison, export-kernel replay, external checkers and clean Linux release
reproduction remain **NOT_RUN**, assigned to Open Math. Actual arithmetic
boundary–cup compatibility remains **OPEN**.

## Sources and scope

The 40,542-byte received ZIP has SHA-256
`f68a88c8c69a7a971666d399f74427dea292ddbc1653c2d40debfda8f0a65e8b`.
CRC and all 20 manifest entries pass. The ZIP, pasted review and supplied notes
are preserved unchanged under `inputs/`; [provenance](PROVENANCE.json) records
the intake at bc2f211 and supplier baseline 40d01c5. The supplier explicitly
reported uncompiled candidates. That historical report is preserved rather
than relabeled as a successful run.

The [contract](CONTRACT.md), [ordinary derivation](DERIVATION.md) and
[predeclared plan](PLAN.md) fix the claim, assumptions and exclusions. The
[source-bound native receipt](evidence/native/RESULT.json) identifies final
source hashes, driver/configuration, toolchain/dependency lock, target axioms
and fresh artifact hashes. The new manifest binds this packet. The prior
63-file and 65-file freezes are checked unchanged, including their original
research sources. The three prior module artifacts also reproduce their
previous native hashes; the aggregate Solution changes to import four more
modules. No accepted manuscript or dependency pin was edited.

There are 18 new separately selected declarations, combined with the previous
21 in [comparator.json](verification/comparator.json). Other source lemmas are
compiled locally; only selected declarations and their dependencies are covered
by the later comparator export. Inventory counts are not a measure of proof
importance or arithmetic coverage.

## Formal statement and proof connection

All new names below have prefix `Research.DerivativeSwitch.ScalarRatio`.

| Selected declarations | Actual content and connection |
| --- | --- |
| `coordinate_of_frame` | For genuine invertible matrix frames and DB=TN, transport the full tensor identity with factor det(B)/det(T). The input normal coordinate is a cofactor identity, not the desired actual comparison. |
| `coordinate_of_closed_frame` | Closedness of the actual row forces its normal support onto the sole kernel coordinate. This derives the normal coefficient as literal evaluation on a target column. |
| `adjugate_ne_zero_of_frame`, `coordinate_unique` | Derive nonzero adjugate from the rank-one normal frame, then prove uniqueness by a nonzero adjugate entry. This works even when the actual row/tensor is zero. |
| `raw_side_coordinate` | Explicitly construct source/target frames from raw D0,A,h,v,x and derive DB=TN from the actual cycle. Derive the full cofactor coordinate from closedness, nonzero area and nonzero target determinant. |
| `common_strict_coordinate_formula` | Apply the raw construction to both sides, ordering target columns TF=[D0,b,a], TS=[D0,a,b]. The actual column swap gives det TF=−theta. Both use N=diag(I,0,1), deriving uF=−eta qF/theta and uS=delta eta qS/theta. |
| `CommonStrictData.coordinate_values` | The structure contains raw source data, actual cycles/closedness and two nonvanishing conditions. Coordinates supplied independently through HasCoordinate are uniquely the proved formulas. No formula or desired unit relation is stored as a premise. |
| `transported_ratio`, `CommonStrictData.actual_coordinate_ratio` | Under the explicit nonzero denominator guards, delta uF/uS=−qF/qS. The actual-data result uses independently specified coordinates, not assignments by the desired formula. |
| `transported_unit_criterion`, `integral_unit_criterion`, `CommonStrictData.actual_integral_unit_criterion` | A common nonzero field factor cancels from UnitRelated over the specified integral subring R, even when it is not an R-unit. Removing delta additionally uses its actual R-unit lift. Both iff directions include zero rows/evaluations. |
| `boundary_cup_cross_evaluations` | Full local adjunctions for all local vectors, involutive J and the same stored rows give qF=cF epsilon eta and qS=cS epsilon eta. Neither cross equality nor determinant preservation is an input. |
| `normalization_defect` | For nonzero epsilon and cS, the exact transported ratio is −cF/cS. These guards are retained in the compiled statement. |
| `common_normalization_adapter`, `det_neg_one_common_normalization` | A common normalizer gives delta uF=−uS without dividing by it, even when it is zero. For delta=−1 this gives uF=uS in the fixed cofactor orientation. |
| `integral_boundary_cup_adapter` | An actual R-unit ratio of normalizers, plus the R-unit lift of det J, gives UnitRelated(uF,uS). The normalizers need not individually be units or nonzero. |
| `valuation_equal_of_unitRelated` | A multiplicative map K→*₀G trivial on images of R-units maps unit-related scalars equally. It does not construct an arithmetic valuation or formalize the full additive-DVR converse. |

The raw theorem covers arbitrary finite I with index I ⊕ Fin 2, hence every
matrix size m+2 for m≥0. It is over any field, including characteristic two.
The explicit area≠0 excludes zero local classes. Target determinant≠0 retains
generic boundary independence. Neither determinant is assumed to be an
integral unit. Complement independence and the quotient interpretation are
ordinary derivations, with exact finite controls; no separate Lean quotient
or derived determinant-functor construction is claimed.

## Repairs, execution and axioms

Original candidate bytes and failing diagnostics remain recoverable. The
[frames repair record](evidence/history/frames/REPAIRS.md) and
[unit/adapter repair record](evidence/history/units/REPAIRS.md) describe exact
proof/API edits with patches. In particular, incoming grouped structure fields
did not declare the intended independent inputs under Lean's parser. Splitting
them supplies exactly the fields of the original mathematical specification;
no desired equality, normalization or new mathematical hypothesis was added.
Explicit Fin 2 matrix coercions remove inference timeouts. Scalar/block
simplification and an accessor-named copy of the existing eta≠0 fact complete
the proofs. No increased heartbeat limit remains. The scoped transparency
elaboration option is not a kernel bypass.

The [native command log](evidence/native/commands.json) records all seven
fresh solution-module compilations, aggregate Solution, source guards, models
and the [explicit type/definition and axiom audit](evidence/native/axioms-and-statements.log).
Every compiler invocation uses `-Ddebug.skipKernelTC=false`. Dependencies match
all nine original revisions and tracked source checks. Lean is 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, arm64-apple-darwin24.6.0;
Mathlib is `56a005855ea17e0b0958f73ec801ae140b0a1679`. The official master
cache supplies trusted pinned import closures, not a fresh Mathlib build.

Seventeen new selected results use exactly propext, Quot.sound and
Classical.choice; the valuation consumer uses propext and Quot.sound.
The prior thirteen selected matrix results use all three; the prior six and
two inverse-J adapter results use propext and Quot.sound. No selected proof uses
sorryAx, a custom axiom, a native-evaluation assertion or a kernel bypass.
The solution source escape scan also passes. Coordinate has three harmless
unused-DecidableEq parameter warnings, retained without disabling a linter;
the other three new modules compile warning-free. The inherited quarantined
main target is not imported.

The [finite results](evidence/finite/RESULT.json) reproduce the supplier's
normal/optimized outputs byte for byte: 180 new models in sizes 2–6, 720 full
basis adjunction checks, 540 unit comparisons at primes 2/3/5, 180 complement
changes, 121 common nonunit clearings, 90 zero-functional cases and 90 rejected
wrong-functional controls. The prior 300-case regression also passes. The
received output's NOT_RUN Lean field describes that finite program's scope;
the separate native receipt records the actual current formal run. Reused
matrix utilities do not constitute an independently implemented checker.

## Frozen cloud preparation and local comparison

Two fresh generations are byte-identical: **25 files**, with 24 manifest entries
and manifest SHA-256
`117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`.
The generated default builds seven solution modules and Solution; Challenge
is excluded until separately requested. Its separate build has exactly 39
intentional theorem-hole warnings. Seven specification modules preserve their
paired import contexts. The prior three are byte-identical to the old freeze;
the four new ones contain concrete definitions and the eighteen signatures,
with no solution imports or definition holes.

The [handoff receipt](evidence/LOCAL_HANDOFF_CHECK.json) and
[full commands](evidence/handoff/commands.json) bind generation, separate builds,
export hashes and the local probe. The [probe log](evidence/handoff/structure-and-axioms.log)
records exact statement/referenced-definition matching and transitive axiom
checking for all 39. It rejects missing old/new main theorems, a changed theorem
type, changed normal-form and integral-unit definitions, and challenge holes
submitted as proofs. Inputs remain unchanged after builds/exports. A local
cache symlink was used only for testing and is not a generated input.

This direct use of pinned compareAt/checkAxioms is **not** the protected Linux
comparator and performs no export-kernel replay. No external checker or paranoid
run occurred. Open Math must pull the repository, verify the frozen manifests,
run the protected cloud command and retain each checker's actual outcome.

## Review and assurance decision

The [initial model review](evidence/math-review-initial.md) deliberately
re-derives the algebra, records the changing candidate snapshots and supplies
an independently implemented 32-case exact 2×2 control, including zero cases and
necessity checks for the determinant-unit/nonzero-adjugate guards. It does not
approve the later compiled bytes. The separately authored
[final review](evidence/math-review-final.md) assesses the actual compiled
structures/types, final source repairs, concrete specifications and evidence.
The [findings ledger](FINDINGS.md) records dispositions and the scope of open
arithmetic obligations.

Proof repairs were authored by /root/scalar_frames_lean and
/root/scalar_units_lean; integration, driver and specification preparation by
/root. Review is by /root/boundary_scalar_math_review, which did not author
the new mathematics or repairs. This is model review, not human acceptance;
shared models/context can cause correlated errors. Prior review is reused
only with explicit unchanged-source/evidence checks, not counted as a new
independent review of the old 21.

| Gate | Status | Evidence and limit |
| --- | --- | --- |
| A01 Scope/snapshot | PASS | Archive, current source hashes, unchanged prior freezes, toolchain/locks and fresh artifacts. |
| A02 Frozen specification | PASS | Contract, derivation, concrete challenge and exact 39 target inventory. |
| A03 Semantics | PASS | Actual structures and explicit target types checked; full cofactor specification and actual integral-unit ring retained. |
| A04 Proof mapping | PASS | Crosswalk above; frames, adjugates, uniqueness, unit cancellation and same-row adapter. |
| A05 Build/lint | PASS | Seven fresh modules, aggregate Solution, source guards, exact controls and separate challenge build; harmless warnings identified. |
| A06 Axioms | PASS | Actual transitive sets for all 39; only the conventional permitted set. |
| A07 Boundaries | PASS | Zero rows, common nonunits, nonzero local class/target, minimal dimension, characteristic-independent proofs, complement changes and negative controls. |
| A08 Export-kernel replay | NOT_RUN | Native compilation is A05; no separate export replay claimed. |
| A09 Protected comparison | NOT_RUN | Local direct matching passes; protected Linux execution is deferred. |
| A10 External kernels | NOT_RUN | All paranoid/external outcomes await Open Math. |
| A11 Clean release reproduction | NOT_RUN | Local fresh outputs use trusted caches; no clean Linux release run claimed. |
| A12 Non-author mathematics | PASS | Separate source-bound model re-derivation/final review; limitations stated. |
| A13 Evidence/claims | PASS | Original bytes, repairs/failures, current evidence and open arithmetic/cloud work distinguished. |

Development requirements A01–A07 and A13 are MET. Release/critical assurance
remains incomplete. Even a successful paranoid run establishes these formal
statements under the stated trust base, not the arithmetic occurrence of their
hypotheses or the restricted converse. The actual integral Selmer presentation,
classes/functionals, boundary–cup naturality/normalization, required
localizations and retained limits remain uninstantiated here.
