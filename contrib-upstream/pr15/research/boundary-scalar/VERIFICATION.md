# Verification of the boundary-scalar contribution

**Development profile: MET for the declared algebraic scope.** This report
combines fresh native Lean execution, exact finite controls, and separately
authored model mathematical review. Protected Linux comparison, export-kernel
replay and external checkers remain deferred to Open Math. The arithmetic
determinant-compatibility theorem remains OPEN.

## Scope, sources and provenance

The received 59,579-byte ZIP has SHA-256
`a90ece63029cdbca8bb7db1871cc5325a6cd19b505e6ed53810ab17fb2e62bae`.
CRC integrity, all 17 outer-manifest files and all nine inner review-manifest
files passed; all 19 members are accounted for. The archive and pasted review
are preserved in `inputs/`, with [provenance](PROVENANCE.json). The supplied
review is an adversarial rereview by an assistant involved in the original
candidate, not independent self-acceptance.

The supplied source commit is `40d01c53b3545a62949b14669c4906d3e978110e`;
the branch at intake was `083344e84a231d9127d57589ae5c0b355384579b`.
The reviewed six-lemma Lean/Python files match the current originals exactly.
The old 63-file packet manifest and all inherited accepted sources are intact.

The ordinary claim, assumptions and full construction are fixed in
[DERIVATION.md](DERIVATION.md) and [CONTRACT.md](CONTRACT.md). The fresh
[native result](evidence/native/RESULT.json) binds those files, all three Lean
sources, the checker, selected declarations, toolchain and dependency lock.
The current packet manifest binds the complete new source and evidence set.

The two new proof modules are
[BoundaryScalar.lean](../../lean/Research/BoundaryScalar.lean) and
[BoundaryCupAdapter.lean](../../lean/Research/BoundaryCupAdapter.lean).
The former has 24 proved declarations; the latter has two. The protected
challenge selects 13 principal matrix results, both adapter results and the
original six: **21 distinct declarations**. Supporting matrix lemmas are
compiled and used transitively; they are not additional independently selected
comparator targets. Counts measure inventory, not mathematical importance.

## Statement and proof crosswalk

All matrix names below have prefix `Research.BoundaryScalar`.

| Selected result(s) | Exact formal content and proof connection |
| --- | --- |
| `adjugate_singularNormal`, `adjugate_finiteNormal` | For an arbitrary finite index set, compute the full canonical adjugates as E_pp and −E_pq. The finite result assumes p≠q. The proof uses the concrete diagonal and swap matrices and adjugate multiplicativity. |
| `tensor_of_normal_form` | Given D B=T N and a proved canonical tensor identity, transport it to the full actual tensor with factor c det(B)/det(T). The sole divided target determinant is explicitly nonzero. The canonical identity is proved for the two normal forms, not assumed as a desired actual determinant equality. |
| `finite_tensor`, `singular_tensor` | Retain the actual cycle z=B e_p and actual closed row λ. Derive the row coordinates from λD=0 and compute every entry of zλ as a scalar times adj(D). The cross evaluation is an entry of λT. |
| `finite_cross_ne_zero`, `singular_cross_ne_zero` | Closedness, λ≠0 and det(T)≠0 force the respective actual cross evaluation to be nonzero. This protects the subsequent divisions. |
| `finite_coordinate_iff`, `singular_coordinate_iff` | With det(B)≠0 and λ≠0, any independently defined actual adjugate coordinate equals the computed expression, and conversely. This establishes uniqueness instead of merely naming the desired coordinate. |
| `boundary_scalar_formula` | Supply the two exact normal-form equations, actual cycles/closed nonzero rows, det(B_F)=η, det(B_S)=δη, and nonzero δ,η,det(T). The theorem proves both full tensor identities, nonzero q_F,q_S,u_F,u_S, and δu_F/u_S=−q_F/q_S. |
| `scalar_comparison`, `normalized_scalar_comparison` | Cancel the retained common source/target factors. Equal nonzero cross evaluations give comparison −1, with no individual coefficient-ring-unit hypothesis on that common evaluation. |
| `scalar_comparison_of_unit` | For an explicit ring homomorphism f:R→K and e:R×, the lower-level relation q_F=f(e)q_S gives comparison f(−e). This is an actual R-unit image, not a field-unit assertion. |
| `Research.BoundaryCupAdapter.cross_evaluations_eq` | Over a commutative ring and separate finite/singular modules, use J⁻¹ in the transported alternating pairing. The two stated boundary--cup identities with the same factor c imply equality of the actual cross evaluations. |
| `Research.BoundaryCupAdapter.cross_evaluations_with_factors` | Distinct c_F,c_S remain visible in the two evaluations; no equality or unit ratio is inferred for arbitrary distinct factors. |

The original six statements retain the crosswalk and exact sources in the
[original packet](../determinant-switch/VERIFICATION.md). Their proof bodies
were not changed by this extension.

The formal matrix inputs are normal-form equations and basis-determinant
relations. Constructing B_F,B_S,T from D₀,A_F,A_S,h_F,h_S,v,x is proved in
ordinary algebra in the derivation. The passage to H=L^n/im(D₀), determinant-line
interpretation and DVR valuation consequence are likewise ordinary algebra,
not new Lean constructions. The adapter assumes the actual adjunctions;
it does not establish their arithmetic occurrence or identify the manuscript's
functionals automatically. These are explicit scope boundaries.

## Execution and axioms

The [native command log](evidence/native/commands.json) records a fresh
output tree, three research-module compilations, the aggregate Solution, and
the explicit [type/axiom audit](evidence/native/axioms-and-statements.log).
All compiler invocations use `-Ddebug.skipKernelTC=false`; no previous project
artifact substitutes for these outputs. All nine dependency revisions match
the existing lock and their tracked sources are clean.

The observed toolchain is Lean 4.35.0 at
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
`arm64-apple-darwin24.6.0`, with the pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The official master cache was used
for the requested import closures; these are trusted published dependency
artifacts, not a fresh build of Mathlib.

Every selected matrix result uses exactly `propext`, `Quot.sound` and
`Classical.choice`. The original six and the two adapter results use exactly
`propext` and `Quot.sound`. No selected proof depends on `sorryAx`, a custom
axiom, native-evaluation assertion or kernel bypass. The solution source scan
also rejects explicit admissions and proof escapes. The quarantined inherited
main target remains separate and was not imported.

The supplied exact checker reproduces its frozen output in normal and optimized
Python: 300 cases in sizes 2–5, 152 matched-normalization cases, 129 unequal-scale
negative controls and 255 divisible-vector cases. The explicit primitive example
gives u_F=−1/2, u_S=1/4 and comparison 2. The old checker reproduces its 3,800
volume and 132 normalization controls, and its optimized execution is correctly
rejected. These are finite controls, not proofs of the general statement.
The native driver reruns the appropriate source guards and models; the intake
logs preserve the additional received-output and optimized-rejection checks.

## Exact statement comparison and packaging corrections

The final generated project builds the solution as its default and excludes
Challenge until explicitly requested. Its four solution roots register Solution
and the three Research modules. The separate challenge builds with exactly
21 intentional specification-hole warnings. Both are legacy-module sources;
Lake's module-system import guidance is recorded and is not a solution proof
admission.

Two fresh generations produced 17 byte-identical input files, with generated
manifest SHA-256
`fa7749aa918702ddb8f3694641839a1f751e2b377784c153e3332196076fc171`.
All dependency revisions are preserved; only the root lockfile package name
changes. Generated copies are not editable authorities. A local-only dependency
cache symlink was used for testing and is excluded from the generated inputs.

The [direct local probe](verification/compare_exports.lean) invokes pinned
`compareAt` and `checkAxioms` on separate exports. It enforces the exact
21-name inventory, compares all eight referenced project definitions with no
definition holes, and audits the solution's transitive axiom closure. The
[complete log](evidence/handoff/structure-and-axioms.log) and
[command/exit receipt](evidence/handoff/commands.json) show exit zero after
rejecting a missing main theorem, changed main statement, changed protected
normal form, and specification holes submitted as proofs. The
[handoff result](evidence/LOCAL_HANDOFF_CHECK.json) records artifact hashes and
scope. This is a local structural/axiom probe; it is not the protected Linux
comparator and performs no export-kernel replay.

Development history is retained in `evidence/history/`. An initial setup command
used the wrong working directory, and its subsequent pinned dependency
materialization was stopped with exit 130. A fresh project then exposed the
missing Research module registrations, which were repaired. Finally, a single
combined specification file changed an old `J v` coercion to a different
EquivLike instance after broader imports. The strict comparator rejected that
statement. Separate specification modules with each solution's exact import
context repair the mismatch; the complete final comparison passes. No old
proof was edited to make the specification pass, and failed attempts are not
reported as successful runs.

## Non-author review and assurance decision

The [initial mathematical review](evidence/math-review.md) independently
re-derives the general formula and primitive example. Its supplemental exact
checker uses a different determinant algorithm for 150 cases in sizes 2–6,
including GL₂(Z_(2)) determinants beyond ±1, nonunit η, fractional complements
and nonintegral L-valued functionals. The full proof, rather than those samples,
supports its mathematical decision.

The separately authored [final review](evidence/final-review.md) checks the
ordinary bridge, actual formal statements, coefficient-ring unit criterion,
typed adapter, final specifications and corrected comparison. Reports were
authored by the named model reviewer and copied unchanged. The formal core was
authored by `/root/boundary_scalar_lean`; the adapter, integration and execution
were by `/root`; review was by `/root/boundary_scalar_math_review`. Distinct
agent identities do not establish uncorrelated reasoning or human acceptance.

| Gate | Status | Exact coverage |
| --- | --- | --- |
| A01 Scope/snapshot | PASS | Received bytes, pinned source/branch, exact source/configuration hashes, dependencies and fresh artifacts recorded. |
| A02 Specification | PASS | Contract, derivation, typed assumptions and separate concrete challenge reviewed and hash-bound. |
| A03 Semantics | PASS | Elaborated statements, eight definitions and all 21 selected targets checked; the initial coercion mismatch was repaired and retested. |
| A04 Proof mapping | PASS | Canonical adjugates, tensor transport, closed-row reduction, uniqueness, comparison and adapter steps mapped above. |
| A05 Build/lint | PASS | Three fresh native module builds, aggregate Solution, source/axiom escape scan, focused exact models and repository guards. |
| A06 Axioms | PASS | All 21 selected transitive closures match the conventional allowlist, with actual per-target sets retained. |
| A07 Boundaries | PASS | Minimal dimension, characteristic two, nonzero denominators/rows, divisible vectors, fractional complements, common nonunit factors and primitive negative example. |
| A08 Native export replay | NOT_RUN | Native compilation is A05; no separate export-kernel replay claimed. |
| A09 Protected comparison | NOT_RUN | Exact frozen specifications and local direct probe pass; Linux protected execution is deferred. |
| A10 External checking | NOT_RUN | No paranoid or external checker run on the Mac. |
| A11 Clean release reproduction | NOT_RUN | Fresh local project outputs use pinned caches; no clean Linux release reproduction claimed. |
| A12 Non-author mathematics | PASS | Separate model source-level derivation and final review, with model-independence limits stated. |
| A13 Evidence/claims | PASS | Source, supplied evidence, observed execution, historical failures, formal scope and open arithmetic obligations remain distinguished. |

Development requirements A01–A07 and A13 are MET. Release/critical profiles
remain incomplete. A future Open Math paranoid run checks these exact formal
statements; it does not prove the actual Selmer construction or the arithmetic
boundary--cup normalization. No manuscript acceptance or restricted-converse
verification follows from this packet.
