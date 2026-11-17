### 1) Verification target

**Accepted within the stated conditional algebraic scope. Development-profile evidence review: MET.** The final raw-frame construction, zero-aware coordinate uniqueness, coefficient-subring unit equivalence, same-row boundary-cup adapter and concrete 39-target specification pass this review. The arithmetic instantiation remains **OPEN**. Protected comparison, export-kernel replay, external kernels, Linux release reproduction and paranoid/cloud execution remain **NOT_RUN**.

Date: 2026-11-08. Reviewer: non-author Codex model agent
`/root/boundary_scalar_math_review` (GPT-6-family host identity; exact serving
model identifier unavailable). The initial report is preserved unchanged at
`math-review-initial.md`, SHA-256
`2d108cd56146be84f418ccac981ac91cca3124230620309327a1960396ba7c68`.
It contains the independent general cofactor derivation, source lookup,
meaningful boundary/necessity examples and the reproducible independent
32-case checker. This final report checks the later compiled bytes and
evidence; it does not rewrite the initial candidate's uncompiled status.

I did not author the new mathematics, proof repairs, driver or challenge.
The proof repairs were authored by `/root/scalar_frames_lean` and
`/root/scalar_units_lean`; `/root` integrated and executed the combined
checks. This is a distinct non-author model review of their work, with
shared-model/context correlation limits and no human acceptance. Reuse
of this same reviewer's earlier assessment of the unchanged 21-target
packet is a repeat/source-identity check, not another independent vote.

I used read-only source/Git inspection, SHA-256, exact Python and report
writing. I independently ran the finite tests recorded in the initial
report. The native compiler, axiom, build/export and direct-probe runs
were produced by the integrator; I inspected their actual sources,
commands, logs, type output and artifact bindings rather than rerunning
them. No reviewer Lean build, cloud/paranoid run, source edit, manifest
change, commit or push occurred. The math-verifier and Lean
proof-assurance skills are applied in **review existing evidence** mode,
using the predeclared **development** profile, not release or critical.

Repository: `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review`.
Intake/base commit: `bc2f21120c1b090a279c7b56675caa0e502584e1`.
The new sources were uncommitted additions during review; the hashes and
generated-input manifest below identify them independently of that commit.
All hashes are SHA-256 of raw bytes, without normalization.

| Final mathematical source | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitch/Coordinate.lean` | `229e66269880b9970b15ca36fab290d2572fdfac7396383d3327e652128ade90` |
| `lean/Research/DerivativeSwitch/CommonStrict.lean` | `c5770846489d7fdab0024d8f3c49e0a474eb0fa56dc428cc6a7034bc8e5605e4` |
| `lean/Research/DerivativeSwitch/UnitCriterion.lean` | `efd9f4404b9760f9d7ebc2cb0874f21f517ed3868e9e23f78fd0465a2c03e45a` |
| `lean/Research/DerivativeSwitch/BoundaryCup.lean` | `64750e7706f82cf0a47b76c80503bcab0577c2aa18f9703c09b4b8288be0df90` |
| `research/scalar-ratio/CONTRACT.md` | `7d7d69aa9fb2cae043ba29c93a0de5099ad552d387e1f53b09f9f58909cc4aca` |
| `research/scalar-ratio/DERIVATION.md` | `02fbb34ccd76ff3d3894b812416b722cf6f044322d16d35b4d0f11e39561e733` |
| `research/scalar-ratio/PLAN.md` | `fdfdcb6bac5480d41a68882ec4dc4bea7a967d16e992887ebe462264ce8b4de8` |

The received notes and original candidate hashes are bound in the initial
report. The unchanged old research sources, manuscript and exact owner
passages were compared there. No earlier verdict was used as a substitute
for the actual new inference. The current manuscript remains the same
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`
source; its arithmetic construction is not freshly accepted here.

### 2) Independent re-derivation (outline)

The independent derivation in the initial report remains valid for the
final statements, including zero rows. Briefly, for
`T=[D0,a,b]`, define `rhoF(y)=det[D0,a,y]` and
`rhoS(y)=det[D0,y,b]`. Closedness and invertibility of T give
`lambdaF=(qF/theta)rhoF`, `lambdaS=(qS/theta)rhoS`, even when a row
vanishes. A rank-one determinant-update calculation gives

```text
adj(DF)=-(1/eta) zF rhoF,
adj(DS)=(1/(delta eta)) zS rhoS,
uF=-eta qF/theta,        uS=delta eta qS/theta.
```

This is deliberately different from the implemented one-diagonal-normal-
form proof. The implemented construction agrees: actual cycle columns
give zero, strict columns give D0, complement columns give AFx/ASJx,
and the two target frames are `[D0,b,a]` and `[D0,a,b]`. Both
reduce to `diag(I,0,1)`, with target determinants `-theta` and `theta`.
Thus the finite minus sign comes from an actual column transposition.
The old coordinate transforms by `det(B)/det(T)`, in the correct direction.

The frames force nonzero adjugates independently of the rows. A nonzero
adjugate entry makes the scalar in the full tensor identity unique,
including when the tensor is zero. No division by a cross evaluation
is used for this conclusion.

Set `c=delta eta/theta!=0`. Then `delta uF=c(-qF)`, `uS=c qS`.
Multiplication by c and by the R-unit -1 preserves the same R-unit
witness. This gives the transported `UnitRelated` iff, including both
zero and exactly-one-zero cases. Removing delta needs its explicit
lift to the units of the specified subring R. The quotient formula
additionally requires qS nonzero; zero/zero is handled by the relation,
not treated as an arithmetic quotient.

The full cup identities on the stored rows and the explicit coordinate
involution give `qF=cF epsilon eta`, `qS=cS epsilon eta`. The minus
sign in the singular adjunction cancels alternation. This proves the
defect `-cF/cS` with the stated denominator guards, and the division-free
common-normalization identity without assuming the common factor is a
unit or nonzero. These computations do not construct the arithmetic
adjunctions or choose their normalization to get the desired result.

The initial report's independent finite control and guard counterexamples
are retained with executable source. They are supplementary error
detection; the universal derivation and exact formal statements support
the mathematical decision.

### 3) Checks

**Actual compiled definitions and repaired structure.** I inspected the
final source diffs, all new challenge signatures/definitions and the
native printed definitions, including their implicit parameters and
relevant explicit theorem-type portions. `CommonStrictData` is now a
type with exactly ten independent data fields:
`D0, AF, AS, hF, hS, v, x, J, lamF, lamS`, followed by six proof
fields: the two actual cycle equations, two actual row-closedness
equations, nonzero area and nonzero target determinant. Its only type
parameters/instances are K, I, Field K, Fintype I and DecidableEq I.
There is no stored coordinate formula, desired unit equality, qF=qS,
nonzero-row assumption or arithmetic normalization.

The native `HasCoordinate` is the complete matrix identity
`tensor z lam=u•adj(D)`, with tensor entries `z_i lam_j`. `Index I`
is literally `I⊕Fin 2`, and `Local K` is `Fin 2→K`. `frame` and
`target` retain their concrete block/column definitions. `matrixUnit`
constructs a field-matrix unit from an actual nonzero determinant; it
does not assert an integral-unit determinant. The native `UnitRelated`
existential ranges over the units of the actual subtype R, using
`R.subtype`, not units of K.

`BoundaryCupIdentity` has three fields only: J²=1, the universal finite
adjunction on `d.lamF,d.AS`, and the universal singular adjunction on
`d.lamS,d.AF` with the displayed minus. The pairing is the fixed area
form composed with the same coordinate-plane J. There is no arbitrary
application of a map F→S to an untyped S element: both local spaces here
are the explicit coordinate plane. This is the involutive matrix
specialization of the earlier abstract inverse-J adapter, whose broader
module/ring generality remains unchanged.

**The 18 new selected statements.** Prefixes below are
`Research.DerivativeSwitch.ScalarRatio`; all statements were compared
against their concrete specification and the ordinary argument.

| Declaration(s) | Semantic finding |
| --- | --- |
| `coordinate_of_frame` | Genuine invertible B,T and DB=TN transport a separately proved normal tensor coordinate by det(B)/det(T). No actual comparison conclusion is assumed. |
| `coordinate_of_closed_frame` | Actual closedness derives normal row support and the coefficient as an entry of lambda T. |
| `adjugate_ne_zero_of_frame`, `coordinate_unique` | Nonzero adjugate is established from the frame and used for uniqueness. There is no nonzero-tensor premise, so zero functionals are covered. |
| `raw_side_coordinate` | Constructs B,T from raw D0,A,h,v,x,y. The actual cycle equation derives DB=TN; no normal-form equation is a theorem input. |
| `common_strict_coordinate_formula` | From both raw cycles, both closed rows, area≠0 and the common target determinant≠0, derives both full coordinate witnesses, with the correct swap sign. |
| `CommonStrictData.coordinate_values` | Applies nonzero-adjugate uniqueness to coordinates supplied independently by their full cofactor witnesses. Includes zero rows. |
| `transported_ratio`, `CommonStrictData.actual_coordinate_ratio` | Exact ratio only with the explicit nonzero qS guard, plus nonzero delta/eta/theta supplied directly or by the data. |
| `transported_unit_criterion` | Unit-related transported coordinates iff unit-related actual cross evaluations, with nonzero common field scale and no q nonvanishing premise. |
| `integral_unit_criterion`, `CommonStrictData.actual_integral_unit_criterion` | Untransported iff additionally uses an actual R-unit determinant lift. It is a relation over R, not a vacuous field-unit assertion. |
| `boundary_cup_cross_evaluations` | Full same-row adjunctions and involution derive the two actual cross values with their separate cF,cS factors. |
| `normalization_defect` | The exact ratio is -cF/cS, requiring epsilon≠0 and cS≠0; eta≠0 is retained by the data. cF may vanish. |
| `common_normalization_adapter`, `det_neg_one_common_normalization` | A common factor gives delta uF=-uS without dividing by it; delta=-1 gives uF=uS in this orientation. Common zero is allowed. |
| `integral_boundary_cup_adapter` | Explicit R-unit normalizer ratio and determinant lift give UnitRelated(uF,uS), also for zero evaluations. |
| `valuation_equal_of_unitRelated` | Only an equality consequence for a multiplicative monoid-with-zero homomorphism trivial on R-unit images. It neither constructs an arithmetic valuation nor proves the full additive-DVR converse. |

Core matrices are field-valued; the data structure does not encode that
they arise from integral R-lattices. Actual R-integrality, coefficient
ring identification, retained determinant bases, strict cohomology and
the arithmetic functional construction remain application obligations.
The target determinant retains D0; no strict minor is removed as a unit
and no unchanged embedding of strict cohomology torsion is asserted.

**Boundaries and finite evidence.** The initial report checks minimal
size, nonprimitive classes, fractional complements, common nonunit
scales, characteristic two, both-zero and one-zero cases, complement
changes, and missing determinant-unit/nonzero-adjugate guard controls.
The nonzero local area still excludes v=0 and a generically acyclic
constituent. Its independently executed normal/optimized supplied suite
has identical output SHA-256
`e2d141099503d845ec240d1c85d7323a8d909c06b2a5540457acec92c48426e6`;
the reproduced independent small checker has 32 cases, 23 zero-evaluation
cases and 12 defined ratios. The supplied utility reuse is not counted
as independent implementation. No further repeated sample testing was
needed after the proofs and final statement comparison passed.

**Source-pinned native compilation and axiom evidence.** I read the
driver and command record and recomputed every native input and retained
`.olean` digest from `lean/.checks/scalar-ratio-verified-1/lib/`.
All match `RESULT.json`. The driver checks both previous 63/65-file
frozen manifests and their listed files, source/audit guards, exact
models, all nine locked dependency revisions and tracked source state;
it then compiles the seven solution modules and Solution into a fresh
output tree with `lean -j1 -Ddebug.skipKernelTC=false`. Its LEAN_PATH
starts with those fresh outputs, followed by pinned dependency caches.
All recorded commands exit zero. Cached dependencies are explicitly
trusted, not a fresh Mathlib build or a clean Linux reproduction.

Observed version: Lean 4.35.0, arm64-apple-darwin24.6.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; Lake
`5.0.0-src+eb6cafb`; Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The unchanged toolchain
file is `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`
and dependency lock is `a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58`.

The auditor prints 26 new named definitions/structures/accessors, obtains
all 39 actual declaration types through `getConstInfo`, and applies
`Lean.collectAxioms` transitively, rejecting every axiom outside the
predeclared conventional three. I checked the exact inventory and all
per-target sets. Seventeen new targets use exactly `propext`,
`Classical.choice`, `Quot.sound`; the new valuation consumer uses
`propext`, `Quot.sound`. The old thirteen matrix targets retain all
three, and the old six plus two abstract adapter targets retain the
latter two. No selected proof uses sorryAx or a custom/native-evaluation
axiom. The final log ends `AXIOM_AUDIT_PASS declarations=39`.

Coordinate emits three unused-DecidableEq section-variable warnings in
supporting lemmas; they do not alter the intended statements or admit
proofs. No linter was disabled. The other three new native compile logs
are empty. Local transparency elaboration settings remain, but the
proofs are compiled with kernel checking explicitly enabled and the
conventional axiom audit passes. No increased heartbeat setting remains.

| Native input/evidence inspected | SHA-256 |
| --- | --- |
| `research/scalar-ratio/verify.py` | `040370d1c94f70467facbc2288414b9c414e998eb3585b4a18893fdb814a3f4e` |
| `research/scalar-ratio/evidence/native/RESULT.json` | `7fee26cdfd15afaa9ab638367979481e16170503c838f7ac10666069fd575c58` |
| `research/scalar-ratio/evidence/native/commands.json` | `e35c661543780d87b2c4f1258969e133985463e5ab01392c68263360f3611887` |
| `research/scalar-ratio/evidence/native/Axioms.lean` | `96cd239fca9af1c82219f545d1dcc118ac050b07cafef798884503f1dac417e2` |
| `research/scalar-ratio/evidence/native/axioms-and-statements.log` | `23e8819553a10a28d9f926d3ce6e64dd5aec6ad639be50de14a9dc964742968f` |

The retained fresh artifact identities are:

| Artifact relative to the fresh `lib/` | SHA-256 |
| --- | --- |
| `Research/DerivativeSwitch/Coordinate.olean` | `acdcbdbf23e607fb051d3d1f09d85eb01e860c307c651fcef7948f9f331ac7b3` |
| `Research/DerivativeSwitch/CommonStrict.olean` | `0625a1ef4a17a5b73980e40f23bc1d699ff676790bcc4e20d1e414dedf84ccc6` |
| `Research/DerivativeSwitch/UnitCriterion.olean` | `c992a4b3ae6050cffced44c47e8e3db96faa2779225d87391bb160ac3acc9445` |
| `Research/DerivativeSwitch/BoundaryCup.olean` | `a9df08ffae16713d71f8c4036d1d72ee4d2e8fe91142ab95c7bc49ee8692ad43` |
| `Solution.olean` | `ddbde0ba2e8addfb10a272f4af15d01ff2065ac88ab0ff32432762de734be11b` |

The three old module artifact hashes also match their previous native
identities; they have not acquired mathematical coverage from merely
being imported into the larger Solution.

**Concrete challenge/configuration and local probe.** I read all four
new specification modules and the root aggregator. The prior three
specification modules were byte-compared with the old packet and are
identical. There are exactly 39 selected theorem proof holes: old 21
plus new 18. All coordinate/matrix/record/unit/cup definitions are
concrete; `definition_names=[]` permits no definition holes. Each
specification's import chain mirrors its source context through
specification imports, with no solution import. The final source and
specification meanings agree. The 39-name list is exact and distinct,
with the old 21 as an exact prefix and only the conventional three
permitted axioms.

The default generated library explicitly registers Solution and all
seven research module roots. Challenge is separate and non-default;
its seven submodules are under that root. The default solution build
and explicit Challenge build both pass. The Challenge log contains
exactly 39 expected `sorry` warnings; solution logs contain none. Legacy
Mathlib module-system import warnings and the three unused parameters
are recorded, not treated as admissions. The producer records the
absence of Challenge from the default build before explicitly building
it. Later Challenge artifacts therefore do not imply a default import.

The generator's explicit source/output list copies all authorities
byte-identically. Its sole lockfile transformation changes the root
package name, using declared UTF-8 JSON formatting. I checked both
generated directories `lean/.checks/scalar-ratio-handoff-1` and `-2`:
all 24 manifest-listed inputs and the manifest itself are byte-identical,
match their hashes, and match the current source map including the
generator. The 25-file generated manifest digest is
`117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`.
Inputs remain unchanged after builds/exports. Cache symlinks and build
artifacts are not generated input authorities.

| Reviewed verification source | SHA-256 |
| --- | --- |
| `research/scalar-ratio/verification/comparator.json` | `ae8b3b382cfc69d3aceb281c188548923855345a71f3775b813530ca059f00c8` |
| `research/scalar-ratio/verification/Challenge.lean` | `b7e458429c13a677784af6885d1d2c8aa5e09f6a633aa112aab090547d62c84f` |
| `research/scalar-ratio/verification/Challenge/Coordinate.lean` | `5d9345ec01b581faba690428fcfbc0d01196d61ba13d73e1ae6b9ae4e04bf1cc` |
| `research/scalar-ratio/verification/Challenge/CommonStrict.lean` | `50a3a1847f96d80bddacb6146696b07d6ca06f0b73c95f45793e3ca919313af5` |
| `research/scalar-ratio/verification/Challenge/UnitCriterion.lean` | `a2f864a2f353519d2c40739ed3c16f1a61498867817314df52a77215b2883b3b` |
| `research/scalar-ratio/verification/Challenge/BoundaryCup.lean` | `cc95c0bfa2a80fc2c967ed69b5fafb8c0defe7fc704bc2962b0d113afef8253b` |
| `research/scalar-ratio/verification/Challenge/Original.lean` | `ae5cd67b93287c345a3b1a808eeeed9744667bb73eb10f068d8b056b20b497e8` |
| `research/scalar-ratio/verification/Challenge/Matrix.lean` | `70141ae019654b59a07e1d34cead19aa5882f9a2f1b1097f021bb24653c12860` |
| `research/scalar-ratio/verification/Challenge/Cup.lean` | `657609e50b5b058f5e2435cced7f1efcadcd91aed076a7612742f409c12bf18e` |
| `research/scalar-ratio/verification/Solution.lean` | `7af2c393419c0d091defd9219f84d963bfc484b64633f8eee6e4f591554d671d` |
| `research/scalar-ratio/verification/lakefile.toml` | `9600bce268e5e5b0b9e0b3b255984b089b2006294c93e9264da2217ab86fead8` |
| `research/scalar-ratio/verification/prepare.py` | `c884b292701340b5a09d731f95ae714dad00726705955157f3931f9ec7eb2e4f` |
| `research/scalar-ratio/verification/compare_exports.lean` | `fd5c43364d6f209ce48d75eb5f3b8bf363bfd05a8549e21a54d5a39cdb02485d` |
| `research/scalar-ratio/verification/README.md` | `4db77bc8aad5d3bb68573ece21f43c15273e2cb5857e618b0c8a131bfeabf17c` |

The direct probe parses separately exported Challenge and Solution,
uses pinned `compareAt` and `checkAxioms`, requires the exact inventory
and no definition holes, then exercises six in-memory failure paths.
The command receipt records the exact `lake env lean -j1
-Ddebug.skipKernelTC=false --run` invocation, working directory,
export arguments and exit zero. The complete log shows actual rejection
of a missing old main theorem, changed theorem type, changed old normal
form, missing new raw common-strict theorem, changed protected
UnitRelated definition, and challenge `sorryAx` submitted as proof. It
then prints `STRUCTURE_AND_AXIOMS_PASS declarations=39 negative_controls=6;
no kernel replay or isolation`.

I inspected that code, receipt, positive/negative output, source map and
export identities. The result is producer-run evidence inspected by this
reviewer, not an independent execution. Both exports use lean4export
3.1.0/format 3.1.0 with the pinned Lean commit. Their hashes and sizes
match the actual local files. A structural match and these rejection
controls do not constitute kernel replay or protected Linux execution.

| Handoff evidence inspected | SHA-256 |
| --- | --- |
| `research/scalar-ratio/evidence/LOCAL_HANDOFF_CHECK.json` | `646753596be0a3501ccc12db523cfa2829d31a505dc991f94bc7d1b46389b734` |
| `research/scalar-ratio/evidence/handoff/commands.json` | `d8c4837f6dfea6c513a828f6df0389b43c27ae2d4716804141e393bff52a75a7` |
| `research/scalar-ratio/evidence/handoff/structure-and-axioms.log` | `891a06ac7b0c90a0fa1ef72e42f9b1198abec31b814397543db9b282c05ac51f` |
| `research/scalar-ratio/evidence/handoff/BUILD_RESULT.json` | `3f5feddc6516d117a66e5b725bcd27cbe96eb9d4e3374a73d818fc14e5c2cd1a` |
| `research/scalar-ratio/evidence/handoff/default-build.log` | `44c2a62cbb9e8ddce40b80c1d5c4d2aa80c26d8c8cb837ed5a3ea49e6b790024` |
| `research/scalar-ratio/evidence/handoff/challenge-build.log` | `8403f4f1de0a1fe6409c0b09105479c270b68659fa8114e487c1549666fa48a7` |
| `lean/.checks/scalar-ratio-exports-1/challenge.ndjson` | `56b951f679cc409dac4b751f0f5986811875f66168e2981afc99bdc5198babc0` |
| `lean/.checks/scalar-ratio-exports-1/solution.ndjson` | `760a03e8467c3d9ec81a562c6933807fe6127a7f2758844d63dc1d86dbf71247` |

**Scope/status documents.** I reread CONTRACT and DERIVATION and reviewed
PLAN, README, VERIFICATION, FINDINGS and PROVENANCE against the actual
source and execution coverage. No material overstatement was found.
They distinguish original uncompiled candidates, final repairs, ordinary
quotient/determinant/additive-DVR interpretation, native proof checking,
unprotected local matching, deferred cloud checks and OPEN arithmetic
application. Root wrapper/OPENMATH operations, final repository link and
manifest assembly, remote pushes and whole-publication maintenance are
the integrator's separate operational scope, not certified by this
mathematical review.

| Status/provenance file inspected | SHA-256 |
| --- | --- |
| `research/scalar-ratio/README.md` | `15d21ed9fd9f3a5c42fa802a71a427221da704fc22048b2b62d468e3ef54b302` |
| `research/scalar-ratio/VERIFICATION.md` | `0d4de50533ccb31c37ce5cc6f29e2cdebb656491b80ca1debe30fca0904c715b` |
| `research/scalar-ratio/FINDINGS.md` | `c19be41eddfdf4457c48481ee927e77c625024e9dcdac4eb59767d3696ee3e6f` |
| `research/scalar-ratio/PROVENANCE.json` | `d5e7e85cf4e9f6822991e0adddcdd37e12f6d9c36a08c52956ba849d58186aa1` |

**Development assurance gates.**

| Gate | Status | Evidence and limitation |
| --- | --- | --- |
| A01 Scope/snapshot | PASS | Exact source/configuration/manifest/lock and current native/export hashes checked; evolving initial snapshots preserved separately. |
| A02 Specification | PASS | Raw mathematical specification, repaired concrete records and 39-target challenge reviewed and bound. |
| A03 Semantics | PASS | Compiled core definitions/structures and relevant explicit types match source contracts; complete local structural matching covers the reviewed 39 signatures/referenced definitions. |
| A04 Proof mapping | PASS | Independent cofactor derivation and source-to-formal raw-frame, uniqueness, unit and cup crosswalk above. |
| A05 Build/lint | PASS | Exact seven-module native and generated default/Challenge evidence inspected, guards and tests passed; harmless warnings identified. No reviewer Lean rerun. |
| A06 Transitive axioms | PASS | Actual 39-target closure and 17+1 new split checked against conventional three, with no sorryAx. |
| A07 Boundaries | PASS | Initial independent/general and finite checks retain zero cases, actual rank guards, unit ring, fractional/divisible data, common nonunits and characteristic two. |
| A08 Export-kernel replay | NOT_RUN | Native compilation and structural parsing do not supply this separate operation. |
| A09 Protected comparison | NOT_RUN | Direct local matching passes; protected Linux comparator is unperformed. |
| A10 External kernels | NOT_RUN | No external/paranoid checker execution. |
| A11 Clean release reproduction | NOT_RUN | Fresh local outputs use trusted caches; no clean Linux release run. |
| A12 Non-author mathematics | PASS | This source-bound model re-derivation/final review, with stated independence/correlation limits and no human acceptance. |
| A13 Claim discipline | PASS | Initial failures/repairs, actual execution, formal/ordinary scope and remaining arithmetic/cloud obligations are distinguished. |

The required development gates A01–A07 and A13 are MET. No release or
critical profile is MET, and no optional checker result has been used to
hide an unresolved required mathematical finding.

### 4) Discrepancy report (if any)

**Initial E1 resolved for the final compiled bytes.** The original grouped
record-field syntax did not declare the intended independent inputs.
The final split fields match the supplied mathematical specification;
the actual native structure print and consumers confirm this. No desired
coordinate formula, unit comparison or extra normalization premise was
introduced. This resolution does not retrospectively make the original
uncompiled candidate a checked formal artifact.

I read the exact original-to-final diffs and both repair reports:
`evidence/history/frames/REPAIRS.md`, hash
`259d3f8007791cc1e2ba7b2538e6817f49f8201dd414a709d683e5a7d9a6ec8f`,
and `evidence/history/units/REPAIRS.md`, hash
`749ba9294809e58b1891edc6ce69e6afa87b52319ad03ac5abc6c07d07aeedad`.
The remaining changes are scalar/block simplification, explicit Fin 2
coercions, source-comment provenance and an accessor-named copy of the
existing eta≠0 fact. Native checking and type inspection confirm that
the intended premises/results were retained. Intermediate timeouts,
cache/prefix errors and failed proof elaboration remain historical;
they are not counted as successful runs or mathematical counterexamples.

No remaining mathematical discrepancy was found in the final conditional
theorem or its stated scope. The older primitive and new determinant-unit/
adjugate controls show why weaker inferences fail; they do not refute
the guarded theorem or establish/refute the arithmetic manuscript.

### 5) Certification result

**CERTIFIED under the explicit algebraic hypotheses, on the listed final
raw source and specification hashes:** raw common-strict frame construction
and cofactor formulas; coordinate uniqueness even for zero tensors;
guarded exact discrepancy; zero-aware coefficient-subring unit iff;
multiplicative-map consequence; and the same-row conditional cup
evaluation/normalization adapters. **Development-profile evidence review:
MET**, using the inspected producer-run native39 and local39/6-control
receipts, together with this non-author mathematical review.

The initial report remains immutable. This decision is not an acceptance
of future edited source/configuration/report bytes, a new independent
review of the old 21, or authority to claim the arithmetic realization.
The actual integral Selmer presentations and actual rows, boundary-cup
naturality/normalization, required localizations and retained limits,
derived determinant-functor bridge, manuscript incorporation, restricted
converse, human acceptance and publication/release acceptance remain
OPEN or outside this bounded contribution. Protected/Linux/paranoid,
external-kernel and export-replay work remains NOT_RUN.
