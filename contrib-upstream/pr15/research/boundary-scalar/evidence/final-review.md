### 1) Verification target

**Decision: accepted within the explicit matrix and conditional-adapter scope. The split specification repairs the earlier elaboration mismatch; the current direct structural/axiom probe passes all 21 targets and four rejection controls. Development evidence has been inspected; protected, external and arithmetic acceptance are not claimed.**

Date: 2026-11-08. Reviewer: non-author Codex model agent
`/root/boundary_scalar_math_review` (GPT-6-family host identity; exact
serving-model string unavailable). This report extends, without editing,
the intake report `math-review.md`, raw SHA-256
`2cbfef8ba00ab0e34696f93d02a50130d9b10649a19b93a5598d25052262b3c0`.
That report contains the independent determinant-update derivation,
source/history search and excerpt bindings, nine arithmetic application
obligations, primitive counterexample, and exact-check replay. Its
arithmetic limitations remain in force.

I did not author the new Lean modules or derivation. I reviewed all their
definitions, theorem statements and proof bodies and compared their
interfaces with the already reviewed matrix construction. The typed
inverse-based adapter was proposed by the integrator, then checked by
this reviewer. This is a distinct model-agent review, not a human review,
blind review, or proof of epistemic independence; shared model families,
task context and source material can cause correlated errors.

I applied the math-verifier skill and the lean-proof-assurance skill.
The Lean assurance mode is **review existing evidence**, using the
**development** profile for this isolated non-release research addition.
No compilation, axiom command, replay, protected comparison, external
kernel, cloud dispatch or paranoid execution was performed by this
reviewer. Integrator-produced native execution receipts have now been
inspected and hash-matched to the exact sources; this is observation of
supplied artifacts, not a new execution by this reviewer.

Repository: `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review`.
Base commit: `083344e84a231d9127d57589ae5c0b355384579b`.
Branch: `codex/derivative-switch-boundary-v13`. The new sources/docs are
untracked additions during this review, so the base commit alone does
not identify them. All hashes below are SHA-256 of original raw bytes.

| Proposed file inspected | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitchBoundary.lean` (unchanged original) | `63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea` |
| `lean/Research/BoundaryScalar.lean` | `fd1ea9ca11a417072c7be08ef477901427c57a74962559d753d62db95883f3ef` |
| `lean/Research/BoundaryCupAdapter.lean` | `330699edaab6812ed68ed09a5fb682ad1d6b3af5a030a252691723066beffd7b` |
| `research/boundary-scalar/DERIVATION.md` | `1c16ce59014cc551c7b2537bd0d7be00f5343e80452464b6e1e7c2b3fd80b356` |
| `research/boundary-scalar/CONTRACT.md` | `74c0a7c963302202babb94ed1f5f8de9085216ac820521a57d8f04bf9215d360` |

The combined specification and local-tooling scope were subsequently read
in full. They select exactly 21 declarations: six existing declarations,
thirteen principal matrix declarations, and the two adapter declarations.
Both coordinate characterizations and both cross-evaluation nonvanishing
theorems are included. The remaining eleven matrix helper statements
are source-reviewed and freshly compiled; they are not separately
selected comparator targets. All eight referenced project definitions
are concrete, and `definition_names=[]` permits no definition holes.

| Reviewed verification input | SHA-256 |
| --- | --- |
| `research/boundary-scalar/verification/Challenge.lean` | `966d252297c89c83b28bcda1e21031da37ad54bd6a35712f68a680bcf281130f` |
| `research/boundary-scalar/verification/Challenge/Original.lean` | `ae5cd67b93287c345a3b1a808eeeed9744667bb73eb10f068d8b056b20b497e8` |
| `research/boundary-scalar/verification/Challenge/Matrix.lean` | `70141ae019654b59a07e1d34cead19aa5882f9a2f1b1097f021bb24653c12860` |
| `research/boundary-scalar/verification/Challenge/Cup.lean` | `657609e50b5b058f5e2435cced7f1efcadcd91aed076a7612742f409c12bf18e` |
| `research/boundary-scalar/verification/comparator.json` | `72047c185bbc3d5f9c5632244a014be7e9a9f35e1cc86d5cde0e0aab5411cec8` |
| `research/boundary-scalar/verification/lakefile.toml` | `abf16baba12326d8d4cfe4fcf4ba5d4cafa25c4d551df22938ce208264f93872` |
| `research/boundary-scalar/verification/Solution.lean` | `4dfa14193c0c7bd1a8500c17ecf144aaf25fc5c6a5a8ba19444a4aa6a72362eb` |
| `research/boundary-scalar/verification/prepare.py` | `bab372124454a4728227dc6630f5c0999afac6e44d104a5d0138e6910f360407` |
| `research/boundary-scalar/verification/README.md` | `33fa8d30b4ff305c185976ffa290e744230537bdc558d68f2cd77d068721e5cd` |
| `research/boundary-scalar/verification/compare_exports.lean` | `a4be6356a55e6bc4c6b4767b054816d42de97251f93c112a5d404c01d09fc7d2` |
| `research/boundary-scalar/verify.py` | `a472c291f61180992681ddfaa64f0485d54413165a26b97c3bb8f6dcab43c452` |

The final root `Challenge.lean` imports only three specification modules.
Each uses its paired solution module's exact import order and context.
Their 21 intentional theorem proof holes are specifications, excluded
from the default solution library. `Challenge/Original.lean` is
byte-identical to the old frozen six-declaration challenge. All eight
definitions remain concrete: `AxesKernel`, `Volume.area`, `Volume.action`,
`BoundaryScalar.axis`, `singularNormal`, `exchange`, `finiteNormal`, and
`BoundaryCupAdapter.transportedPairing`, in their displayed namespaces.
The new source signatures preserve the reviewed hypotheses and
conclusions, and the successful direct comparison checks their exact
elaborated forms. No solution module is imported into a specification
module.

`Solution.lean` imports only the three solution research modules. The
corrected Lake default is `BoundaryScalarSolution`, with four roots:
`Solution` and the three `Research` modules. `Challenge` is separate and
non-default; its specification submodules lie under its root and were
discovered by the observed build. `requiresModuleSystem=false` and
`debug.skipKernelTC=false` are explicit. This design and local build do
not establish protected runtime isolation.

Toolchain pin: `leanprover/lean4:v4.35.0`. The inspected lock file has
Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` and eight
other locked dependencies. Relevant metadata identities:

| File | SHA-256 |
| --- | --- |
| `lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lean/lakefile.toml` | `632fda3c75f7616378b9dadd0906d9518c7b4a1199c59d7b36369121acfb3b26` |
| `lean/lake-manifest.json` | `a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58` |
| `lean/SOURCE_MANIFEST.json` | `343d2eb94974a9c3defb58b8349f94378fb1984cb260b53162790426d8bbff96` |

No new acceptance of that frozen manifest's mathematical claims is given.
The new sources explicitly remain outside the accepted `ZInQ` snapshot.

### 2) Independent re-derivation (outline)

The intake report supplies a rank-one determinant-update proof independent
of the author's normal-form decomposition. Its formulas are

```text
uF = -eta qF/theta,
uS = delta eta qS/theta,
delta uF/uS = -qF/qS.
```

I separately checked how the integrator's concrete common-strict data
meet every hypothesis of the new formal main theorem:

1. For `m=n-2`, order coordinates as the strict source coordinates,
   then class index `p`, then complement index `q`.
2. Set `BF=[I_m,zF,(0,x)]`, `BS=[I_m,zS,(0,Jx)]`,
   `T=[D0,a,b]`. Their determinants are `eta`, `delta eta`, `theta`.
   The strict parts `hF,hS` change neither source determinant.
3. Actual cycle equations give `DF BF=[D0,0,a]`,
   `DS BS=[D0,0,b]`. The formal definitions give exactly those matrices
   as `T finiteNormal p q` and `T singularNormal p`.
4. Multiplication by `axis p` selects the actual cycles `zF,zS`.
   The actual closed rows satisfy the theorem's `lF vecMul DF=0`,
   `lS vecMul DS=0`; no canonical row is assumed as an input.
5. Column `q` of `T` is `b` and column `p` is `a`, so the formal lets
   `(lF vecMul T) q`, `(lS vecMul T) p` are precisely the ordinary
   opposite-boundary evaluations `qF,qS`.
6. Nonzero `eta`, `delta`, `theta` and actual nonzero rows are exactly
   the stated ordinary hypotheses. The main theorem derives the
   complete tensor identities and nonzero scalars, then the ratio.

This bridge is **ordinary algebra**, not a Lean construction of `BF`,
`BS`, `T`, complexes, quotients or determinant lines. Both modules and
the derivation/contract say so. The formal theorem is a general
normal-form presentation theorem whose hypotheses are met by the
reviewed concrete construction.

The final derivation explicitly realizes the adapter's common boundary
space as `H=L^n/im(D0)`, with `dF(f)=[AF f]`, `dS(s)=[AS s]`.
Each closed ambient row kills `im(D0)`, so it descends to a unique
functional on this quotient. The two opposite-boundary evaluations
then equal the matrix `qF,qS` exactly. This clarification is correct;
it remains an ordinary quotient construction rather than a new Lean
construction or an arithmetic realization.

For arbitrary finite index types, the canonical sign calculation does
not depend on an order or adjacency of `p,q`. Let `P=exchange p q` and
`S=singularNormal p`. Then `P^2=I`, `det P=-1` for `p!=q`,
`adj P=-P`, `adj S=e_p e_p^t`, and `finiteNormal=P S`. Hence

```text
adj(finiteNormal) = adj(S) adj(P) = -e_p e_q^t.
```

This independently confirms the finite `-qF` and singular `+qS`
canonical coefficients for the exact definitions, including nonadjacent
indices.

The typed adapter is also exact: inverse cancellation gives
`beta(v,Jx)=epsilon omega(v,x)` and
`beta(x,Jv)=epsilon omega(x,v)`. Alternation supplies
`omega(x,v)=-omega(v,x)`. The minus in the second adjunction therefore
makes both evaluations equal. With `cF,cS`, their respective factors
remain visible. No nonvanishing conclusion is inferred from
alternation, and no determinant equality is an adapter hypothesis.

### 3) Checks

**Source-to-formal crosswalk.** The following is source-level semantic
review, subsequently compared with the challenge signatures and relevant
explicit elaborated output from the exact native source artifacts.
All 24 theorem declarations in `BoundaryScalar.lean`, the two adapter
declarations, and their five new concrete definitions were read.

| Formal definition/declaration | Checked meaning and proof |
| --- | --- |
| `axis` | Exactly the coordinate vector `e_p`, via `Pi.single p 1`; no user-supplied abstract cycle axis. |
| `singularNormal` | Diagonal identity on every index except `p`, where the diagonal is zero. The final two-by-two block is `[[0,0],[0,1]]`. |
| `exchange`, `finiteNormal` | `exchange` is target row swap `p↔q`; its product with the singular normal form is identity on strict coordinates with block `[[0,1],[0,0]]`. Direction is correct. |
| `exchange_mul`, `exchange_self`, `vecMul_exchange`, `axis_exchange`, `det_exchange`, `adjugate_exchange` | Respectively row permutation, involutivity, row-coordinate permutation, `e_p P=e_q`, determinant minus one, and adjugate minus the exchange. All are correct with the exact stated domains. |
| `adjugate_singularNormal`, `adjugate_finiteNormal` | Full matrices `e_p e_p^t` and `-e_p e_q^t`, not selected cofactors alone. Correct in all finite sizes admitted by their statements. |
| `singular_closed_row`, `finite_closed_row` | Closed normal-form rows are supported only at `p` and `q`, respectively. The finite theorem retains `p!=q`; it does not assume the desired row formula. |
| `tensor_of_normal_form` | From `D B=T N`, `z=B z'`, `lambda T=lambda'`, and the canonical outer-product identity, derives `z lambda=(c det B/det T) adj D`. Only `det T!=0` is required; `B` may be singular here because no source inverse is taken. Its proof multiplies the adjugate identity on the correct sides and cancels right multiplication by `T`. |
| `finite_tensor`, `singular_tensor` | Derive canonical rows from the actual closedness hypothesis, then apply transport. Full outer-product conclusions have the correct signs and determinant direction. |
| `scalar_comparison` | Cancels nonzero `delta,eta,theta,qS`; no unnecessary `qF!=0` assumption or ring-unit claim. |
| `row_eq_zero_of_target`, `finite_cross_ne_zero`, `singular_cross_ne_zero` | Nonzero actual rows and invertible `T` imply the actual cross evaluations are nonzero. This is derived before divisions in the main theorem. |
| `basis_cycle_ne_zero`, `tensor_coordinate_unique` | A nonzero source determinant ensures `B e_p!=0`; a nonzero tensor makes its adjugate scalar unique. No existence conclusion is smuggled into uniqueness. |
| `finite_coordinate_iff`, `singular_coordinate_iff` | A separately defined tensor coordinate is characterized by the computed scalar. Both require nonzero source determinant and nonzero row to justify uniqueness. |
| `boundary_scalar_formula` | Given the two exact normal-form equations, actual basis cycles, closed nonzero rows, source determinant relations and nonzero volumes, concludes both full tensor identities, both nonzero cross evaluations, both nonzero coordinates, and `delta uF/uS=-qF/qS`. No ratio equality is an input. |
| `normalized_scalar_comparison` | A common nonzero cross evaluation gives exact comparison `-1`. It need not be a unit in an integral coefficient ring. |
| `scalar_comparison_of_unit` | Requires an actual `e:Rˣ`, a ring homomorphism `f:R→K`, and `qF=f(e)qS`, then identifies the comparison with `f(-e)`. It is an image-of-a-coefficient-ring-unit result, not merely `IsUnit` in a field. It is a sufficient implication; no formal DVR valuation equivalence or necessary-and-sufficient criterion is asserted by this declaration. |
| `transportedPairing` | Exactly `epsilon*omega f (J.symm s)` with `J:F≃S`; valid when finite and singular spaces differ. |
| `cross_evaluations_eq`, `cross_evaluations_with_factors` | Universal lower-level adjunction hypotheses imply equal evaluations or the two explicit factors. They assert neither their arithmetic occurrence nor their nonvanishing. |

**Implicit parameters and vacuity.** The scalar module assumes a field
`K`, arbitrary `Fintype ι`, and `DecidableEq ι`. It imposes no hidden
characteristic-zero or cardinality-two restriction. The main `p!=q`
forces at least two indices. The singular-only helpers validly include
the singleton case: the one-by-one zero matrix has adjugate one. The
closed-row and transport helpers validly permit zero rows or singular
`B` where no uniqueness/nonzero conclusion is claimed. The main theorem
requires nonzero `eta,delta` and the two source determinant equations,
so its actual source cycles are nonzero. The main normal-form equations
also imply cycle closedness by multiplication with `e_p`.

The adapter assumes an arbitrary commutative coefficient ring and
modules, not a field. Alternation implies skew symmetry without dividing
by two; the result remains valid in characteristic two and the zero
ring. It permits zero `c`, `epsilon`, or `omega`, correctly making only
an equality assertion. The docs explicitly require nonzero
`omega(v,x)` if using the pairing, rather than the independent matrix
argument, to deduce nonzero cross values.

**Integral-unit distinction.** For any unital ring map `f:R→K`, the
image of `e:Rˣ` is a nonzero field unit with the inverse `f(e^-1)`.
The formal corollary specifies that preimage in `Rˣ`; nonzero `qF/qS`
alone would not do so. For the intended DVR valuation statement, the
ordinary interpretation additionally supplies the actual embedding
`R→Frac(R)` and that `delta=det J` is an `R`-unit. The formal result
concerns `delta uF/uS`; without the latter premise it must not be
silently turned into an assertion about the valuation of `uF/uS`.
The inspected derivation retains that premise and leaves the valuation
statement outside the Lean formalization.

**Meaningful boundary checks.** The intake proof/checks cover `n=2`,
nonprimitive actual cycles, fractional complements, nonunit strict
factors, arbitrary integral-unit `delta`, and the primitive counterexample
`(-1/2,1/4,2)`. The arbitrary-index canonical derivation above covers
nonadjacent `p,q`; characteristic two collapses the sign consistently.
The new formal statements exclude zero denominators exactly where
needed. No additional repetitive finite testing was needed after
those checks and the source-level comparison passed.

**Proof-source inspection.** No `sorry`, `admit`, added `axiom`,
`unsafe`, `native_decide` or kernel-skipping option occurs in either new
Lean file. This static observation is distinct from the transitive
axiom audit inspected below.

**Inspected native evidence.** The producer's command record invokes
`lean -j1 -Ddebug.skipKernelTC=false -o <fresh output> <source>` for
all three research modules, then freshly compiles `Solution.lean` against
those outputs. Each compile command records exit zero and an empty
diagnostic log. The target artifacts and all twelve native input-hash
bindings were recomputed by this reviewer and match `RESULT.json`.
The version output identifies Lean 4.35.0, arm64-apple-darwin24.6.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Lake
`5.0.0-src+eb6cafb`. The producer checked all nine locked source
revisions and tracked dependency cleanliness. Cached dependency build
products are explicitly trusted; this is not a fresh Mathlib build.

The auditor imports the freshly built `Solution`, prints the eight
definitions, retrieves the exact 21 declaration types via
`getConstInfo`, and calls `Lean.collectAxioms` on each. Every unexpected
axiom throws an error. I checked the exact target inventory and all 21
axiom entries; the thirteen matrix targets use exactly `propext`,
`Classical.choice`, `Quot.sound`, while the old six and the two adapter
targets use exactly `propext`, `Quot.sound`. No `sorryAx` is admitted.
The log ends `AXIOM_AUDIT_PASS declarations=21`. The explicit
elaborated main theorem, coordinate-characterization, unit-corollary and
adapter portions retain the source's field/ring/module parameters,
finite index assumptions, actual rows, nonzero premises and conclusions;
no new semantic discrepancy was found. This is not an external kernel
or protected comparator result.

| Inspected producer artifact | SHA-256 |
| --- | --- |
| `lean/.checks/boundary-scalar-verified-final/RESULT.json` | `466e73c5cbec94d9151d2cd93127b839505d9fd685153ab1f4fa4d2f0724cb88` |
| `lean/.checks/boundary-scalar-verified-final/commands.json` | `859012aa7adee0685ced8a5c76d70fa77138974760005ba84bf3682a788fd130` |
| `lean/.checks/boundary-scalar-verified-final/Axioms.lean` | `5746201b6858391191ebe49ed49e33561d2db9eceb32fe4446db89265ac43c02` |
| `lean/.checks/boundary-scalar-verified-final/axioms-and-statements.log` | `0090695110695aea638af358bd4276990b9885523a499f186a80db287c6af7f3` |
| Fresh `lib/Research/DerivativeSwitchBoundary.olean` | `39e5ac5cab19dcdfa4a530342dab3725ffc9b90ed18536b10ee0a04900ad7a3e` |
| Fresh `lib/Research/BoundaryScalar.olean` | `e0b77134fd2fa2a1d8a530d898eca49a2f42dfcb7fc2947f87415ee5aef19ce3` |
| Fresh `lib/Research/BoundaryCupAdapter.olean` | `ba8147cf17bbcd508ba240ef4d3bc3314aecc0a001d77282698e67ad87a089e3` |
| Fresh `lib/Solution.olean` | `4d08db26dcff0129726c6fc8f133918bfbdf511c8841021c0d194f5140378566` |

**Generated-project identity.** I inspected
`lean/.checks/boundary-scalar-handoff-6` and `boundary-scalar-handoff-7`
without regenerating or building. All sixteen manifest-listed files plus
the manifest itself (seventeen inputs total) are byte-identical. Their
manifest digest is
`fa7749aa918702ddb8f3694641839a1f751e2b377784c153e3332196076fc171`.
Each manifest digest matches its file; every source path/hash in
`SOURCES.json` matches the current original source bytes, including the
generator's own hash. Copies are byte-identical, and the one declared
lock transformation changes only the root package name. This verifies
the explicit source/output list and repeatability of the supplied
generated inputs. Earlier 14-input manifests were intermediate and are
not the final specification binding. No fresh Mathlib build, Linux
isolation or undocumented cache provenance is inferred.

**Observed local build/export/probe receipts.** The producer's fresh
generated-project default `lake build` exits zero and records that no
`Challenge.olean` existed immediately afterward. The later explicit
`lake build Challenge` exits zero and reports exactly 21 expected
`sorry` warnings in the three specification modules. The final presence
of a challenge artifact after that separate build is expected; it does
not show that the default imported it. Both builds also have expected
legacy/module-system import warnings, with no incomplete proof warning
in a solution module. The original proof modules and their import
contexts remain unchanged.

Both selected exports use `lean4export` 3.1.0, export format 3.1.0, with
Lean commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Their command
record lists all 21 target declarations, the permitted axioms and the
standard pinned primitive inventory. The two export commands exit zero
and emit empty diagnostic logs. The direct probe parses those exports,
uses pinned `Lake.Check.Compare.compareAt` and `Lake.Check.Axioms.checkAxioms`,
requires the exact 21-name inventory and no definition holes, then
exercises four in-memory corruptions. Its log contains, in order:

```text
REJECTED missing theorem: Const not found in solution:
  'Research.BoundaryScalar.boundary_scalar_formula'
REJECTED changed theorem statement: Challenge and solution theorem statement do not match:
  'Research.BoundaryScalar.boundary_scalar_formula'
REJECTED changed protected definition: Const does not match between challenge and target
  'Research.BoundaryScalar.finiteNormal'
REJECTED challenge holes as solution proofs: Illegal axiom detected: 'sorryAx'
STRUCTURE_AND_AXIOMS_PASS declarations=21 negative_controls=4;
  no kernel replay or isolation
```

The final five-entry command receipt records the exact probe invocation,
working directory, stdout/stderr log and exit zero. I inspected its actual
source, arguments' source/manifest binding, complete positive/negative
log and current exports; I did not independently rerun it. The command is
`lake env lean -j1 -Ddebug.skipKernelTC=false --run` followed by the
absolute path of the reviewed `verification/compare_exports.lean`,
`comparator.json`, `../boundary-scalar-exports-6/challenge.ndjson`, and
`../boundary-scalar-exports-6/solution.ndjson`, with working directory
`lean/.checks/boundary-scalar-handoff-6`. The probe's
`IO.println` success marker is reached only after all comparison, axiom
and rejection checks succeed. This establishes the named direct
structural/axiom result, not the protected `lake comparator`, native
export replay or any external-kernel result.

| Local generated-project evidence | SHA-256 |
| --- | --- |
| `lean/.checks/boundary-scalar-default-build-6.log` | `037852a9d98b6869164b971d021b6f0185c65e160c318453dac4d0ba74da78f9` |
| `lean/.checks/boundary-scalar-exports-6/challenge-build.log` | `a8e0ef0888dac538a457098c4671a4de83c016712adb12331d997254fb353b35` |
| `lean/.checks/boundary-scalar-exports-6/commands.json` | `5161b15886257127f19bf31b3870a00905f25e896b8e1501d4ba00f5d7d35f48` |
| `lean/.checks/boundary-scalar-exports-6/solution.ndjson` | `4d5f9aefda69011b789d543abc0b834a205f6066767732599ba50f15d1f91dc9` |
| `lean/.checks/boundary-scalar-exports-6/challenge.ndjson` | `06d074281724b25a6fa78b857a11922756cda53bdd48c2431785f330c43e2fb8` |
| `lean/.checks/boundary-scalar-exports-6/structure-and-axioms.log` | `a59aae5c681fc214f06f8b4c74930ccac5f36459a23e2fa8d939c95a241672e9` |

Both `solution-export.log` and `challenge-export.log` are empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The final receipt is byte-identical to
`research/boundary-scalar/evidence/handoff/commands.json`. The supplied
native files copied into `research/boundary-scalar/evidence/native/`
also match the inspected native-output files byte for byte. The
source/export bindings, warning count, absence-after-default timing,
probe exit zero, history and unperformed higher-assurance checks were
reconciled with `research/boundary-scalar/evidence/LOCAL_HANDOFF_CHECK.json`,
SHA-256 `ff04dbefc97c5eaf211566c60e7302167634e8c4dca2006294734151f1183dd3`.

**Reader-facing scope/status review.** The new research README leads
with the exact ratio, routes to the derivation/contract/Lean sources,
and states the arithmetic normalization remains OPEN. `FINDINGS.md`
distinguishes the primitive weaker-inference counterexample, ordinary
construction, formal normal-form coverage, typed adapter, corrected
packaging/specification issues and arithmetic source application. The
provenance record identifies the supplied author's earlier involvement
and marks prior repository-status statements historical. No material
scope/status contradiction was found in these inspected texts. The
completed `VERIFICATION.md` was also read and reconciled with the actual
native/probe evidence, formal-to-ordinary boundary and this review's
producer-run-inspected role; its development-only claim and explicit
NOT_RUN/OPEN limits match this decision. This
does not independently certify every archive-ingestion assertion or
the later final assembly/link check; the final verification report and
wrapper/operations documents are assembled by the integrator outside
this mathematical review's authored scope.

| Reader-facing file inspected | SHA-256 |
| --- | --- |
| `research/boundary-scalar/README.md` | `a864768be46bba2cd8503cf4e3ee079338dd673eca03612fa74ec68c6c56157e` |
| `research/boundary-scalar/FINDINGS.md` | `72b6d3b88837a027541ef41afaf2669362c7c2d6696d05b0e6ac36abe93f9137` |
| `research/boundary-scalar/PROVENANCE.json` | `f798709f4adcebaf15966f8b1200593267dc737335b81ca80bd28bb22c4c268b` |
| `research/boundary-scalar/VERIFICATION.md` | `95a2ce3d5a5e73cebd205cd6af77e5546de7c140f7d00168c28794402b347b5f` |

**Development-profile gate assessment after native-evidence inspection.**

| Gate | Required? | Status | Evidence / limitation |
| --- | --- | --- | --- |
| A01 Scope and exact snapshot | Yes | PASS | Four proposed files, exact challenge/configuration, source/generation mapping and native input/artifact hashes above. |
| A02 Frozen specification | Yes | PASS | Supplied note, new derivation/contract, exact source definitions and statement crosswalk reviewed at listed hashes. |
| A03 Semantic review | Yes | PASS | Source mathematics, ordinary bridge, explicit native types and split specification reviewed; C1 resolved by exact import contexts and a successful 21-target structural comparison. |
| A04 Reviewable proof and mapping | Yes | PASS | Independent derivation and all formal proof steps mapped above. |
| A05 Build/lint | Yes | PASS | Exact source-bound native commands and empty compile diagnostics inspected; producer also ran frozen-source/audit guards and exact controls. No new execution by this reviewer. |
| A06 Transitive axioms | Yes | PASS | All 21 current-target entries and exact inventory checked; actual axiom sets are subsets of the declared conventional three. |
| A07 Boundary analysis | Yes | PASS | Explicit edge/vacuity analysis plus intake counterexample and exact checks. |
| A08 Native replay | No | NOT_RUN | No replay by this reviewer. |
| A09 Protected frozen comparison | No | NOT_RUN | Direct local structure/axiom comparison passes on the bound split specification, but protected comparator execution remains unperformed. The earlier local mismatch is preserved and resolved below. |
| A10 External checking | No | NOT_RUN | No alternative kernel or paranoid execution. |
| A11 Clean reproduction | No | NOT_RUN | No clean isolated reproduction by this reviewer. |
| A12 Independent mathematical review | No | PASS | This distinct non-author model derivation/review, with the correlation limits stated above. |
| A13 Claim discipline | Yes | PASS | Mathematics, source review, integrator-produced execution, unperformed higher-assurance checks and arithmetic OPEN status separated. |

Overall development assurance is **MET for this evidence-review scope**.
The earlier structural failure was retained, diagnosed and repaired,
then the exact split specification passed the complete direct probe.
All required development gates have inspected evidence. No new reviewer
execution, protected comparator, export replay, external checking,
clean Linux reproduction, arithmetic or release/critical acceptance is
inferred from that decision.

### 4) Discrepancy report (if any)

**Resolved finding C1 — single-file challenge elaboration mismatch.** The
direct probe failed with `Challenge and solution theorem statement do
not match: 'Research.DerivativeSwitch.singular_kernel_line'`. I inspected
the actual failure log, SHA-256
`a8b04e79e8cb967b5ea8462dad7d716717595bfa9aef096b4214f5b1250f3d10`.
The failed challenge export has digest
`38c671d5a65bb50b1d77c6ef9e8a18d663343c769e27fb6215797b1a26c5096a`;
the solution export has digest
`4d5f9aefda69011b789d543abc0b834a205f6066767732599ba50f15d1f91dc9`.
The failed single-file challenge source is the listed `28aafc40...`
version. A separate read-only comparison of exported type DAGs found
the first constant difference: the challenge elaborates the `J v`
coercion through `DFinsupp.instEquivLikeLinearEquiv`, while the solution
uses `LinearEquiv.instEquivLike`. Their application shapes consequently
differ as well. Additional imports before the copied original section
matter to the exact elaborated type. This is a specification-environment
mismatch, not a counterexample to the mathematical lemma. The final
separate specification modules use their paired sources' exact import
contexts. Their reviewed current exports pass the complete 21-target
comparison and four negative controls above. The original six-declaration
specification itself remains byte-identical. This resolves C1 for the
listed split-specification hashes, not for the rejected single-file
version. The rejected exports/log remain historical evidence rather
than being overwritten or promoted to a pass.

**Resolved finding C2 — package-root omission.** The first generated
Lake library had only `roots=["Solution"]` (configuration SHA-256
`aa807cceb5568978f7b0181ce3b9452ae19ad8b4f0deec5024f8abd3c64cccdc`)
and did not register the unrelated `Research` roots. The final
configuration explicitly lists `Solution` and the three research roots,
while `Challenge` and its submodules remain separate. The fresh default
and explicit Challenge builds passed. A separate initial invocation
also used the wrong working directory for cache-link setup and was
stopped with exit 130 while materializing pinned dependencies. Neither
unsuccessful attempt is counted as successful verification. These were
verification-packaging failures, not mathematical proof changes.

The preserved historical bindings were checked at
`research/boundary-scalar/evidence/history/`: the rejected single-file
challenge is `28aafc40b6798270fa95b0235f50560e37e862e0ea8905a853bfb1e57ffce025`,
its failure log is the C1 digest above, the coercion-instance diagnostic
patch is `0938dc93004f347b14a941c5f9a1f59ff3ffecdfaa8e923ab14882d501613818`,
the interrupted-build log is
`8f52338f44a40bdc9f58925ff6e31e6f3c09b5043531cb9620827ec73342acf3`,
and the unregistered-module log is
`f637956b75a5bc724255158e0114a06c5ee4e927e6f1a69caeeb0e113982e11f`.
The diagnostic agrees with the independently inspected export difference.

No mathematical discrepancy found in the exact proposed sources,
derivation or contract. The formal statements express the declared
normal-form consequence, with the common-strict construction accurately
kept in ordinary algebra. The adapter fixes the earlier abstract-plane
typing ambiguity by using `J.symm`, retains the crucial minus sign,
and does not overclaim pairing nonvanishing.

No change to the existing six-lemma source, manuscript, frozen accepted
snapshot, polynomial artifacts, old receipts, upstream application
contracts or release assets is needed for this isolated contribution.
This observation gives no acceptance to changes outside the listed
review scope. The arithmetic connecting maps, their normalizations,
their retained-ring coverage and their identity with the manuscript's
actual duality-defined functionals remain unresolved in this review;
the source/history limits are recorded in the untouched intake report.

### 5) Certification result

**Mathematical decision: CERTIFIED under its explicit
normal-form assumptions**, for the exact new Lean source hashes above,
the ordinary common-strict-to-normal-form bridge in the exact derivation,
and the typed conditional boundary-cup implication. This certifies
source-level mathematical fidelity; it does not itself claim observed
kernel checking.

**Development-profile evidence-review decision: MET** for the exact
listed proof sources, ordinary derivation/contract, eight concrete
definitions, split 21-target specification/configuration, generator,
native driver/probe and inspected artifacts. The current challenge is
accepted as a mathematical specification within this conditional scope.
The native/probe executions were produced by the integrator and inspected
by this reviewer. Protected execution remains unperformed. No future
edited bytes are accepted in advance.

Actual arithmetic realization, manuscript incorporation, the uniform
bound and height-one arguments, whole-proof acceptance, protected Open
Math execution, human acceptance and release acceptance remain OPEN or
unperformed within this review's scope.
