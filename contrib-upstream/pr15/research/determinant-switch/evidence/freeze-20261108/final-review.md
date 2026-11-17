# Final bounded mathematical and challenge review

### 1) Verification target

**Decision: accepted within the stated abstract scope.** M1 and M2 from `math-review.md` are resolved. The unchanged six-lemma mathematical source, corrected contract, separately stated challenge, comparator configuration, handoff generator, and bounded local export-probe source have no remaining substantive finding from this review. This accepts their mathematical meaning and verification design; it does not assert that the deferred protected comparator, external kernels, or arithmetic integration have run.

| Identity | Reviewed value |
| --- | --- |
| Reviewer | Codex model reviewer, GPT-6 family; no more specific backend identifier exposed to this agent |
| Task | `/root/packet_math_review` |
| Role | Separately authored non-author review of the six-lemma source and handoff; no repository-source edits by this reviewer |
| Date | 2026-11-08, Europe/London |
| Checkout | `/Users/chey/Coding_Projects/diophantinezq/derivative-switch-review` |
| Branch/base commit | `codex/derivative-switch-boundary-v13`; `dbef6c581abd407e03f0729f6462dc86d2e5f4c2` |
| Dirty revision | Corrected contract and new verification files, bound individually below; the base commit alone does not identify them |
| Prior review | `math-review.md`, SHA-256 `2ef8fa012497e738a63115f849446373990007b6d2cb0ce040707244c81a97e1`, preserved unchanged |
| Pinned environment examined | Lean 4.35.0; exact installed source corresponding to the packet's declared commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; nine dependency pins in the existing lockfile |
| Review mode | Read-only source/evidence review, using development-profile terminology; selected semantic and design checks only |

The original non-author derivation, cofactor justification, exceptional-case analysis, and manuscript source lookup remain in the first report. This reviewer identified the two clarification requests and reviewed the author's edits. Both clarifications expose an existing source argument or intended lattice domain; this reviewer did not supply a new arithmetic proof route. Distinct agent identities do not establish uncorrelated reasoning, human review, or independence from shared model failure modes.

The repository's `AGENTS.md`, linked audit protocol, and research-review protocol were read in the initial review and remain governing instructions. The original six-lemma source is byte-identical to the source accepted in that review.

**Raw-byte SHA-256 bindings, relative to the checkout:**

| File | SHA-256 |
| --- | --- |
| `lean/Research/DerivativeSwitchBoundary.lean` | `63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea` |
| `research/determinant-switch/CONTRACT.md` | `01be1c4182cd5c7483ad2253b93b975ddced22396372e726aa808614d525516b` |
| `research/determinant-switch/README.md` | `779ebb536b4d16c35e70d7ae3ff4626a083dd8e6628f8f6aca9dc3e5ec9fff29` |
| `research/determinant-switch/VERIFICATION.md` | `d174466488af378f4d4ca35a852040c3768755f6ce5de9f12f35fb3e2c507970` |
| `research/determinant-switch/PR.md` | `b35d2b202d9c738748dfd6aca5498ea6fd32f13a9452cb8fd63791c0c35209bb` |
| `research/determinant-switch/verification/Challenge.lean` | `ae5cd67b93287c345a3b1a808eeeed9744667bb73eb10f068d8b056b20b497e8` |
| `research/determinant-switch/verification/comparator.json` | `c91df4fe3af892aa84e5beb124b6a07ad741eec20060508fc515f44dd19f970a` |
| `research/determinant-switch/verification/lakefile.toml` | `5ea438b8dbe8bffa2b289bb0b99f46e8fed55f3c19237cc94c59ede0afdd0c52` |
| `research/determinant-switch/verification/README.md` | `b58d2f7dc29650ce8aba1605cdd54f2b1a9b3f7901a21ab5b9f735885661a915` |
| `research/determinant-switch/verification/prepare.py` | `a813ad793c42d0cb44348cff090565942fb61aa5cfdc5e5c2f822b939da8a950` |
| `research/determinant-switch/verification/compare_exports.lean` | `4669da5900da840a77549ad341e766c110989fdf9e7abc511949ff6a1a700117` |
| `lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lean/lake-manifest.json` | `a770787f33b5824f61a0731d59e67fca3f44a531b21d1fc1a804064c6fb54e58` |

The new probe is a local review utility, not one of the seven copied source templates in `prepare.py`. It is not needed for the later standard `lake comparator` command. Acceptance of these exact files does not extend to later file edits, other final packet records not listed here, or arithmetic consumers. The three packet reader documents were inspected for material scope/status contradictions, not as an independent audit of every execution receipt they cite.

### 2) Independent re-derivation (outline)

**Resolution M1.** Corrected contract lines 50–60 now distinguish the boundary-kernel lines from generic `H¹` dimensions and state the needed strict-`H¹` vanishing. The cited V13 premise says the old `H¹(C_F)` is spanned by the old class `A`, whose localization `v` is nonzero. The triangle injects `H¹(C_str)` into `H¹(C_F)` with image the localization kernel. Localization on that one-dimensional old space is injective, so strict `H¹` vanishes. The two exact sequences then identify the old and new generic `H¹` spaces with the respective kernel lines. The exact-formal-coverage section repeats the extra premise. **M1 resolved on the bound contract.** This does not prove the arithmetic occurrence of its premise.

**Resolution M2.** Contract lines 72–78 now name free rank-two integral lattices `F_R,S_R`, their generic fibers, `v∈F_R`, and the integral isomorphism `J:F_R≃S_R`. The induced map on quotients is well-defined because `J(Rv)=R(Jv)`, and its inverse descends as well. Restriction gives an isomorphism of the finitely generated torsion submodules, so their Fitting ideals agree. The later coverage paragraph names the same lattice quotients. **M2 resolved on the bound contract.** No assertion about arbitrary non-finitely-generated generic-vector-space quotients is substituted for this one.

The final editorial pass also writes the integral triangle quotients as `F_R[-1]` and `S_R[-1]`, consistently with those lattice domains. This corrects notation at the integral comparison target without changing the reviewed ordinary argument or claiming to construct the arithmetic triangles. Its verification paragraph now identifies the separately authored model review while leaving human/arithmetic acceptance, Linux isolation and external checking unclaimed. This final contract revision was explicitly reread before its new hash was accepted.

**Challenge definitions.** Their meaning was checked independently against the stated ordinary algebra:

| Definition | Exact intended meaning | Finding |
| --- | --- | --- |
| `Research.DerivativeSwitch.AxesKernel` | For every `x∈F,y∈S`, the combined boundary is zero if and only if `x=a·v` and `y=b·Jv` for some scalars. Both directions, both coordinates, and independent scalars are present. | Concrete, correct, unchanged. It remains an assumed exact kernel description, including when `v=0`. |
| `Research.DerivativeSwitch.Volume.area` | The signed determinant of the two columns: `v₁w₂−v₂w₁`. | Concrete, correct, unchanged. |
| `Research.DerivativeSwitch.Volume.action` | Left multiplication by the matrix with rows `(a,b)` and `(c,d)`. | Concrete, correct, unchanged; its convention matches the determinant factor in the area theorem. |

**All six challenge signatures**, with prefix `Research.DerivativeSwitch`:

| Name | Independent meaning and disposition |
| --- | --- |
| `finite_kernel_line` | Over any declared field and modules, `AxesKernel` gives `dF(x)=0 ↔ x∈Kv`, for every `x`. All abstract maps and `J` are arguments. **Accepted.** |
| `singular_kernel_line` | Under the same hypotheses, `dS(y)=0 ↔ y∈K(Jv)`, for every `y`. **Accepted.** |
| `boundary_images_meet_zero` | Equality of one finite and one singular boundary forces both to be zero. It states image-intersection triviality elementwise. **Accepted.** |
| `no_identity_strict_square` | Given an explicit `x` outside the scalar line of `v`, the universal square equality `dF(x)=dS(Jx)` is impossible. The essential `hout` premise is retained. **Accepted.** |
| `Volume.area_action` | For every commutative ring, every four matrix entries, and every two coordinate pairs, transformed area equals `(ad−bc)` times original area. **Accepted.** |
| `Volume.area_neg_one` | Specialize to determinant `−1` and original area `1`; transformed area is `−1`. **Accepted.** |

The challenge retains the same implicit type variables, field/module structures, and separate commutative-ring context as the solution. It adds no characteristic-zero, dimension, or nonzero-vector assumption and makes no stronger conclusion. The source-level no-go and volume claims therefore have precisely the mathematical coverage accepted in the first report.

The six `sorry` theorem bodies are explicitly specification placeholders. They supply no accepted proof. The three definitions are complete terms, not placeholders. The solution imports the two Mathlib modules only and does not import `Challenge`. `Challenge` likewise imports only those Mathlib modules, with no import from the solution. The two modules have duplicate public declaration names intentionally and are used in separate environments, never imported together as a proof device.

### 3) Checks

**Source comparison observed by this reviewer.** A read-only Python extraction removed comments and normalized whitespace, then compared each of the six complete theorem signatures before its proof body and all three complete definitions. The extracted dictionaries matched. A separate check confirmed six distinct entries in `comparator.json`, exactly the six theorem names, an empty definition-replacement list, and exactly the three conventional permitted axioms. This was a static source check, not Lean elaboration or a protected comparator execution. The actual namespace and variable contexts were also inspected manually.

**Comparator semantics checked in the exact installed 4.35 source.** In `Lake/Check/Compare.lean`, `compareAt` first compares each selected declaration's kind and complete `ConstantVal`, including its type. It then traverses constants referenced by the type. Constants not in the theorem/definition replacement sets must have equal complete `ConstantInfo`; `runForUsedConsts` recursively traverses types and values. Therefore `definition_names: []` permits no replacement of `AxesKernel`, `area`, or `action`: all three are reached through the selected theorem types and their concrete values must agree. An empty list does not skip definition comparison. Theorem proof bodies may differ, as required for a challenge with placeholders.

`Lake/Check/Axioms.lean` separately requires the solution targets to be theorem declarations and traverses their types and proof dependencies, rejecting every axiom outside the fixed allowlist. `sorryAx` is absent from that allowlist. In `Lake/CLI/Check.lean`, the official comparison path includes the permitted axioms and the kernel primitive constants in its comparison, then invokes the axiom audit and native/selected kernel checks. This is the behavior the README describes, not a behavior inferred solely from its prose.

The exact pinned installed primary sources examined were under `/Users/chey/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/lake/`:

| Source | SHA-256 |
| --- | --- |
| `Lake/Check/Compare.lean` | `0281630a33b8f08a9f3f40f229cd843c02441a0cd4d8a6d8548dc2bb8ded4c68` |
| `Lake/Check/Axioms.lean` | `261fa54494a6a17c23b8588d788ab1080e5c39af2143948f8e140cfa295560d1` |
| `Lake/Check/Util.lean` | `f1e1b1ed49778fdad130a436340d55db72a5d6017cf5bc5d6a5dccdf7f55cb3d` |
| `Lake/CLI/Check.lean` | `55daf430e5adea38453b21798cbdf4cd099f66ec969494022a566a8ae098c00b` |

The corresponding upstream source locators are the pinned files under [Lean commit eb6cafb](https://github.com/leanprover/lean4/tree/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/lake/Lake). Local installed source was the primary evidence read; this reviewer did not browse mutable latest documentation.

**Lake target/isolation design.** The handoff defaults only to `BoundarySolution`, rooted at `Research.DerivativeSwitchBoundary`. The separate `Challenge` library is not a default target or an import dependency of the solution. `requiresModuleSystem=false` accommodates these existing legacy source modules. `debug.skipKernelTC=false` is explicit. The handoff retains the original Lean pin, Mathlib input revision and nine locked dependency revisions. Source/configuration isolation is a future execution condition, not something achieved by placing both source files in a directory. The README correctly requires externally preserved trusted hashes/configuration and read-only source during the future Linux run.

**Deterministic handoff source.** `prepare.py` uses an explicit seven-file copy map and preserves those source bytes. Its only semantic lockfile change is the root package name; it records the original lock hash and deterministic JSON serialization rule. It records source paths, input hashes and generator hash; emits no timestamps or output path into generated artifact contents; sorts manifest entries; creates only regular files; and refuses an existing output directory. The manifest excludes itself and its digest is printed for an external record. This is a sound deterministic-generation design. This reviewer did not execute generation or independently attest the integrator's byte-comparison run.

**Local export probe source.** `compare_exports.lean` calls the pinned `compareAt` on the configured targets plus legal axioms, with the exact pinned primitive list and no definition holes, followed by `checkAxioms` on the solution. It then tests four genuine rejection paths: a missing theorem, a changed theorem type, a changed protected area-definition value, and the challenge's `sorryAx` proofs presented to the solution axiom checker. The area modification adds an unused let to a closed term: it preserves mathematical meaning while changing the complete protected definition value, so its rejection tests the intended structural comparison. The four controls are not kernel rejection tests.

The probe trusts the externally frozen configuration; its internal check enforces count six and no definition holes, not exact name identity or uniqueness. The bound configuration reviewed above supplies those stronger properties. Its positive-status line is printed before negative controls, so completion requires final process exit zero and all four expected rejection messages. It makes no protected-execution or kernel-replay claim, and no such operation is present in its source.

**Supplied output inspected, not rerun.** The integrator's `export-structure-final.log` contains the positive structural/axiom line and all four rejection messages, specifically missing `finite_kernel_line`, changed theorem statement, changed `Volume.area`, and illegal `sorryAx`. `export-commands.json` records the six target names, primitives and legal axioms for both exports and exit zero for their exporter commands. This reviewer read those two records and hashed the exports but did not independently rerun the probe, parse the full exports, or inspect a separate final probe process-status receipt. The inspected log does not by itself prove kernel replay or sandboxing.

These observed artifact hashes are relative to `/Users/chey/Coding_Projects/diophantinezq/audit-output/2026-11-08-packet-freeze-review/`:

| Artifact | SHA-256 |
| --- | --- |
| `export-structure-final.log` | `1a1e703acd1bd6fca514e1f69c0eaab97b71b27a86499db99e2f256bcf112c51` |
| `export-commands.json` | `12e3c4d41c49528269067b076247991dbefc565446700a619d104203d408589c` |
| `solution.ndjson` | `b95f855582935940e4fd7672ee8727de62dd5a2927f5fdb66a9b1f6522e2f2cd` |
| `challenge.ndjson` | `5c3f44bfbdde6524d9993ec49b8e9838c907c1f86e3e312c7f459029b28d3a41` |

**Handoff claims.** The README correctly labels Open Math OS dispatch, Linux bubblewrap behavior, protected comparison, `--paranoid`, and external kernels as future work. The installed source confirms Linux/bubblewrap enforcement and the named additional checkers. The documented six-checker requirement applies to a future successful run; it is not current evidence. Setup/cache code execution, exact exit-code preservation, cache trust, temporary exports, and outstanding runtime/resource decisions are distinguished. No attempt was made to validate Open Math OS itself or run any of these commands.

The revised packet `README.md`, `VERIFICATION.md` and `PR.md` consistently distinguish the completed bounded model review and local structural/axiom probe from protected comparison, native export replay, external checking, human review, release assurance, and arithmetic tensor compatibility. `VERIFICATION.md` incorporates M1's strict-`H¹` condition and describes the probe's configuration and exit-status limits accurately. It also preserves the original ingestion evidence as historical rather than silently rebinding it. No material mathematical or scope contradiction was found in these reader-facing changes. Their positive execution claims remain supported by the integrator's separate receipts, which this report does not independently certify in full; final link/manifest assembly is likewise outside this bounded check.

### 4) Discrepancy report (if any)

- **M1: resolved.** Strict-`H¹` vanishing is now an explicit premise/derived source bridge for the dimension claim.
- **M2: resolved.** Integral free rank-two lattices and their finite torsion quotients are now explicit.
- **New substantive findings: none** in the exact reviewed files.
- **Limits retained:** native-build and reproducible-generation results belong to the integrator's separately recorded execution evidence. A direct structural/axiom probe is not the official protected comparator and is not kernel replay. The future challenge must remain protected from solution-side edits; hashes require an externally preserved trusted binding.

This round does not edit or replace the first report's findings. It appends their reviewed disposition on the new bytes. No change to the six proof bodies occurred, so the mathematical acceptance in the first report remains applicable to that exact source.

### 5) Certification result

**CERTIFIED within the abstract mathematical scope** of the six declarations, their concrete definitions, and the corrected contract bridges reviewed here. Repository review decision: **Accepted within stated scope** for these exact files and the stated handoff design. There is no remaining semantic blocker from this review to freezing this non-release packet.

For Lean proof-assurance reporting, this is a selected development-profile review contribution, not a complete execution report. Its standalone aggregate development-profile status is **INCOMPLETE** because this reviewer was not assigned to certify the final build/lint and execution receipts. The integrator may combine separately reviewed execution evidence only when it is bound to the same artifacts.

| Gate | Status in this review | Precise coverage |
| --- | --- | --- |
| A01 Scope/snapshot | PASS | Named source/configuration bytes, base commit, dirty inputs, toolchain and lock are identified above. |
| A02 Frozen specification | PASS | Corrected contract and concrete challenge reviewed and hash-bound. |
| A03 Semantic review | PASS | Six meanings and three definitions independently reviewed; prior solution elaborated statements remain applicable to unchanged source. Fresh challenge/kernel execution is not inferred from static comparison. |
| A04 Proof mapping | PASS | First report's independent derivations apply to the byte-identical solution. |
| A05 Build/lint | NOT_RUN | Not executed or fully audited by this reviewer in this round; integrator has separate run evidence. |
| A06 Transitive axiom audit | UNAVAILABLE | Audit implementation and supplied positive log inspected; final executable run binding/status not independently assessed here. This is a coverage limitation, not an adverse axiom finding. |
| A07 Boundaries | PASS | Zero vector, essential outside vector, characteristic two, zero ring, divisible vector, cofactor denominators, and strict torsion remain covered by the first report. |
| A08 Native replay | NOT_RUN | No replay by this reviewer; probe source performs none. |
| A09 Protected statement comparison | NOT_RUN | Trusted specification/configuration design reviewed; the supplied direct structural comparison is explicitly narrower. |
| A10 External checking | NOT_RUN | No external kernel or paranoid run. |
| A11 Clean reproduction | NOT_RUN | Generator design reviewed; no clean Linux or release replay by this reviewer. |
| A12 Non-author mathematical review | PASS | This separately authored source-level review and the preserved independent derivation, with the model-independence limitations stated above. |
| A13 Claim discipline | PASS | Source review, supplied output inspection, future design and unperformed execution are separated. |

No actual Selmer-complex construction, boundary–cup adjunction, normalized arithmetic tensor compatibility, height-one arithmetic coverage, restricted converse, manuscript acceptance, release, or human acceptance is certified. The precise arithmetic tensor comparison remains open. No push, remote job, Open Math OS dispatch, sandbox bypass, or `--paranoid` execution was performed by this reviewer.
