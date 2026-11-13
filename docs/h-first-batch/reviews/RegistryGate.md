# Independent first-batch registry and gate review

**Recommendation: proceed with a four-target statement/infrastructure registration proposal on the frozen main below, without changing the checker, existing pins, or five-premise headline. This is a preliminary non-designated-Astra engineering review, not protocol acceptance, a green full-kernel result, or a proof of the four targets.**

Reviewed main: `a5937595cde3e3db00975b81e5171cdef92c801a`, including auditor repair `97eb199f830d2078da885ee00298c1ef5fb52448`. Frozen PR41 source: `2757349fbd8ca613340b679bbd149f78c2baba6b`. Review date: November 13, 2026 UTC. The PR41 proposal's recorded base is the earlier PR36 head, not the current main; regenerate the first-batch proposal's base binding from current main, rather than copying its old manifest hash. The substantive review here concerns the registry/checker interface and the raw target bodies, not their fidelity to published primary theorems.

## 1. Exact recommended scope and manifest delta

Add only these four sources, with four entries appended to the existing `targets` array:

```json
[
  {
    "declaration": "ZInQ.Targets.H.T13",
    "provider": "ZInQ.Contrib.H.T13_holds",
    "source": "ZInQKernel/Targets/H/T13.lean"
  },
  {
    "declaration": "ZInQ.Targets.H.T17",
    "provider": "ZInQ.Contrib.H.T17_holds",
    "source": "ZInQKernel/Targets/H/T17.lean"
  },
  {
    "declaration": "ZInQ.Targets.H.T19",
    "provider": "ZInQ.Contrib.H.T19_holds",
    "source": "ZInQKernel/Targets/H/T19.lean"
  },
  {
    "declaration": "ZInQ.Targets.H.T21",
    "provider": "ZInQ.Contrib.H.T21_holds",
    "source": "ZInQKernel/Targets/H/T21.lean"
  }
]
```

The only production `files` additions are the four corresponding source paths, each mapped to the **lowercase 64-hex SHA-256 of the exact final file bytes**. Keep all 941 existing file pins and the five existing target entries byte-for-byte in value and order. Preserve `schema`, `baseline_commit = 9c7b60ef504a22a68137b46c86dd46efd54c6738`, `scope`, `headline`, and `exports`. Expected registry counts are **945 pinned files and 9 targets**. No new target provider is declared by a registration-only change.

`MINIMAL_MANIFEST_DELTA.json` supplies the additive proposal and exact three-field target shapes, with `acceptance: false` and `protocol_acceptance: false`. Its four `null` values explicitly mean **final source hashes unavailable because implementation belongs to the integrator**. That proposal is not a production contract and must not be passed to `validate()`. Do not substitute the original PR41 hashes after changing imports, scopes, comments, or other source bytes. The original hashes are retained separately in `SOURCE_HASHES.json` as source provenance, not recommended final pins.

The proposal's canonicalization is `first-h-batch-json/v1`: UTF-8, LF, recursively sorted object keys, two-space indentation, `ensure_ascii=False`, one terminal newline, array order preserved. The checker does **not** require that canonicalization; its identity is SHA-256 of raw serialized manifest bytes. Keep canonicalization metadata in the proposal/evidence, not as a new required production-checker field. When editing the existing production manifest, preserving unrelated formatting and existing array order minimizes the review delta.

### Import and definition closure

The PR41 bodies of T13, T17, and T19 use Mathlib objects directly, not an `HSyn` declaration. `open HSyn` and `open scoped ModularForm` are inherited environment setup, not mathematical inputs to those bodies. Replace their `Defs.HSyn` import with the narrow Mathlib modules needed to elaborate the unchanged bodies; retain `MatrixGroups` scope for T19's `GL` notation. Removing unused scope/open directives is an environment edit whose elaboration and body equivalence must be checked after extraction. Exact minimal module lists still require the integrator's compiler evidence; none was inferred or compiled here.

T21 already imports `ZInQKernel.HDecomp.Conductor.Breaks`, which is pinned at `7742365fd985fda83c733324394cb4a59db3f083e246dad63279924ce790306d` in current main. Its body, at PR41 lines 48–52, matches the baseline's `GlueConductor.SerreDifferentBound` at `Breaks.lean` lines 350–354. Preserve the existing `T21_iff_baseline` check and the import if needed. This reuses the existing object layer; it does not require changing or repinning `Breaks.lean`.

Do **not** bring the other 30 targets, the 34-import umbrella, or the three `Defs` modules into this batch. Registering only four entries while tracking the rest of PR41's new non-Contrib Lean files still fails by design. An umbrella is unnecessary: the checker discovers every tracked project module and `check_kernel.py` explicitly builds them, even without a root import. A four-import umbrella would also need its own fifth new file pin and infrastructure review; it is not part of the minimal delta.

No manuscript or new-record promotion is proposed. Release-manuscript/PDF duties are outside this registration-only change, subject to the eligible reviewer confirming that scope. Existing conditional mathematics and manuscript artifacts must remain unaffected.

## 2. What the unchanged current checker allows

References: `scripts/check_kernel_contract.py` lines 62–108 and 111–129.

- `validate()` permits new baseline sources when tracked, ordinary/non-symlinked, present in `files`, and hash-matching. It does not require resetting `baseline_commit`. The current main validates read-only with 941 pins and five targets.
- Every tracked protected non-Contrib Lean source must be pinned, even if not imported by a root. Frozen PR41 fails with `Unregistered baseline source` as expected; its draft audit does not satisfy registration.
- A target's `source` must name a pin; target declarations must be unique and nonempty as a list; provider names must be unique. Missing, untracked, symlinked, malformed, and changed file pins are rejected. The bypass-option denylist applies even in comments.
- `classify()` compares actual committed base/head changes against `KERNEL_CONTRACT.json` and the **trusted base's** file pins. Self-consistent changes remain `statement_or_infrastructure_review`, with `acceptance: false`. Registration necessarily changes the manifest and takes that route.
- Once registration is independently accepted into a trusted base, adding only `ZInQKernel/Contrib/H/<ID>.lean` is eligible for `proof_only_astra_review`. The existing manifest already reserves the provider. Subsequent proof PRs require no shared-manifest edit, no target edit, no root edit, and **no manifest sharding**. Helper proofs may also remain in Contrib. Separate helper files outside Contrib would require registration/review.
- The classifier is a routing predicate, not an approval and not validation of a dirty worktree: it uses committed `base` versus `HEAD`. Freeze/commit the integrator's exact candidate through their authorized workflow before asking for acceptance; do not mistake an uncommitted edit's classification for the final PR route.

`baseline_commit` is metadata in this validator, not an authenticated anchor it resolves. The trusted `--base-ref` supplied by the protected reviewer is the actual classification anchor. Preserve the metadata value, but do not claim it alone secures the baseline.

### Full closed-provider contract

References: `scripts/audit_kernel.lean` lines 39–50 and 150–164.

Each target must be a universe-parameter-free declaration whose type is exactly `Prop` (`sort 0`). A missing provider is legitimately **open**, not a failure and not a proof. If the reserved provider exists, it must be project-owned, have a theorem body or safe/non-partial definition body, have no universe parameters, and its **full elaborated type** must be kernel-definitionally equal to the closed target constant. New explicit, implicit, instance, or section arguments do not close the target. Quantified assumptions already inside the registered proposition remain part of that proposition and are not prohibited extra provider binders.

The checker does not enforce provider spelling or its source-module path as a separate hardcoded rule; the prescribed names are frozen registry conventions. The auditor enforces project ownership, not specifically Contrib ownership. The trusted routing rule and review must ensure a proof-only PR stays in Contrib. A missing target, forbidden axiom anywhere in the owned declaration closure, `sorryAx`, or wrong provider type fails the auditor. Runtime unsafe/partial declarations are separately reported, not certified executable code and not recognized providers.

## 3. Repair 97eb199 and remaining trust gaps

### What the repair actually improves

The current auditor reads raw `moduleData.constants` rather than selecting each body through `env.find?`. It checks the serialized name table, retains every raw project declaration occurrence, permits only matching theorem signatures for duplicate names, and adds dependency roots from every raw body. It rejects custom project axioms directly, checks external-base module leakage, replays project declarations, and kernel-checks every duplicate raw theorem body under a fresh name. A good imported copy therefore cannot simply hide a bad project duplicate body or its direct forbidden-axiom dependencies.

The current integration-test source covers project duplicates in both import orders, external duplicates, forbidden-axiom masking, actual project-module leakage, and a deliberately invalid duplicate proof term. **These Lean tests were read, not executed in this review.** Earlier repair records give scoped static judgments and retain runtime obligations; they are not reused here as final-source build evidence or automatic acceptance of the new targets.

### G1 — Source/artifact binding remains a trust assumption

**Material qualification for any claim of a hostile-artifact-secure proof gate; not a mathematical counterexample to ordinary compilation.** The manifest pins source bytes. The auditor checks declarations supplied by serialized artifacts against the reconstructed environment. `check_kernel.py` annotates its output with head/manifest identities and calls source/dependency checks before and after the build/audit, but does not independently prove that serialized definitions are the compilation of those exact source bytes.

A different, internally well-typed serialized target definition could in principle have the same name but a different body, with a provider proving that substituted proposition. Kernel replay establishes correctness relative to the loaded/replayed definitions, not equality to the textual source definition. A clean trusted source-to-artifact build and trusted dependencies are the conventional basis for the stronger correspondence. Repair 97eb199 handles duplicate bodies; it is not an artifact authentication mechanism.

The Python control `test_generated_artifact_change_not_in_contract_fingerprint` establishes only that an untracked mock artifact does not affect `validate()`'s result. It is **not** a forged-olean demonstration and does not establish a bypass of the complete build/auditor. No serialized Lean forgery was constructed or tested. Do not claim a fully secure proof gate, sandbox, or source-authenticity proof from the audit's success.

### G2 — Contrib body changes are absent from the source-stability fingerprint

**Concrete current implementation limitation.** `validate()` returns the manifest digest, pinned-file count, discovered module/path map, target entries, headline, and exports. Unpinned Contrib bodies are not hashed into that result. A tracked Contrib file can change contents without changing the return value, provided it remains allowed by the textual denylist. Consequently the equality checks in `check_kernel.py` lines 85 and 95 do not detect every Contrib content change during compilation/audit.

The controlled Python test changes the same tracked Contrib path between validations and confirms exact return-value equality while its source digest changes. This does not supply a successful adversarial Lean run; it identifies the fingerprint gap exactly. Stable, isolated source snapshots and independent exact-revision review remain necessary. If stronger source-mutation/authenticity claims are desired, separately review a complete tracked-source fingerprint and a trusted source/artifact binding policy rather than silently expanding this registration batch.

### G3 — Registry metadata is not a declaration-to-source receipt

`validate()` accepts a target entry whose source is an unrelated pinned file and does not check whether that file declares the named proposition. The auditor checks target existence/type in the verified environment but does not verify that the declaration originated in the manifest's named source module. Python controls confirm this boundary. Likewise Python validation alone accepts a nonexistent target name; the Lean auditor is the later check that rejects it. These facts do not make the proposed correct mapping invalid; they mean exact source ownership/mapping must be reviewed rather than advertised as independently authenticated by the `source` field.

All three qualifications concern this repository's checker/trust model, not mathematical truth, independence of reasoning, or the serving identity of this review. They do not prevent an honestly scoped registration proposal under the conventional trusted-build/reviewer assumptions, but they prevent calling this report a complete hostile-artifact security acceptance.

## 4. Green versus registration versus acceptance

For the integrator's **final implemented tree**, checker/build green requires:

1. Track precisely the four new statement files and final hash pins; preserve the existing baseline/contract fields and all existing pins. Ensure no unregistered PR41 files or unintended baseline edits are tracked.
2. Verify extraction keeps the actual statement bodies and resolves the same objects/notations under the replacement imports. T21's baseline equivalence must still elaborate. Record final source hashes, exact compiler/dependency versions, and final revision.
3. Run the normal contract tests and validator, including trusted-base classification. Registration must report `statement_or_infrastructure_review`, never proof-only or approval. The 29 Python tests here are not a substitute for normal Git-integration execution on the final candidate.
4. Run `scripts/test_kernel_audit.py` and the required **complete** `scripts/check_kernel.py` path under the pinned Lean 4.35.0/dependencies: build both roots and every tracked module, frozen-target identity check, dependency/source checks, full project replay, axiom audit, exact headline, exports, and all nine target statuses. `--skip-build`, a narrow four-file compile, and PR41's customized draft audit are not equivalent to required CI.
5. Registration-only output should show the four new providers `open`; it may still be green. A subsequent proof-only candidate may show `proved_exact_type` only after the full provider/replay checks. No leaf proof automatically removes `SixContactMin` or any of the other four premises from the headline; a separately checked discharge/assembly theorem is needed.

For **public acceptance**, the registration PR must explicitly request statement/infrastructure review of the exact four statements, imports/definition closure, pins, and qualifications. An eligible non-author designated-Astra reviewer must independently assess the applicable Protocol_D scope and objections, and the protected controller must issue its exact-revision acceptance. This report supplies neither that eligibility nor that check. Existing contributor-written approvals, CI green, historical component judgments, and the PR41 proposal cannot replace it. Live controller/ruleset enforcement was not audited here; policy/code requirements must not be represented as a live controller readback.

Suggested registration scope sentence:

> This change registers only T13, T17, T19, and T21 as four closed-Prop statement targets with reserved, undeclared providers. It adds four source pins while retaining all 941 existing pins, the five original targets, baseline_commit, headline and exports. It requests independent statement/infrastructure review; it is not a proof, protocol acceptance, assembled-proof acceptance, or a manuscript/record release. The other PR41 targets remain outside this batch.

## 5. Reproduction, controls, and limitations

**29 isolated Python tests passed:** seven exact upstream contract-test cases and 22 added first-batch/boundary cases. The original checker and test sources were loaded from immutable current-main Git blobs, not rewritten. Fixture Git history was emulated in memory to honor the no-commit/no-shared-repository-mutation restriction. Thus these are tests of the actual checker logic with modeled Git outputs, **not** a fresh real-Git integration run. All fixture files, logs, and proposal/report outputs stay in the new review directory; bytecode is disabled, temporary directories are redirected there, and a Python audit hook rejects out-of-directory file mutations and Lean/Lake/Git-mutating subprocesses. Two additional isolation probes confirmed that a forbidden write is rejected before mutation and a synthetic Lean subprocess audit event is rejected without spawning a process.

Controls cover four-target registration, unrelated unregistered targets, later one/two-provider Contrib-only routing without manifest edits, incidental manifest edits, self-consistent statement changes, changed body hashes, target/provider duplication, missing pins, untracked pins, unsafe paths, malformed digests, symlinked pins, non-Lean Contrib files, new workflows, bypass tokens even in comments, and the three deliberate metadata/fingerprint limitations above. Every expected rejection or expected boundary behavior passed. Ordinary full-provider negative tests are present in the pinned Lean test source but were not run here.

Actual read-only source validation: current main is `valid_candidate_contract`, `acceptance: false`; frozen PR41 rejects unregistered baseline sources as expected. No Lean/Lake/compiler processes, real Git commits/mutations, shared target/manifest rewrites, PR edits/comments, pushes/merges, Tasks, outreach, or settings/token changes were undertaken. Compilation, final target bytes/hashes, proof work, and implementation remain the integrator's responsibility.

Public-safe evidence:

- `SOURCE_HASHES.json`: raw-byte SHA-256 pins for the sources examined.
- `MINIMAL_MANIFEST_DELTA.json`: four-entry proposal, canonicalization, unresolved final-source hashes, preserved fields, and excluded files.
- `TEST_RESULTS.json` and `python-tests.log`: test coverage, actual source validation, isolation, and non-execution statements.
- `review_fixtures.py`: reproducible Python-only harness; invoke with main and PR41 checkout paths as arguments from a new own review-output directory.

Private workstation provenance is intentionally separate in `PRIVATE_PROVENANCE.json`; do not include it in a public PR packet.

Key source SHA-256 values:

- Current `KERNEL_CONTRACT.json`: `2c66ac6bc539829173269b7ff0474a0b7def9beca335711d3d3ceeb7b6ba9ba9`.
- `scripts/check_kernel_contract.py`: `ff1f2dd9f5b19f96d314934fede23c6ff0b6a57bb82671050913050c7aae4d5e`.
- `scripts/audit_kernel.lean`: `673af3d23f5433cb17145e9de8cac97b40a7d513281b7c2a726fb19ca089facc`.
- `scripts/test_kernel_contract.py`: `1f4641c5dcd96809f9a65857384b1b0ea981b680116b6d5e9ebedfd5afca8a45`.
- `scripts/test_kernel_audit.py`: `81e103c0f06f5840ddd64ff997288a703e69557e39f1779f66bbd8c3ce3b0469`.
- Frozen `docs/h-targets/registration-proposal.json`: `9905e862ed131ada98cc46df1b2dc1a0a832a5109eca5728135227b27552de07`.
