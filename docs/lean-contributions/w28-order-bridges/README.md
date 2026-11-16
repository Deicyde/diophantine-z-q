# W28: upstream delivery of the exact QM order prerequisites

This is a focused transfer of [fork PR30](https://github.com/Deicyde/diophantine-z-q/pull/30)
at `97378a0a2819b6130b4ea753ef4888d471af2c0a` to upstream
`fe026617ddd1f2275d7dd0190e5a3814a1c5d1b6`. It is **not** an `R1fpAb`
witness, a recognized headline-premise provider, a manuscript change, or a
completed Hilbert10 proof. The full witness and historical `#discharges`
limitation remain exactly as recorded in the preserved fork evidence.

## Minimal source transition

All **28 Lean modules** retain their paths, definitions, namespaces, theorem
statements and mathematical proof bodies. The only Lean source changes are:

- `CloudB4W28FineModuli/MaximalOrder.lean:2`
- `OneProof/R1fpAbOrderBridges.lean:1`

Both imports change from `ZInQKernel.HDecomp.QM.Structures` to the accepted
upstream `ZInQKernel.Contrib.HDecomp.QM.Structures`. The latter's entire source
blob is identical to the original fork source (`f492800c7537986f5315027f9d5ac9a9e958040a`).
Current `HDecomp/A6/A6` and `Repo/A1Quaternion` are also byte-identical. Current
`HDecomp/Objects` differs in the unrelated QMDichotomy/Yu leaf bundles; it is
rebuilt from upstream rather than borrowed from the fork. No W28 arithmetic
proof consumes those dichotomy assumptions.

No new Lean dependency, Lake require, protected-contract change, pin change,
root-import change, missing fork intake, or PR68 supplier is needed.
[Upstream PR68](https://github.com/elliotglazer/diophantine-z-q/pull/68) remains
separate; none of its union is copied or modified by this transfer.

## Exact closed results retained

Namespace `ZInQ.Contrib.CloudB4W28`:

- `isMaximalOrder_orderLattice : QuaternionAlgebra.IsMaximalOrder orderLattice`,
  with the literal original `LeafQM.O` carrier by `rfl`.
- `isIndefiniteRamifiedExactlyAt_two_neg_three :
  QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt (2 : ℚ) (-3 : ℚ) 2 3`.
- Actual local division at `ℚ_[2]` and `ℚ_[3]`, real tensor-product splitting
  into `Matrix (Fin 2) (Fin 2) ℝ`, and reduced-trace Gram determinant `-36`.
- The entry's closed maximal-order/ramification aliases and conjunction.

None assumes a moduli witness or maximality/ramification premise to prove it.
The exact task input remains the unchanged fork statement at
`0e70c94e4a2d26838f0766cd69b39bd02f48fb85`; that existential is not proved here.

## Preserved historical files and notices

The eight original non-Lean files are preserved **byte-for-byte** outside
Contrib, as required by the current upstream source validator:

- `README-fork.md`, `AXIOMS-fork.txt`, and `VERIFICATION-fork.json` in this
  directory are historical fork-source evidence, not new upstream passes.
- `ThirdParty/CloudB4W28FineModuli/{LICENSE,NOTICE.upstream,ATTRIBUTION.upstream.md,NOTICE.md,SOURCE_MANIFEST-fork.json}`
  holds the complete original notices and provenance records.

`UPSTREAM_TRANSFER.json` maps every original file, hash and current location.
Bare notice filenames and old work paths inside unchanged source comments or
historical documents refer to that original context; the locations above are
where their unchanged bytes live in this upstream candidate. The historical
vendor manifest's paths remain relative to the original Contrib vendor root,
not its new ThirdParty storage directory.

Upstream proof source: Anthropic FLT
`6e837e75355538c7f80bab5b956861e86c4eacc2`, with complete Apache-2.0 and
third-party notices preserved. The 25 vendored arithmetic modules are not the
full fine-moduli theorem cone. There is no new license grant or premise.

## New upstream verification

Fresh isolated 32 GiB FaaS compilation, Lean 4.35.0
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, unchanged Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

- **32/32 modules compiled, zero reused project artifacts**, including all
  28 incoming modules and the four actual upstream prerequisites.
- Closed-type examples, literal carrier equality and actual real tensor
  splitting passed. All **11 actual axiom reports** contain exactly
  `[propext, Classical.choice, Quot.sound]`.
- Source validator passes: 945 unchanged locks, 972 tracked project modules,
  `acceptance: false`. Seven contract tests and 18 actual pinned-kernel
  adversarial tests passed.
- Independent source-static audits found no explicit public-name collision
  with all 948 current-upstream or 1,414 PR68 Lean files, and confirmed the
  two import edits and eight preserved metadata files.

- The unchanged upstream auditor passed a selected replay of all 28 incoming
  modules, their four current prerequisites and one separate literal reference:
  **33 modules / 991 serialized declarations**, no runtime declarations skipped,
  no duplicate names, and only the standard three axioms. Its headline comparison
  used the independent literal reference, not self-comparison. The reference is
  unsubmitted test scratch, not a new mathematical premise or public proof file.

These are selected component checks, not the complete upstream 972-module
kernel/registry/CI run or Protocol B acceptance. Historical fork success is not
used as an upstream pass. Full hosted computation and App review remain pending.

Actual focused command:

```sh
python3 /tmp/w28-upstream/reused/commands/direct_build.py \
  --root /tmp/w28-upstream/repo --out /tmp/w28-upstream/build-focused \
  --toolchain /tmp/w28-upstream/toolchains/leanprover--lean4---v4.35.0 \
  --jobs 2 --max-failures 1 --module-timeout 300 \
  ZInQKernel.Contrib.OneProof.R1fpAbOrderBridges
```

The same fresh libraries were used for original `ProofCheck.lean` and
`EntryProofCheck.lean`; every compiler command retained
`-Ddebug.skipKernelTC=false`. A new dependency/access/test gate is not inserted
in the proof. Full required hosted computation contexts and the designated
App's exact-revision review remain pending integration checks.

## Draft-only delivery and review boundary

The current Protocol B workflow directly merges or enables auto-merge after a
successful ready-PR review. Drafts return before that path
(`protocol-b.yml:1626–1628`, `1967–2006`). This task expressly prohibits landing,
so this upstream PR is **draft only**: do not mark it ready, request
`/protocol-b review`, enable auto-merge, or otherwise trigger that merge path
without the owner's separate authorization. The policy is not changed or
bypassed. Local source or kernel checks do not substitute for designated-App
acceptance, human reading, or outside-family review.

This transfer changes no existing manuscript, registered application record,
proof-provider spelling, frozen target or other held claim. **Hilbert10 and
R1fpAb remain open.**
