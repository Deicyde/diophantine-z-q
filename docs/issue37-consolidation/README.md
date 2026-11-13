# Issue 37: source-preserving proof consolidation

**This package is not a completed Hilbert’s tenth problem proof.** Its purpose is to put the existing proof suppliers and consumers in one reviewable source tree, remove repeated copies of the same files, and make the remaining end-to-end work explicit in the [Hilbert10 roadmap](../hilbert10-roadmap.md).

## What is combined

The consolidation uses main `54de47e9a0e82c587493dad34926e9de79715ac7` as its base. It preserves 510 unique files (486 Lean sources and 24 source notes) from 21 proof PRs:

`#38 #39 #40 #42 #43 #45 #46 #47 #48 #49 #50 #52 #55 #56 #57 #58 #59 #60 #61 #64 #67`.

Those PRs contain 661 file occurrences. The union eliminates **151 repeated file occurrences** by storing each identical path/blob once. No theorem body is rewritten, renamed, weakened, or replaced. Every surviving file maps back to its exact original PR, commit, Git blob and SHA-256 in [`SOURCE-MAP.json`](SOURCE-MAP.json). Different-name declarations with identical proof expressions are not deleted merely because their bodies look alike; their names and consumers are preserved.

This includes the coefficient/finite-field/analytic work, Skolem–Noether, Chebotarev, Brauer–Nesbitt, general tame Abhyankar, ramification and different suppliers, genuine D1 consumer, cochain/cocycle work, actual completion bridges, and the **conditional** global KW support. A supplier’s full type still governs its scope. In particular, public #46 supplies the original conditional T30 route; this consolidation does **not** smuggle in the later unpublished 494-module LocalKW source/type packet or claim its timed-out raw verification passed.

## What is held apart, and why

- **#41 and #51:** competing H target/registration drafts. Their T13/T17/T19/T21 files and contract variants must not be combined by last-writer-wins. Extracted target statements are not proofs of their own hypotheses.
- **#54:** thin provider bindings stacked on its prerequisite branch. The corresponding target/registry choice needs a separately verified source-to-consumer integration, not an import of two files in isolation.
- **#53:** optional Axiom object/cache bridge with its own dependencies and workflow. Its current point/Tate extensions remain distinct work; they are not silently imported into the unchanged main compiler/package configuration.
- **#44:** contract-regeneration tooling. Changing an admission/checker policy is not proof-source deduplication.
- **#62:** proposed H-decomposition, Objects/root/contract and blueprint changes. The useful proposed glue is recorded in the roadmap, but this proof-only union preserves current main’s protected Objects, root and target statements instead of mixing changed object/application contracts without review.
- **#63:** earlier organization snapshot. The new roadmap can reuse its verified context, but must preserve current-main navigation/policy changes and not refresh a stale manuscript binding to make a docs check green.

Original PRs and their review/failed-run histories remain intact. This proposal describes a replacement map; it does not close or land any original PR, cancel an owner’s landing attempt, or turn historical component evidence into a new assembled-proof acceptance.

## Revision and evidence discipline

The initial source inventory is preserved. During acquisition, #64 was rebased from `0b09211e7eeaa084e00fcf16e84887026aea6530` to `ff76d64fed503a0227f1718a115da67749e83343`; all eight contributed proof-file blobs were verified identical. The ledger records both identities. #62 likewise moved from `4abd51a3359f10c00c6654b5772d5e91cee0dcfd` to `e303a42543e9adf89aa70075372b622f4870a770`; its proposed object/contract scope remains held apart.

The original root, five target definitions, compiler and package pins, registry, checker logic, policies and current manuscript are unchanged by this union. Current main’s separate review-gate retirement is preserved. Earlier notes and reviews retain the identities and qualifications of the source phase they actually checked; unknown serving-model reviews are not relabelled as designated acceptance.

Compilation, exact full-type checks, raw kernel replay, the stock full normal gate, exact-head public CI, actual consumer wiring, accepted integration, and a final Hilbert10 theorem are distinct statuses. The **new combined tree** needs its own full validation; another PR’s green CI does not substitute for it. See this proposal’s exact-head evidence for actual results rather than reading old “pending” producer notes as new statuses.

## Completion criterion

A complete result must supply every remaining actual mathematical object, compatibility square, representation/trace, conductor/height and analytic hypothesis required by the chosen end-to-end route, prove the integer-definition theorem, and verify the final Hilbert10 consequence. A green consolidation package is an intermediate milestone. **Until the intended Hilbert10 result is fully proved, the work is not done.**
