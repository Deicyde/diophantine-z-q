# Controlled fork-dispatch rollout record

The owner required both the cache-provenance follow-up to PR133 and a successful
controlled fork-dispatch test before using the Lean profile on outside PRs.
The owner's subsequent instruction was that, if the test passed, the profile
could be used on outside PRs. This record supplies the completed prerequisites;
it is not an independent model review or permission to bypass admission checks.

[PR137](https://github.com/elliotglazer/diophantine-z-q/pull/137) merged at
01:55:43 UTC on November 17, 2026, as
`5c7ad7973b911ebc0ee1532cc8fcf5dbf70b52f4`. The controlled test used [PR144](https://github.com/elliotglazer/diophantine-z-q/pull/144),
an admin-operated fork, at head `f13c114ae1ed42f9f9863aa0118cc30e14082a1a`
on that protected base.

- [Kernel run 43999602932](https://github.com/elliotglazer/diophantine-z-q/actions/runs/43999602932)
  succeeded through `workflow_dispatch` on the exact fork head. Its complete
  audit covered 944 modules and 37,708 declarations. Project-cache restore and
  save were skipped. The run used read-only Actions, Contents, Metadata and
  PullRequests permissions, without a review environment or provider/App keys.
- [Gate preflight 44004656292](https://github.com/elliotglazer/diophantine-z-q/actions/runs/44004656292)
  succeeded and returned `eligible: true`, `ready: true`. Its original
  [lean-preflight.json](lean-preflight.json) is preserved unchanged. It binds
  the exact head and base, kernel run and attempt, source trees, workflow hash,
  artifact ID and digest, and the complete reported audit.
- [The original public result](https://github.com/elliotglazer/diophantine-z-q/pull/144#issuecomment-6937149187)
  was posted through Elliot's account at 03:24:21 UTC. [PASS.json](PASS.json)
  preserves the local observation unchanged, including the later cleanup.
  The throwaway PR was closed without merging. Cleanup run `44009975893`
  succeeded and no reserved test refs remained.

Kernel artifact `14295483026` has SHA-256
`87bb930351e49c28a6099304f66288077fef5cef8bd8200758339ce36f502973`.
The kernel workflow hash was
`a340919517c59da2c446ab3f7119377d9b4aa2cdc7760159cf93d5165cd7d745`,
and the contract hash was
`87028f6f342e173412914a32451584c86b02416e5061b837cb9df62bfb5392ac`.
An earlier preflight stopped on HTTP 503. The replacement reused the same
existing kernel run; it did not dispatch another kernel build.

This test validates the controlled execution/provenance route, not completion
of the mathematical formalization, unaffiliated-contributor authorization or
the new unattended admission implementation. There were no review-provider
calls: the PR was returned to draft before the reviewer stage, and the retained
gate artifacts contain preflight evidence rather than provider reports.

While repairing PR154, Astra read back both successful run states, exact heads,
the PR137 merge and the original public comment through the GitHub API on
November 17, 2026. Those observations agree with the retained records. The
current workflow must still enforce its own exact-head, source, permission,
admission and artifact checks on every subsequent PR.
