# Version 18: power-call certificate and split-cubic halving

PR108 is the first bounded part of the source-application group requested for PR107. Its earlier 31-block candidate remains at commit `6292f2e205ea9a3d098160392b09adc2b036ab4a`. The present candidate applies only its S15 certificate and S25 halving proof. All other source, citation, status and prose edits remain pending, not accepted by exclusion. The inverse-theorem adoption follows completion of the source-application group. Released Versions 16 and 17 and the current-release selector are unchanged.

Base manuscript SHA256: `8f4a6a99ce63b1bf6c7ab2fe71507795507a94281a775bf02fa07ca2be9359ae`. Candidate SHA256: `d6966b1921ff796d0f26592be5579e644f40085745f193c600210c1b198e9028`.

## Complete manuscript change map

| Change | Base lines | Candidate lines |
|---|---:|---:|
| 1 | 12251-12256 | 12251-12265 |
| 2 | 22274-22282 | 22283-22296 |

All 268 statement environments and 925 labels are unchanged. The first change adds the finite certificate argument and its immutable source link. The second proves the necessary halving condition used by the existing seed contradiction. These are author-prepared explanations for review, not independent acceptance.

## Certificate and its consumer

The saved circuit `construction/precision-natural-polynomial.json` has SHA256 `f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`. The new checker certifies every parameter of all 15,845 power calls, including their proposed result. A node is certified only if it is a nonnegative constant, an explicitly declared natural variable, or a sum/product of earlier certified nodes. No call output is certified. Induction gives a polynomial with nonnegative integer coefficients at each certified node, without assuming that any private block vanishes. The private-variable offset is not a node reference. The checker also checks references, allocations and the frozen source hash.

The manuscript uses exactly this sufficient syntactic property in its existing translation to natural-valued point codes. This does not prove the arithmetic semantics of the power template or the whole construction. The 11 tests include uncertified arguments in every slot, direct and indirect call-output dependencies, malformed references and the frozen-source mismatch. The existing required construction job runs the tests and checker and retains the result. Its 293,620 nodes, 54,056 explicit variables and 47,535 argument occurrences are finite computation claims checked by that job.

The in-text checker link is pinned to `6292f2e205ea9a3d098160392b09adc2b036ab4a`, whose checker bytes are unchanged here. It no longer points to mutable main. No new archive-tag link is introduced by this bounded change.

## Halving and its consumer

Over the odd good residue field in the existing proof, a point P with 2P=(e_i,0) on a split cubic has order four, nonzero ordinate, and abscissa different from every root. Its tangent line l satisfies product(X-e_a)-l(X)^2=(X-u)^2(X-e_i). Evaluating at each other root shows e_i-e_j=(l(e_j)/(e_j-u))^2. For the three roots 0, ell, -3ell, the existing prime conditions make respectively -ell, ell, -4ell nonsquares. No nonzero two-torsion point is divisible by two; the existing finite-group argument then gives the required exact two-primary order. This is a direct proof and imports no additional published theorem.

## Earlier findings and the remaining work

The two original PR107 review rounds remain in its public discussion. Both were incomplete. Their favorable scoped observations are not approval of the whole change. N107-1 requested the executable certificate supplied here. N107-2 requested preservation of H170, carried in [the pending status record](version18-cleanup-status.md). H170's original manuscript paragraph remains byte-identical. The present PR does not discharge that propagation obligation.

At PR108's original head, Fable requested changes and Astra's attempted report was rejected by the gate's schema validation: it put seven PR107 identifiers into a `prior_findings` list for which the current PR context supplied no identifiers. Astra also reached its context allowance and recorded incomplete source and history coverage. That attempt was not an accepted gate report. Its original report and findings are preserved in the PR discussion and run 43664822557, attempt 2. The four valid Fable findings are:

| Finding | Present treatment |
|---|---|
| `43664822557-2-fable-F108-1` | Nekovar local-control source comparison remains open for the following source PR. S21/S22 are absent here and the main argument is retained unchanged. |
| `43664822557-2-fable-F108-2` | Guillot, Serre and Silverman source comparisons remain open for following source PRs. Their proposed citation/application edits are absent here. |
| `43664822557-2-fable-F108-3` | S04 is absent here. The existing primitive-form wording and binding pointer remain unchanged. The following source PR must preserve the exact supplier/consumer record. |
| `43664822557-2-fable-F108-4` | The retained checker link is pinned to the reviewed commit. S17/S18 archive-link edits are absent here. Their verification remains part of the later source work. |

The reviews should decide whether these scope changes remove each finding's objection to this bounded PR. They do not settle the deferred applications. The gate-supplied earlier-finding identifiers for PR108 must be dispositioned; historical PR107 identifiers belong in the narrative, not additional entries in the gate's exact-ID list. No finding is overridden.
