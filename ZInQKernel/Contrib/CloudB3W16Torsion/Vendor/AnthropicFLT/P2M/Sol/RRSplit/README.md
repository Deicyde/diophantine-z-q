# H102 curve support: factored FLT proof sources

**Status: source draft, not yet compiled or axiom-checked. This is not an H102 discharge.**

Initial base: `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`. Rebased onto the
parent-approved restored main `2dc949d688c407e32823c4e751679d66b2f40e65`, whose
source tree equals that initial base; fixed Lean 4.35.0.
Source: `anthropics/fermats-last-theorem`, immutable revision
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Lean 4.33.1.
This lane owns only the five assigned source edges, the subsequently transferred
`tateChainRule` edge, and their `RRSplit` helpers. All other vendor dependencies
are primary-author prerequisites and are excluded from this change set.

## Interfaces and boundaries

Each original canonical module under
`ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol`
is an import-only facade. It imports the last part of an ordered helper chain.
The chain retains the original `P2MW.S_AlgebraicCurve_<source>` namespace and its
`solution` declaration and exact public statement. No caller import or theorem
name needs to change.

Factoring cuts lie between complete source sections with balanced namespace and
section scopes, never within a proof. Exact source line ranges, original hashes,
new-file hashes, notation expansions, and private-helper renamings are recorded
in `CURVE_SOURCE_MANIFEST.json`. The current source draft has 23 helper modules,
all at most 136,967 bytes, plus six small original-path facades.

* `residueTheoremK_ratFunc_of_isAlgClosed`: seven parts.
* `residueTheoremK_of_isAlgClosed`: five parts.
* `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`: five parts.
* `tateAgreement`: two parts.
* `tateTraceCompat_of_isSeparable`: two parts.
* `tateChainRule`: two parts.

## Compatibility changes

* Relocate imports using the primary author's canonical reuse map; reuse existing
  source ports already on the pinned main base rather than duplicating modules.
* Expand P2M namespace/open/export command helpers into ordinary Lean commands.
  Resolve metadata aliases directly and remove metadata reactivation commands.
* Inline local notation expressions within their original section scopes.
* Promote source-private helpers into the original file's own `P2MW` namespace
  for access across factoring boundaries. Source-private `_root_` declarations
  acquire that same per-file prefix rather than introducing public root collisions.
  Transparent private root abbreviations restore original dot-notation lookup;
  these are repeated at import boundaries and introduce no assumptions.
* Make ordinary scoped opens absolute, retaining P2M's root-namespace meaning.
* Use explicit tensor-product induction and pin definition/equality expressions
  where Lean 4.35 or factoring otherwise changes elaborator resolution.
* Preserve mathematical proof bodies and all public `solution` signatures.
* Use fixed Lean 4.35.0 and its documented backward elaboration option. Dependency
  pins, existing modules, targets, and project configuration are unchanged.

No new mathematical axiom, assumed residue/Riemann–Roch theorem, weakened target,
placeholder proof, runtime elaborator, new syntax, or new notation is supplied.
The imported `P2M.Util` is the existing main-port module; it is not copied into
this patch and no new metaprogramming implementation is introduced.

## Verification boundary

Compilation of the six complete edges and their `#print axioms` remain pending.
Actual proof-part compilation is underway on the parent-granted dedicated host.
Dedicated invocations use this lane's private slot locks, at most two Lean
processes with `-j 4 -M 16000`, and the parent-approved aggregate memory budget;
the shared original host retains its global lock and 48 GiB limit. The final exact geometric bridges
and H102 `#discharges` check belong to the primary author, not to this support
patch. Failed and successful compiler logs will be retained separately.

## Attribution

Copyright 2026 Anthropic, PBC. Apache License 2.0. Complete upstream `LICENSE`,
`NOTICE.upstream`, and `ATTRIBUTION.upstream.md` accompany this directory; the
primary author also supplies them at the shared vendor root. Each factored file
has a prominent modification/provenance notice. The upstream attribution records
credit Salvatore Mercuri and Kevin Buzzard for local-ring material, and Ruben Van
de Velde, Kevin Buzzard, and Salvatore Mercuri for valuation-subring material in
the affected source files. Original source notices and proof text are retained.

AI-assisted source factoring/port by the CloudB3 Worker16 support lane. No human
or independent review is claimed.
