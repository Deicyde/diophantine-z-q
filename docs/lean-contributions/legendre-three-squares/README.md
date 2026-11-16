# Legendre three-square theorem: focused upstream supplier

This contribution supplies the full classical three-square **IF** statement,
including zero and without additional positivity, squarefree or fixed-residue
assumptions beyond Legendre's excluded-form hypothesis:

```lean
∀ n : ℕ, (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) →
  ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + z ^ 2
```

Export:
`ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof`.

## Minimal source and definition boundary

The primary fork source is
`47ca4df214d1402caa3de40c7d6f661567120fcd`, published separately as
[fork draft PR36](https://github.com/Deicyde/diophantine-z-q/pull/36).
Its defining proposition is
`ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares`, declared in
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:600–601`. That definition and
its surrounding H29 assembly are **not accepted on upstream main** at
`fe026617ddd1f2275d7dd0190e5a3814a1c5d1b6`.

This upstream entry therefore preserves the public theorem name and writes the
exact **expanded** proposition above. It does not copy or redefine H29, import
an unmerged fork assembly, assume PR114 landed, or rename/weaken the canonical
H10 target. The primary entry's mathematical proof body is unchanged: convert
the excluded-form hypothesis to a negated existential, invoke the genuine Atlas
natural-number theorem, cast its witnesses to integers, and reverse the equality.
The missing defining import is replaced by the existing Mathlib tactic import.
There is no new Lake dependency.

The vendored `Atlas.lean` is byte-identical to the primary source
(SHA-256 `ca50ef1ad9cd9519c4fb440d53803810e9b6c9d8b8a9ca3bea75d74fbaed4797`).
Removing only its added attribution comment and enclosing namespace recovers the
exact public Atlas source:

- Repository: https://github.com/facebookresearch/atlas-lean
- Revision: `8860f7b55276b96e51df600021845dd5eb48f5ab`
- File: `MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean`
- SHA-256: `a902763f2e8c6ca272f03774536d58b93c99f5843214288efe226f5e767da284`

The imports and Ankeny proof bodies are unchanged. The namespace wrapper avoids
adding a second root `Nat` theorem.

## Preserved notices

The complete upstream license, including its prefatory line, is preserved
byte-for-byte at `ThirdParty/LegendreThreeSquares/LICENSE` (SHA-256
`fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`).
`ThirdParty/LegendreThreeSquares/NOTICE-fork.md` retains the original fork
source/change record. Its adjacency and defining-import references describe the
original fork layout; this current index gives the upstream paths and expanded
statement boundary. The vendor's original copyright and license header are
unchanged. No new license grant is asserted.

Relocation addendum: the retained vendor comment at `Atlas.lean:44–45` refers
to the complete license and notice being next to the file in its original fork
layout. In this upstream contribution, those exact preserved bytes are at
`ThirdParty/LegendreThreeSquares/LICENSE` and
`ThirdParty/LegendreThreeSquares/NOTICE-fork.md`; this addendum supersedes only
the old adjacency locator. The compiled proof source itself remains at
`ZInQKernel/Contrib/OneProof/LegendreThreeSquares/Atlas.lean`, not ThirdParty.
The entry comment's grouped source/license/notice locator at lines 14–15 is
clarified here: only the complete license and historical notice are stored in
ThirdParty; the compiled source is the Contrib module just named.
The historical notice's defining-import/type and
receipt sentences describe the primary fork contribution, not this upstream
expanded-type export or new upstream checks. No pending primary discharge or
trust-level-zero run is represented as completed by that historical sentence.

`TRANSFER.json` records each source/destination hash and deliberate change. Only
two new Lean files, the two preserved notice/license files, and focused transfer
documentation are added. Existing source, definitions, contract, compiler pins,
proof providers, other PRs and assemblies remain untouched.

## Verification and limits

The proof has been freshly compiled against upstream's unchanged Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` in an isolated 32 GiB Linux worker.
Both project modules compiled from source; no project object files were borrowed.
The complete literal type, closed `@` export, integer witness carrier and zero
case passed. Both exported theorem axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

Selected replay with the unchanged upstream auditor passed for three modules
(the two owned modules and a separate independent literal type reference):
101 serialized declarations, no skipped runtime declarations or duplicate
names, standard-three axiom closure and full literal-type comparison. Eighteen
pinned-kernel adversarial tests and seven source-contract tests passed.

The full upstream registry/CI and approved reviewer acceptance remain separate
integration checks. The primary writer's cold Main/discharge run remains
primary-owned and is **not forecast** here. A local or selected proof check is
not a full H29 assembly, H10 proof, or manuscript acceptance.

Portable reproduction instructions (not literal original private argv):

```sh
lake exe cache get
lake build +ZInQKernel.Contrib.OneProof.LegendreThreeSquares
# Import the module in a scratch file and check the full literal type,
# the zero case, and the two actual #print axioms reports.
lake env lean LegendreTypeAxioms.lean
```

This is an AI-assisted source-preserving delivery of a verified supplier, not a
new proof claim or a new literature-reading verdict. No printed-source reading
flag is cleared by formal-source review.

## Draft-only endpoint

The upstream ready-review workflow can merge or enable auto-merge. This work
has no landing authorization, so the PR remains **draft**: no ready flag,
`/protocol-b review`, auto-merge, main push or merge is requested or performed.
Pending fork/H29 integration and full H10 remain explicit.
