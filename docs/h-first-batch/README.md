# First H-target registration batch (review draft)

This draft isolates **T13, T17, T19 and T21** from the larger H-target proposal in
PR #41. Its base is the merged kernel infrastructure at
`a5937595cde3e3db00975b81e5171cdef92c801a`.

## Registration contract

The proposed change is four new pinned source files and four target/provider
entries. All 941 existing source pins, the existing five target entries,
`baseline_commit`, headline, exports, toolchain, dependency pins, checker,
required workflow and mathematical baseline are to remain unchanged.

| Target | Reserved provider | Mathematical content | Full provider status |
|---|---|---|---|
| `ZInQ.Targets.H.T13` | `ZInQ.Contrib.H.T13_holds` | Full Skolem–Noether embeddings; ambient algebra central simple, source merely simple | Existing separate PR #42; preliminary exact integration review passed |
| `ZInQ.Targets.H.T17` | `ZInQ.Contrib.H.T17_holds` | All finite abelian number-field extensions embed in a cyclotomic field | Open; exponent-two/degree-at-most-two results are partial |
| `ZInQ.Targets.H.T19` | `ZInQ.Contrib.H.T19_holds` | Brauer–Nesbitt for arbitrary groups over any characteristic-zero field | Complete separate local candidate; preliminary exact integration review passed, publication remains with its author |
| `ZInQ.Targets.H.T21` | `ZInQ.Contrib.H.T21_holds` | Global different exponent bound for every number field and prime above p | Open; local complete-DVR proof still requires global transport |

No provider is declared by this registration-only draft, and no premise is
removed from the headline theorem. The expected registry size is 945 pinned
files / nine targets, of which the five original headline premises remain open.
No opaque placeholder leaf is registered. The other 30 H-target candidates and
their umbrella/shared definition modules are outside this batch.

T13, T17 and T19 use Mathlib objects directly and do not require the custom
HSyn definition layer. T21 reuses the already-pinned conductor object layer.
The four statement bodies are byte-identical to the frozen PR #41 bodies;
`validation/ReferenceEquivalence.lean` supplies independent `Iff.rfl` checks.
Minimal-import changes do not change any mathematical quantifier or assumption.

## Parallel proof contributions, after registration acceptance

Each contributor adds only their own `ZInQKernel/Contrib/H/<ID>.lean` and
Contrib helper modules. The provider type must be exactly the registered closed
proposition, without extra universe, explicit, implicit, instance or section
hypotheses. No shared manifest, statement or root-import edit is required.
Manifest sharding is optional for future new-target/definition work, not a
prerequisite for parallel proofs of these registered targets.

Existing proof implementations are coordinated rather than rewritten. In
particular, T13's public packet is
https://github.com/elliotglazer/diophantine-z-q/pull/42 . A future closed H-provider
wrapper must preserve its exact type and be checked independently against this
locked target; a related automorphism consequence cannot substitute for T13.

## Review and verification states

- Source-to-reference preservation: checked for the four target bodies.
- Target elaboration and reference equivalence: four scoped checks passed; each
  target reports only `propext`, `Classical.choice`, `Quot.sound`.
- Independent preliminary reviews: completed for all four targets and the
  registration/checker interface. T13/T19 exact proof connections passed scoped
  source/type checks. T17/T21 full providers remain open. Reports and their original
  source bindings are retained unchanged in `reviews/`; they are not a human or
  designated Astra acceptance. Primary publication locators not actually opened
  remain explicitly unverified; a checked formal proof is not a locator check.
- Full current-kernel build/replay/headline audit: pending for the final candidate.
- Registered in trusted main: **no**.
- Mathematical human approval or designated Astra/protected acceptance: **not
  supplied**. A valid candidate manifest or green build is not that approval.

The first-batch registration necessarily takes statement/infrastructure review.
An updated candidate manifest does not authorize its own acceptance. The gate's
source/artifact trust assumptions and source-stability limitations remain
explicit; this batch does not silently modify or declare the checker hardened.

## Scope

Focused Lean statements and contributor interfaces only: no manuscript, quartic
record, polynomial bound, CI permissions, release, or headline change. The full
H estimate and the existing five headline premises remain open. Incidentally
bumping Lean/Mathlib to import a newer library is outside this batch.
