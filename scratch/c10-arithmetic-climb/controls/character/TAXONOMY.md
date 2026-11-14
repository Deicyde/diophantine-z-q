# Negative-fixture taxonomy (added after review; the four `controls/*.lean` files and their
# logs are UNCHANGED — their bytes and hashes in DESCENT-RECEIPT.json still stand)

These four files are **structural application / guard-rejection fixtures**. Each shows that the
candidate theorem, as proved, *cannot be applied* once a hypothesis or instance is dropped, and
that the rejection is a real elaboration failure at the intended place. **None of them is a
mathematical counterexample**, and none should be reported as one.

| fixture | what the failure actually demonstrates | what it does NOT demonstrate |
|---|---|---|
| `BadZeroLevel.lean` (`failed to synthesize NeZero 0`) | the `NeZero n` guard is load-bearing in the *statement* applied here: with `n = 0` the theorem does not apply and the instance is not silently derivable | that descent at level 0 is false. `ZMod 0 = ℤ` has unit group `{±1}`, so a level-0 descent may well be provable by another route; this fixture says nothing about it |
| `BadSecondPlace.lean` (type mismatch) | the proved statement supplies one character for ONE caller-fixed place; the two-place statement is a different type and the term does not inhabit it | that no character can satisfy two places at once. For two places agreeing on the relevant roots of unity it can; the fixture is about term/type identity, not universal falsity |
| `BadNoPrimes.lean` (type mismatch) | the actual consumer's `∀ p ∈ T, p.Prime` is really used: with it dropped the term has the wrong type | that the order bound is false without primality. It is a direct-term mismatch, not a refutation |
| `BadNonClosedTarget.lean` (`failed to synthesize IsAlgClosed ℚ`) | the value lemma's algebraic-closedness input is load-bearing: it is inapplicable with `K = ℚ` | an explicit root-of-unity counterexample over `ℚ`. No witness (e.g. a character value outside `ℚ`) is constructed here |

The in-file comment headers were written before this taxonomy and are **not** edited, so that the
reviewed bytes, hashes and raw logs stay identical; this file is the authoritative reading of what
the four fixtures prove. The positive compiled checks (`CharacterDescentChecks.lean`) and the
positive boundary applications (`BoundaryAndAxioms.lean`, levels 1 and 4) are unaffected.
