# Round-8 primary API verification

Both primary modules newly reached by provider round8 compile on the pinned
Lean4.35 / Mathlib56a00585 toolchain. Module checks returned0 in5.62s and6.62s.
A fresh two-module axiom check returned0,5.37s,7278144KiB peak RSS, printing two
actual axiom lists, each exactly `[propext, Classical.choice, Quot.sound]`.

The changes activate existing root algebraic-geometry scopes and use a
semireducible map-coercion rewrite with the same existing equality theorem.
Public statements and mathematical hypotheses are unchanged. No new syntax,
notation, admission, axiom or geometric-degree premise is introduced.

This is prerequisite evidence, not a Mumford discharge. Raw compiler outputs and
source/cache hashes are preserved privately; the genuine full cardinality/degree
provider, exact leaf and newest-Main discharge checks remain pending.
