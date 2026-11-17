# Round-9 primary API verification

All four source modules newly failing in provider round9 now compile on the
pinned Lean4.35 / Mathlib56a00585 toolchain. Final module checks returned0 in
6.82s,7.84s,11.96s and8.83s. A fresh four-module axiom check returned0,20.63s,
7120136KiB peak RSS and printed four actual axiom lists, each exactly
`[propext, Classical.choice, Quot.sound]`.

The source changes defer a premature local namespace open; qualify the existing
private integer-extension function instead of introducing an alias to a private
root declaration; restore an absolute root `open … hiding …`; and normalize a
map-coercion rewrite using the same existing equality theorem. Private function
bodies, public statements and hypotheses are unchanged. No new syntax, notation,
axiom, admission or geometric-degree premise is introduced.

This is prerequisite evidence, not a Mumford discharge. Raw outputs and
source/cache hashes are preserved privately. The full genuine degree/cardinality
provider, exact leaf and newest-Main checks still need their own verification.
