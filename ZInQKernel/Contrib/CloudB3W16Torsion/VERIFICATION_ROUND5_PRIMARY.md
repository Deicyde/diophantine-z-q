# Round-5 primary API verification

The three newly reached primary API modules compile on the pinned Lean4.35 /
Mathlib56a00585 toolchain. The fresh three-module axiom check returns0,4.87s,
7178452KiB peak RSS and prints exactly the standard three axioms for all three
checked APIs: `propext`, `Classical.choice`, `Quot.sound`.

The changes use the current commutative-ring presheaf tensor-map lemma, remove an
already-solved trailing tactic, and rename the projectivity transport theorem to
its current semilinear-equivalence API. The existing equivalence, scalar action,
public statement and hypotheses are unchanged. No new notation, syntax,
admission, axiom or provider premise is introduced.

These are provider-porting checks only. The entire degree/cardinality provider
and exact Mumford leaf are not claimed until their own kernel, discharge and
axiom checks succeed. Raw transcripts and source/cache hashes remain private.
