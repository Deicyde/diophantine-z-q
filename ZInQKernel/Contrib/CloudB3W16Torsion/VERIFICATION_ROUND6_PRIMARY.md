# Round-6 primary API verification

All four primary modules reached in provider round6 compile on Lean4.35 /
Mathlib56a00585. The fresh four-module axiom check returns0,4.97s,7181080KiB
peak RSS and prints four actual axiom lists, each exactly
`[propext, Classical.choice, Quot.sound]`.

The source-port changes preserve mathematical statements and hypotheses:
activate existing root section scopes; use the current commutative-ring presheaf
abbreviation and tensor map API; explicitly supply the existing scalar-tower and
compatible-action instance; normalize definitional transport by reflexivity or
`erw`; retain the original gluing and square-zero lifting proofs. No new syntax,
notation, runtime registration, admission, axiom, or degree premise is added.

These are prerequisite checks, not a full degree/cardinality or Mumford discharge.
The raw source/compiler/axiom transcripts and source/cache hashes are preserved
privately. The final exact leaf and newest-Main discharge checks remain required.
