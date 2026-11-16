# Round-7 primary API verification

The two primary-retained round7 modules compile on the pinned Lean4.35 /
Mathlib56a00585 toolchain. The fresh two-module axiom check returns0,7.76s,
7153692KiB peak RSS and prints two actual axiom lists, each exactly
`[propext, Classical.choice, Quot.sound]`.

The Picard sheaf proof is adapted to the current precoverage API. It uses the
existing small-hypercover sheaf criterion, maps the cover to the underlying
schemes, and supplies its original over-base structures explicitly. This retains
the original open-cover gluing argument and adds no hypothesis. The tensor-lift
proof removes tactics after a conversion already solved the goal. No new syntax,
notation, runtime code, admission or axiom is introduced.

These are prerequisite checks, not a full Mumford discharge. The exact genuine
degree/cardinality provider and final leaf remain pending their own checks.
Raw transcripts and source/cache hashes are preserved privately; this document
is a summary, not a complete compiler transcript.
