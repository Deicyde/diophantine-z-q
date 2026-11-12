# glue-wp3 (WP3, rv-hsyn repair 3): done

**Result (VERIFIED, compiled, no sorry, standard axioms only).** `scratch/glue-wp3/WP3.lean` proves
glue-descent's cochain leaves from the announced T14-T15:
`leafHasse_of_T14 : BrauerHasse2C → BrauerReciprocity2C → LeafHasse` and
`leafLocalTwo_of_T15 : LocalH2CardC → LeafLocalTwo`. It also proves
`b3_degree_le_QM_of_T14_T15`: B2-B3 with the constants, from the `TextbookLeaves` fields t14a, t14b,
t15, t30 and t31. The converses compile too: `LeafHasse ↔ BrauerHasse2C` given reciprocity, and
`LeafLocalTwo ↔` the finite half of `LocalH2CardC`. So glue-descent's forms say no more than the
announced leaves.

**Glue.** The ±1 ⊂ ℂˣ ↔ ZMod 2 dictionary preserves cocycles and coboundaries in both directions;
continuity into discrete ZMod 2 is local constancy. Restriction is `resp p = resC ℚ_[p]`, by `rfl`. The
real place comes from reciprocity's parity. No gap remains. Inflation enters B2 only through T31, which
was not touched.

**Compiles.** `scratch/glue-wp3/build.sh`: verbatim copies of the six glue-descent files (`cmp`) and
`WP3.lean`. The PkgI6 definitions are verbatim copies of those in pkg-I6 and Leaves.lean.

**Remains.** T30 and T31 are still leaves (their local-field glue is open). Also open: L' unramified
outside T (T32), instantiation on the actual A, and the other WP3 items. Integration note:
docs/research/glue-wp3.md §Integration.
