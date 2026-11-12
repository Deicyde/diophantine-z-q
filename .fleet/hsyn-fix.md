# hsyn-fix: reviews applied to the H decomposition (2026-11-11)

**What changed.** `docs/research/h-decomposition.md`: every repair of rv-hsyn applied, with its
exact text (repair 1, the TYZ sentence: the Lean form uses only the case 𝓛(n) = 0, a special case
of the printed hypothesis that avoids the unproved "i.e." of Thm 3.5(2), nt-tyz F6; repair 2,
route K's glue; repair 3, B2-B3 from glue-descent's cochain forms with WP3 open; repairs 5-10;
repair 4 rewritten for the new sorry list). Folded in: rv-leaves-a (QMHauptmodul composite, BG
narrowed to Thm 2.1 and the §3 datum; Pazuki hardened to `h_F + 3`, same final constant;
GlueOutputs glue, never a leaf), rv-leaves-b (QM dichotomy's combined locator; Poincaré via Milne
1986 Prop. 12.1; cochain forms I6.2a′-c′ announced; localization citation for the global different
leaves, or I6.6/I6.7; shared object layer in WP1), rv-a6-route (A6 sound on the Raynaud route,
proved from R6, R7a, T5 and `QuatUnipotentTrivial`; R8 droppable once that is proved, count kept at
22), glue-I6-rest (D3, D4 proved; D1's `e ≤ a!` global with the local caveat; cores of the
square-root criterion and cyclic inflation), glue-I3-linalg (C2, E1 proved modulo
`SemisimpleBaseChange`). §0 grew 18% (1389 → 1640 words); all caveats kept.

`scratch/h-decomposition/Leaves.lean`: A6 proof (rv-a6-route §10), D4 proof (glue-I6-rest
Conductor.lean), D3 `PkgI6.sq_principalUnits` proved, C2/E1 with the GlueI3 linear algebra
(glue-I3-linalg C2.lean §0, §5), Pazuki `+3` in `PazukiOutput`/`pazuki_numerics`, the bundle's
T14-T15 fields switched to `BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`, citation fixes
in docstrings. Header says `scratch/hsyn/assemble.py` no longer reproduces the file (assemble.py
itself is outside this task's write scope and was not edited).

**Final counts.** 54 leaves (22 research, 32 textbook); 35 stated concretely (39 Props); 19
`opaque` placeholders; 20 glue steps G1-G20 composed in G0. Named glue Props taken as hypotheses:
`PkgI2.QuatUnipotentTrivial`, `GlueI3.SemisimpleBaseChange`.

**Sorry list.** Exactly one: `HSyn.glueOutputs_of_leaves` (hence `HSyn.sixContactMin_of_leaves`).
The former sorrys A6, D4, D3 are proved.

**Compile and axioms.** `lake build ZInQKernel.Hypotheses.JHeight`: success. `lake env lean
scratch/h-decomposition/Leaves.lean`: exit 0, no errors (1m28s; log `scratch/hsyn-fix/log.md`,
output `scratch/hsyn-fix/leaves3.out`). 45 `#print axioms`: 44 give only `propext`,
`Classical.choice`, `Quot.sound` (including A6, D3, D4, C2, E1, `pazuki_numerics`); the top theorem
adds `sorryAx`. No `axiom` declarations.

**For integration (outside scope).** The docstring of `TYZThm35ReadingA` in
`ZInQKernel/Hypotheses/CR3Literature.lean` still says "weakened" (rv-hsyn repair 1); h-trust A6's
suppliers line should be updated as rv-a6-route §5 says.
