# hsyn-fold (2026-11-12)

**What changed.** The published decomposition (docs/research/h-decomposition.md and
scratch/h-decomposition/Leaves.lean) now includes the eleven provers that finished after hsyn-fix.
- Leaves.lean adopts, each in its own section:
  - glue-a6-alg: `PkgI2.quatUnipotentTrivial` is proved, so A6 (`PkgI2.goodReduction_of_QM_rational3`)
    needs only its three leaves. `…'` also drops the auxiliary `w`.
  - glue-c10: `GlueC10.c10`, `frobLift`, `frobDense`, … and `PkgI3.trace_indep_of_ell`.
  - glue-d1-local: `GlueD1Local.D1_local'`, `D1_krasner'`, …
  - leaf-push: concrete R8, T9, T23, T29, T32. Their five `opaque` placeholders are removed and the
    bundles point to the new statements.
  - obj-bridge: §C-§E as `ObjBridge`. §F (I2-Rank from I3.M1) fails in this file on an instance
    search (`AddCommMonoid (ObjBridge.Hom A B)`, raising the heartbeat limits did not help). It was
    left out with a comment.
- The note: §0 (claim, Lean status, a dated "changes" paragraph, what is still not formalized),
  §2 (R8, R17, the T9/T23/T29/T32 rows, §2.3 counts), §3 (G1, G3, G7, G9, G14, G15), §5 (WP1, 2, 3,
  5, 7) and the §6 lines on A6/R8 are updated. All caveats are kept.
- h-trust.md: A6's suppliers line is now the Raynaud route, as rv-a6-route §5 says. h-b1's argument
  is kept as a second route, and a dated note is added.
- Merged by 00:17 PST, all without conflict: def-ladic-cond, glue-rho-cont, glue-b3-unram,
  glue-sqrt-local, glue-vigneras. The note cites them, but none is folded into Leaves.lean (R17 is
  stated in def-ladic-cond; T29 for N5's order is proved in glue-vigneras). None was missing.

**Final counts (Leaves.lean).** 40 of 54 leaves stated concretely (11 research, 29 textbook; 46
Props), up from 35. 14 placeholders (R1-R3, R5, R16-R22; T10-T12), down from 19. R8 is no longer
used by any step, so 21 research leaves suffice; it is still listed. Glue Props still taken as
hypotheses in the file: only `GlueI3.SemisimpleBaseChange` (C2, E1). C10 also assumes trace
identities and semisimplicity, which other steps must supply.

**Sorry list.** One: `HSyn.glueOutputs_of_leaves` (glue G1-G17, G19).

**Compile and axioms.** `lake build ZInQKernel.Hypotheses.JHeight` succeeded. The final
`lake env lean scratch/h-decomposition/Leaves.lean` (00:29 PST, 1.5 min, 12404 lines) exits 0 with
0 errors and 1 `sorry` warning. It has 81 `#print axioms`, covering every theorem the note calls
newly proved. All show `[propext, Classical.choice, Quot.sound]`, except
`HSyn.sixContactMin_of_leaves`, which adds `sorryAx`. There are no `axiom` declarations and 14
`opaque`. Log: scratch/hsyn-fold/log.md.

**Still not formalized.** Glue G1-G17 and G19 as a whole; every step on the actual surface `A` or
on `J₁(N)`; the 14 placeholder leaves; all leaves themselves.
