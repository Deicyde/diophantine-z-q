# jp-an-retype (11-17)

**Result.** Javanpeykar's leaf is retyped onto the analytic stable height. New leaf
`JavanpeykarAnRetype.JavanpeykarThm111An` (ZInQKernel/Contrib/OneProof/JavanpeykarAnRetype.lean) is
`JavanpeykarDirect.JavanpeykarThm111` verbatim, except that the height predicate `IsStableHeightBarAn` is built on
`IsAnStableHeightSS` (metric on A_τ(ℂ)^an, semistability as printed). The docstring gives Thm 1.1.1, §2.3 and
diophantine_zq.tex L870. Proved, with standard axioms:
- `javanpeykarThm111_of_an : JavanpeykarThm111An → MumfordTorsionAlgClosed → JavanpeykarThm111`;
- the converse `javanpeykarThm111An_of_thm111`, given T35 (so the new leaf is no stronger than the old row);
- by-product `isSemistableRes_of_printed` / `isAnStableHeightSS_iff`: semistab-assembly's printed semistability
  is *equivalent* to `IsSemistableRes`, with no hypothesis.

The row's only deciding step is now R3', the same step that `bostLowerBoundAnSS` and `gaudronRemondThm14AnSS`
depend on.

**Compiles.** The new file builds. The full build of Main + Discharges + the new file passes (16217 jobs).
`#discharges` reports `DISCHARGES [OpenResearchLeaves48.javanpeykarThm111] by
JavanpeykarAnRetype.javanpeykarThm111_of_an`, still assuming [JavanpeykarThm111An, MumfordTorsionAlgClosed].
The autofold dry run of scratch/jp-an-retype/autofold.json gives 4/27 on 31 → 4/27 on 31 (count effect 0).

**Rating.** The new leaf is a consequence, rated GLUE, flag class reading-risk. It is not printed form, for two
reasons:
- R3' is still unproved and sits inside the height predicate;
- the leaf composes Thm 1.1.1 with §2.3 and is stated with h_Fal(Jac X), because a curve's h_Fal(X) is not
  defined in Lean.

**What remains.**
- R3' (another worker is proving it).
- The lead's ruling on the §2.3 composite.

No ON THE SPOT arguments were used. Report: docs/research/jp-an-retype.md.
