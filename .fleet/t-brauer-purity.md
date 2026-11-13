# t-brauer-purity (T1, T2, T14, T15)

**Verdict.** None of the four leaves is fully proved. **T15's real-place conjunct is proved**, over the
kernel's own `PkgI6.H2TwoClasses`: `TBrauerPurityK.h2TwoClasses_real`. Hence
`TBrauerPurityK.localH2CardC_iff : PkgI6.LocalH2CardC ↔ ∀ p, H2TwoClasses G_{ℚ_p}`, and glue uses only
the uniqueness half at finite places. **T2 (Abhyankar, DVR form): the case `L = K` is proved**
(`abhyankarDVR_conclusion_of_L_eq_K`, the leaf's exact conclusion), along with its lower half
`n ∣ e(Q|𝔪)` for general `L`, the derived facts (`M/K` finite separable, `integralClosure R M`
Dedekind), and the Kummer step "adjoining `u^{1/e}` (`e` invertible, `u ∈ A`) is unramified wherever
`u` is a unit" in global Dedekind form (via Mathlib's different ideal). **T1 and T14**, and T15 at
`ℚ_p`: nothing proved. They need Serre's criterion and Auslander–Buchsbaum (T1), and class field
theory plus a cochain Kummer bridge to `Br[2]` (crossed products) for T14 and T15; none of this is in
Mathlib 4.35. Tau Ceti and Stacks are not on this host, so no bridge could compile.
**Statement audit:** all five Props are correct as stated (docs §2).

**Compiles** (`lake env lean`, no sorry, axioms `[propext, Classical.choice, Quot.sound]`):
`scratch/t-brauer-purity/{LocalH2Real, LocalH2RealKernel, KummerEtale, KummerUnramified,
AbhyankarBricks}.lean`. `LocalH2RealKernel` imports `ZInQKernel.HDecomp.Conductor.I6Base`.

**Remains:** T2 in general. docs/research/t-brauer-purity.md §4 gives a global plan without
completions: steps (b) and (c) are proved, while step (a) (CRT choice of `ϖ`) and the algebra/tower
plumbing are open, estimated at 300–500 lines. T1, T14, and T15 at `ℚ_p` need the infrastructure
listed in §4.

Report: docs/research/t-brauer-purity.md. Log: scratch/t-brauer-purity/log.md.
