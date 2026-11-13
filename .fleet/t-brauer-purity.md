# t-brauer-purity (T1, T2, T14, T15)

**Main result: leaf T2 (Abhyankar's lemma, DVR form) is proved.**
`TBrauerPurityT2K.abhyankarDVR : PkgI2.AbhyankarDVR.{0}` is proved against the kernel's own
definition (`scratch/t-brauer-purity/T2Kernel.lean` imports `ZInQKernel.HDecomp.Objects`), together
with `abhyankarDVR_objBridge : ObjBridge.AbhyankarDVR`. A Mathlib-only, universe-polymorphic copy is
in `T2Full.lean`. The proof is global and uses no completions: it chooses `π = ϖᵉa/b` from ideal
arithmetic, puts `w = b tᵐ/ϖ`, shows `L(w)/L` is unramified via Mathlib's different ideal, and
gets `e(Q'|P) ≤ [M:L(w)] ≤ m` from the fundamental identity, with ramification-index towers and
residue-field transitivity. T2 can move from leaf to glue (bundle field `t2`).

**T15: real-place conjunct proved** (`TBrauerPurityK.h2TwoClasses_real` over the kernel's
`PkgI6.H2TwoClasses`). Hence `localH2CardC_iff : PkgI6.LocalH2CardC ↔ ∀ p, H2TwoClasses G_{ℚ_p}`.
Glue uses only the uniqueness half at finite places.

**Not proved:**
* T1 (Zariski–Nagata purity) needs Serre's criterion, Auslander–Buchsbaum and branch-locus theory.
* T14 needs global class field theory.
* T15 at `ℚ_p` needs local class field theory.
* T14 and T15 also need a cochain Kummer bridge to `Br[2]`, which requires crossed products.

None of this is in Mathlib 4.35. Tau Ceti and Stacks are not on this host, so no bridge could
compile. **Statement audit:** all five Props are correct as stated (docs §2).

**Compiles** (`lake env lean`, no sorry, axioms `[propext, Classical.choice, Quot.sound]`):
`scratch/t-brauer-purity/{T2Kernel, T2Full, LocalH2RealKernel, LocalH2Real, KummerUnramified,
KummerEtale, AbhyankarBricks}.lean`.

Report: docs/research/t-brauer-purity.md. Log: scratch/t-brauer-purity/log.md.
