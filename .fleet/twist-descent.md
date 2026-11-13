# twist-descent — fleet note (2026-11-13)

**Main result: kf-glue's glue Prop `TwistDescent` is proved, statement verbatim, no hypotheses.**
kf-glue's standard statement `GaloisDescentMor` (stated, unused) is proved as well.
`TwistDescent` is true as stated, so no statement change is proposed.

Proved (namespace `G0ModField.KernelField`, axioms `[propext, Classical.choice, Quot.sound]`):
- `theorem twistDescent : TwistDescent`
- `theorem galoisDescentMor : GaloisDescentMor`
- `conjIsogMaps_of_mulIsogeny : MulIsogeny → ConjIsogMaps`; `conjIsogMaps_of_kerUnitOpen'`;
  `conjIsogMaps_of_cotangent'`
- `kernelFieldExists_of_kerUnitOpen'`: inputs T6, NOS, Raynaud, TorsionStructure, T27, FS5,
  KerUnitOpen. `kernelFieldExists_of_mulIsogeny`: the same with `MulIsogeny` in place of
  `KerUnitOpen`.
- Tools:
  - `TwistDescentGD.exists_open_gal`, `TwistDescentGD.descend`: Galois descent of scheme morphisms
    along a finite Galois `k'/k`, from Mathlib's fpqc `EffectiveEpi`.
  - `TwistDescentHFD.hfd`: a `G_L`-invariant `ℚ̄`-morphism between base changes descends to `L`.
  - `TwistDescentXC.xc_*`: comparisons between base changes.

What compiles:
- `ZInQKernel/Contrib/TwistDescent/GaloisDescent.lean`, Mathlib only (`lake build` OK).
- `scratch/twist-descent/TwistDescent.lean`, the single-file check (7959 lines), built by
  `scratch/twist-descent/assemble.sh` from `scratch/kf-glue/KfGlue.lean` (verbatim) plus
  `Part{XC,HFD,Main,GDM,Final}.lean`. `lake env lean` exits 0 with no sorry
  (`build4.txt`, about 1.5 min).
- `scratch/twist-descent/verbatim_check.py` confirms the statements are kf-glue's text.

What remains: nothing for this task. Downstream, `ConjIsogMaps` and `KernelFieldExists` still need
`MulIsogeny`/`KerUnitOpen` (mul-rigidity) and FS5 `FibreComTrivial` (g0-fibresimple).

Report: `docs/research/twist-descent.md`. Log: `scratch/twist-descent/log.md`.
