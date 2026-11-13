# g12-det results log

Targets (copied verbatim from scratch/g0-mod-galois): `G12Weight` (part_galois.lean),
`DetTate`, `ResQFiniteIndex` (part_det.lean).

## ResQFiniteIndex — PROVED (VERIFIED, compiled)

- File scratch/g12-det/ResQ.lean (`import Mathlib` only; copies `PkgI4.Qbar`, `PkgI4.GQ`,
  `G0Galois.resQ`, `qEmbRing`, `qEmb`, `resQ_spec`, `eq_resQ`, `ResQFiniteIndex` verbatim).
- `G0Galois.resQFiniteIndex : ResQFiniteIndex`. Proof: `qEmbRing K : ℚ̄ → K̄` is bijective
  (`IsAlgClosed.ringHom_bijective_of_isIntegral`, `K̄` integral over `ℚ`); `K' := image of K in ℚ̄`
  has `[K':ℚ] = [K:ℚ]`; `fixingSubgroup K' ≤ range (resQ K)` (conjugate `σ` by `qEquiv`, then
  `eq_resQ`); index of `fixingSubgroup K'` = `[K':ℚ] ≠ 0` (`finrank_eq_fixingSubgroup_index`);
  `Subgroup.finiteIndex_of_le`.
- run1 (04:14, 2m37s): 0 errors. run2 (04:19): 0 errors; axioms [propext, Classical.choice,
  Quot.sound].
