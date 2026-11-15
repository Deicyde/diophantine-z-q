# p1-scheme results log

- 03:28 start (fresh run). Base HEAD 3782dac8e.
- Choice: P := ℙ(ULift (Fin 2); Spec ℚ) (CloudW07 `ProjectiveLine.relativeLine`), not `projectiveLine ℚ`:
  `normalized`, `comp_normalized`, `normalized_eq_of_mul_eq_one`, `relativeChartCoordinate(_mul)`,
  `homOfSections_preimage_standardOpen` are stated for it. IsProper: instance `ProjectiveSpace.instIsProper`.
  Smooth: from Mathlib `AffineSpace.smoothOfRelativeDimension` via `standardOpenIso`.
- scratch/p1-scheme/P1.lean part 1 COMPILED (VERIFIED): restriction lemmas, `tau : ToP1 L` (charts std 0/1,
  f,g = relativeChartCoordinate transported by topIso; inv, basicOpen_f/g proved).
