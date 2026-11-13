# x1-belyi results log

## 2026-11-12
- 22:59 `lake build ZInQKernel.HDecomp.ModCurves.Glue`: OK (9054 jobs).
- 23:05 `scratch/x1-belyi/X1Belyi.lean` v1 (definitions `nTors`, `ratHom`, `ConstantFieldIsQ`,
  `HasRationalPlace`; leaves `TorsionStructure`, `GoodReductionUnramified`, `CurveOfFunctionFieldQ`,
  `X1ConstantField`, `X1RationalCusp`; lemmas `nTors_card`, `exists_addOrderOf`): compiles, no errors.
  VERIFIED (compiled).
- FINDING (VERIFIED, read in Mathlib `ModelsWithJ.lean` L72-80): Mathlib 4.35's `ofJNe0Or1728 j` is
  `⟨j − 1728, 0, 0, −36(j − 1728)³, −(j − 1728)⁵⟩` with `Δ = j²(j − 1728)⁹`; all coefficients are in
  `ℚ[j]`, so `E_j` has good reduction at every place of `ℚ(j)` other than `j = 0, 1728, ∞`.
  (The docstring of `LeafModCurves.Ej` in `ModCurves/Defs.lean` describes an older model
  `y² + xy = x³ − 36/(j−1728)x − 1/(j−1728)`; the definition itself is Mathlib's.)
- FINDING (VERIFIED, read): Mathlib has no multiplication-by-`n` formula for division polynomials and no
  structure theorem for `E[N]`; so the degree bound `[K_N : ℚ(j)] ≤ N²` is reduced to leaf T1.
- 23:20 `finrank_fieldX1_le` (TorsionStructure ⇒ [ℚ(j)(x(P)) : ℚ(j)] ≤ N² for N•P = 0): compiles. VERIFIED (compiled).
- 23:12 `x1ModelExists_of_leaves : TorsionStructure → CurveOfFunctionFieldQ → X1ConstantField →
  X1RationalCusp → X1ModelExists`: compiles. VERIFIED (compiled).
- 23:20 `belyiX1_of_leaves : TorsionStructure → GoodReductionUnramified → BelyiX1`: compiles
  (helpers `scaleEquiv` (T ↦ T/1728 as ℚ[T]-automorphism), `scale_not_dvd`, `transcendental_X_div`).
  VERIFIED (compiled).
- `#print axioms` for `belyiX1_of_leaves`, `x1ModelExists_of_leaves`, `finrank_fieldX1_le`:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
