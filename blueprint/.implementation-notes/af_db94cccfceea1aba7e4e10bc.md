# Implementation note: Multiples of the generator approach the identity at both real places

- Lean name: `ZInQ.Assembly.exists_multiple_large`.
- Draft:
  ```lean
  theorem exists_multiple_large (M : ℝ) : ∃ k : ℕ, 1 ≤ k ∧ ∃ x y h,
      (k : ℤ) • genP0 = .some x y h ∧ M < sigmaPlus x ∧ M < sigmaMinus x
  ```
- Base change of points along `σ : K0 →+* ℝ`: use `WeierstrassCurve.Affine.Point.map`
  (Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:822) with `S = F = K0`, `K = ℝ`
  and the local instance `σ.toAlgebra`, `f = Algebra.ofId K0 ℝ`; identify
  `genCurve.baseChange ℝ` with `realCurve (σ genD)`.
- Mathlib: as in the real-subtraction note; `StrictMono`.
- FINITE COMPUTATION: no (`σ±(d) ≠ 0` is `norm_num` with `Real.sqrt`). Difficulty: medium (~150 lines).

Shared conventions (assembly notes): namespace `ZInQ.Assembly`, files under
`ZInQKernel/Assembly/`. `RelT τ a` abbreviates `ZInQ.Syntax.Rel τ.poly τ.parameterCount
τ.witnessCount a` (syntax note for template semantics); codes are `ZInQ.iota : ℤ → Fin 5 → ℚ`
and `ZInQ.pointCode` (point-codes note); `genP0 : genCurve.toAffine.Point`. The hypothesis
triple `(hH : SixContactEstimate) (hPC : PoleCompleteness) (h22 : FixedPrimePattern)` is
written `hyps`; Mordell–Weil is the theorem `ZInQ.mordellWeilE`, not a hypothesis (drafts below
that still take `hMW : MordellWeilE` instantiate it with that theorem). The constants `A0`, `Bnk n κ`, `heightD` and
every power `4 ^ Bnk n κ` must stay symbolic: mark them `@[irreducible]`/`noncomputable` and
never use `decide`, `norm_num` evaluation or `#eval` on them.
- Status: `ZInQ.Assembly.exists_multiple_large` (`ZInQKernel/Assembly/Real/Accumulation.lean`) proves the
  article with `¬ IsOfFinAddOrder genP0` as an explicit hypothesis; `exists_nsmul_near_zero` is the
  hypothesis-free half. Once `ZInQ.genP0_not_isOfFinAddOrder` is on main, record the unconditional
  corollary here as the Lean name.
