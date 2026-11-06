# Implementation note: The exact ordinary-value relation

- Lean names: `ZInQ.Assembly.value_rel_iff`, `ZInQ.Assembly.exists_value_rel_iff`.
- Draft:
  ```lean
  theorem value_rel_iff (hyps) (N : Fin 5 → ℚ) (t : ℚ) :
      RelT Syntax.valueRecipe (Fin.append N ![t]) ↔ ∃ n : ℤ, N = iota n ∧ t = n
  theorem exists_value_rel_iff (hyps) (t : ℚ) :
      (∃ N, RelT Syntax.valueRecipe (Fin.append N ![t])) ↔ ∃ z : ℤ, (z : ℚ) = t
  ```
  The right side of the second matches `ZInQ.FrozenTarget` and the syntax lemma
  `ZInQ.Syntax.Pstar_zero_projection` (`Rel valueRecipe.poly 6 292890231899 (Fin.append N ![q])`).
- FINITE COMPUTATION: no. Difficulty: medium (~150 lines).

Shared conventions (assembly notes): namespace `ZInQ.Assembly`, files under
`ZInQKernel/Assembly/`. `RelT τ a` abbreviates `ZInQ.Syntax.Rel τ.poly τ.parameterCount
τ.witnessCount a` (syntax note for template semantics); codes are `ZInQ.iota : ℤ → Fin 5 → ℚ`
and `ZInQ.pointCode` (point-codes note); `genP0 : genCurve.toAffine.Point`. The hypothesis
quadruple `(hH : SixContactEstimate) (hPC : PoleCompleteness) (hMW : MordellWeilE)
(h22 : FixedPrimePattern)` is written `hyps`. The constants `A0`, `Bnk n κ`, `heightD` and
every power `4 ^ Bnk n κ` must stay symbolic: mark them `@[irreducible]`/`noncomputable` and
never use `decide`, `norm_num` evaluation or `#eval` on them.
