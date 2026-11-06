# Implementation note: Witness accounting of the specified polynomial

- Lean names: `ZInQ.Syntax.recipe_counts`, `ZInQ.Syntax.vars_PstarNat_lt`.
- Draft:
  ```lean
  theorem recipe_counts :
      powerValueRecipe.variableCount = 17786718 ∧ precisionRecipe.variableCount = 292889492861 ∧
      closeRecipe.variableCount = 292890196210 ∧ mainRecipe.variableCount = 292890231492 ∧
      valueUnionRecipe.variableCount = 292890231898 ∧ valueRecipe.variableCount = 292890231905 ∧
      integersRecipe.variableCount = 292890231905
  theorem vars_PstarNat_lt : ∀ i ∈ PstarNat.vars, i < 292890231905
  ```
- Proof: the closed-form count lemma for `translate` (translation note) plus the shape
  statistics and `witness_count_arith`; composition counts by `rfl` on the allocation monad;
  `vars_PstarNat_lt` from the witness-scope theorem by induction over the library and
  recipes. Never evaluate the precision record in the kernel; reason about `translate`
  symbolically.
- Mathlib: `MvPolynomial.vars_bind₁`, `MvPolynomial.vars_pow`, `MvPolynomial.vars_add_subset`,
  `MvPolynomial.vars_mul`.
- Upstream reuse: none.
- Finite computation: no (uses the three finite-computation leaves).
- Difficulty: medium (~200 lines).
