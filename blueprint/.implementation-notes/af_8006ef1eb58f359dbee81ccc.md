# Implementation note: Deep multiples of the generator

- Lean names: `ZInQ.Assembly.exists_smul_mem_Ek`, `ZInQ.Assembly.exists_common_smul_mem_Ek`.
- Draft:
  ```lean
  theorem exists_common_smul_mem_Ek (Π : Finset Zs) (hΠ : ∀ π ∈ Π, Prime π) (N : ℕ) (hN : 1 ≤ N) :
      ∃ κ : ℕ, 1 ≤ κ ∧ ∀ π ∈ Π, ∀ j : ℤ, (j * κ) • genP0 ∈ Ek π N
  ```
- Mathlib: `AddSubgroup.zsmul_mem`, `Finset.prod_pos`, `Finset.dvd_prod_of_mem`.
- FINITE COMPUTATION: no (uses the bad-place check). Difficulty: easy-medium (~120 lines).

Shared conventions (assembly notes): namespace `ZInQ.Assembly`, files under
`ZInQKernel/Assembly/`. `RelT τ a` abbreviates `ZInQ.Syntax.Rel τ.poly τ.parameterCount
τ.witnessCount a` (syntax note for template semantics); codes are `ZInQ.iota : ℤ → Fin 5 → ℚ`
and `ZInQ.pointCode` (point-codes note); `genP0 : genCurve.toAffine.Point`. The hypothesis
triple `(hH : SixContactEstimate) (hPC : PoleCompleteness) (h22 : FixedPrimePattern)` is
written `hyps`; Mordell–Weil is the theorem `ZInQ.mordellWeilE`, not a hypothesis (drafts below
that still take `hMW : MordellWeilE` instantiate it with that theorem). The constants `A0`, `Bnk n κ`, `heightD` and
every power `4 ^ Bnk n κ` must stay symbolic: mark them `@[irreducible]`/`noncomputable` and
never use `decide`, `norm_num` evaluation or `#eval` on them.
