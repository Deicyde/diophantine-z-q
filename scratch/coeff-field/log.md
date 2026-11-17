# coeff-field results log

Base: wip/coeff-fix 496c1f75, merged origin/main 0caafe66 (STATUS.md only) → ae975643.

## Survey (VERIFIED, read in the tree)
- Vendored Tau Ceti (ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/) has: finite-dimensionality of
  `CuspForm 𝒢 k` (SturmBound.lean:150 `finiteDimensional_cuspForm_finiteIndex`), the Sturm bound,
  the coefficient formula for `T_n` on `cuspFormCharSpace k χ`
  (HeckeSlash/Nebentypus/CoefficientFormula.lean:115), full eigenforms (Newforms/Eigenform.lean),
  complex conjugation of forms (Conjugate.lean).
- No rational structure anywhere: grep for IsAlgebraic / IsIntegral ℤ / FiniteDimensional ℚ / NumberField
  in Tau Ceti ModularForms: no hits. No Eichler–Shimura, no modular symbols, no q-expansion principle,
  no Galois action Aut(ℂ) on forms. Mathlib 4.35: level-one only (E4, E6 graded ring).
- Conclusion: an outright proof needs a rational structure on `S_k(N, χ)`, which is not in the tree.

## Plan
- Glue (to prove): abstract linear algebra — `V` finite-dim over `K`, coordinate functionals `c_i` with
  zero joint kernel, `W = {v | c_i v ∈ F}` spanning `V` over `K`; then eigenvalues of operators
  preserving `W` at a common eigenvector `f ≠ 0` generate a finite-dim `F`-algebra.
- Leaf: `S_k(N, χ)` is spanned over `ℂ` by forms with coefficients in `ℚ(χ)`.

## Abstract.lean (VERIFIED: compiles, lake env lean, 10 s)
- `CoeffField.finiteDimensional_adjoin_eigenvalues`: V f.d. over K, c : ι → V →ₗ[K] K with zero joint kernel,
  span K {v | ∀ i, c i v ∈ F} = ⊤, f ≠ 0, every μ ∈ s an eigenvalue at f of a K-linear T preserving the
  F-rational vectors ⇒ FiniteDimensional F (Algebra.adjoin F s).

## Spec.lean → contribution (VERIFIED: compiles with lake env lean, 13 s; axioms propext, Classical.choice, Quot.sound)
- `ZInQKernel/Contrib/OneProof/EigenformCoeffFieldFinite.lean` (namespace `CoeffFieldFinite`; copy in scratch).
- `eigenformCoeffFieldFinite_of : CharSpaceRationalSpan → DSCoeffExt.EigenformCoeffFieldFinite`
- `charSpaceRationalSpan_of : Gamma1IntegralSpan → DiamondPreservesIntegral → CharSpaceRationalSpan`
- `eigenformCoeffFieldFinite_of_gamma1`, `dsThm965Weak_of_printed (h1 : DSThm965Printed) hA hB`,
  `dsThm965Weak_of_printed_charSpace h1 hR`.
- Leaves stated in integral form (ℤ coefficients) to match the prints (Shimura 3.52: rational integers;
  𝕋_ℤ preserves S_k(Γ₁(N), ℤ)). Lean pitfall: `group` does not use commutativity; finish with
  `simp only [zpow_neg_one]; rw [mul_comm e, mul_inv_cancel_right]`. Kernel deterministic timeout when
  `map_smul' := fun _ _ => rfl` for ℚ-linear maps between subalgebras of ℂ; `Subtype.ext (by simp)` fixes it.

## Final form (VERIFIED: compiled; lake build of Main + Discharges + contribution OK, 13700 jobs; standard axioms)
- Leaves: `Gamma1IntegralSpan` (ℤ-coefficient span of S_k(Γ₁(N)), k ≥ 2), `DiamondIntegralToRational`
  (⟨d⟩: integral q-expansion ↦ rational q-expansion, k ≥ 2); one-leaf variants `CharSpaceRationalSpan`
  (ℚ(χ)) and `CharSpaceNumberFieldSpan` (some number field; weakest).
- #discharges (scratch/coeff-field/discharges-output.txt): dsThm965Weak by `CoeffFieldFinite.dsThm965Weak_of_printed`
  still assumes [DSThm965Printed, Gamma1IntegralSpan, DiamondIntegralToRational]; also `_charSpace`,
  `_numberField` variants; all standard axioms. 56 open hypotheses, 2991 theorems checked.
- autofold dry run: strict 34/11 on 45 → 36/11 on 47 (strictest same); GLUE unchanged. FoldCheck.lean compiles,
  `sixContactMin_of_open36` standard axioms.
- PARI sanity check not run: ~/pyenv is absent on this host and system python3 has no cypari2.
