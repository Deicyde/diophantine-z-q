# Implementation note: The prescribed fixed constants

- Lean names: `ZInQ.Syntax.FixedConst` (enumeration) and `ZInQ.Syntax.FixedConst.expr`;
  convenience abbreviations `ZInQ.Syntax.Ps`, `W`, `Hcat`, `Hmax`, `Ns`, `M0`, `cstar`, `ell`,
  `F`, `D`, `G0`, `E0`, `R`, `Q`, `Bcm`, `Ccm`, `Aht`, `T` (each `:= (FixedConst.x).val`), and
  `ZInQ.Syntax.integerConstant : Fin 5 → ℤ` (defined from the translation).
- Draft: `P0 := primorial 324` (not the literal), `W := 4 * P0`, the rest exactly as the
  table, e.g. `T := (48 * Aht) ^ 13`. Lemma `T_def : T = (48 * Aht)^13 := rfl` style
  unfolding lemmas for the size chapter.
- Mathlib: `primorial` (Mathlib/NumberTheory/Primorial.lean, read at v4.35.0), `Nat.factorial`.
- Upstream reuse: `ZInQ.ExplicitCutoffBounds.factorialBase`, `ZInQ.ExplicitCutoffBounds.d`,
  `ZInQ.ExplicitCutoffBounds.g0` (lean/ZInQ/ExplicitCutoffBounds.lean) have the same formulas
  as `F`, `D`, `G0`: prove `F = factorialBase`, `D = ExplicitCutoffBounds.d` by `rfl` and reuse
  their bounds. `ZInQ.HeightConstantAlgorithm.heightBody` is the precision computation's
  height constant with `r = max(d, 317, 10^12)`; it differs from `Aht` (whose `R` also has
  `Hmax` and `cstar`), so it is not reused here.
- Finite computation: no. None of these constants is evaluated.
- Difficulty: low.

Shared design (all syntax notes): namespace `ZInQ.Syntax`, files under
`ZInQKernel/Syntax/`. Polynomials are `MvPolynomial ℕ ℤ`; evaluation over `ℚ` is
`MvPolynomial.eval₂ (Int.castRingHom ℚ) x`. Templates are written once as programs of a
small deep-embedded construction language `Prog` (free monad over: fresh variable, fresh
block call, rational constant, node operations, formula connectives) with three
interpreters: `Prog.dag` (hash-consed node list, mirrors the JS builder byte for byte, used
for heights and the cross-check), `Prog.formula` (readable `Formula` term, used for
semantics) and `Prog.count` (allocation counter only, cheap to evaluate in the kernel).
Fixed integer expressions stay symbolic (`FixedExpr` syntax, noncomputable `val`); no proof
ever evaluates `c_*`, `ell`, `T`, `D`, `Q` or the program literal `c_3`.
- Status: `ZInQKernel/Syntax/Constants/Fixed.lean` defines the eighteen named constants (`FixedConst`,
  `FixedConst.expr`, `FixedConst.value`, `ZInQ.Syntax.fixedVal`, the ℕ constants `Ps` … `T` with
  `value_P0` … `value_T`), and `Relations.lean` proves their relations. Not done: `integer_constant_0..4`
  (in particular `c_3`, whose Lean value is the compiler's program literal, bounded in
  compiler/natural/universal/wrapper-code-size.md, not the saved 3,181,317-digit literal). Record the
  article when the integer constants are defined. Downstream code must reason through `Ps_eq` … `T_eq`
  and the `value_*` lemmas: the constants are `irreducible`, because the kernel otherwise tries to
  evaluate them.
