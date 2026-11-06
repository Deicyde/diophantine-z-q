# Implementation note: The exceptional-values template

- Lean names: `ZInQ.Syntax.valueExceptionsProg` (construction program), `ZInQ.Syntax.valueExceptionsTemplate`
  (the node-list template, `Prog.toTemplate`), `ZInQ.Syntax.valueExceptionsFormula` (readable formula
  for the semantics chapters).
- Draft: a line-by-line transcription of ``value.exceptions` in addVariableShiftTemplates with fixedMultiple (construction/rational-model-assembly.js)` as a `Prog` action, with
  `valueExceptionsTemplate.parameterCount = 6` and witness count `406`; for example
  `def valueExceptionsTemplate : Template := valueExceptionsProg.toTemplate "value.exceptions" 6`.
  Keep the JS evaluation order of every builder call (it fixes variable indices and node
  order for the cross-check).
- Mathlib: none (syntax only).
- Upstream reuse: none.
- Finite computation: no (its counts are covered by the template witness-count check).
- Difficulty: low.
- The branches are built before the `member` call, so the member block is last (405-411) although `member` is the first conjunct.

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
