# Implementation note: The inverse abscissa template

- Lean names: `ZInQ.Syntax.rawInverseXProg` (construction program), `ZInQ.Syntax.rawInverseXTemplate`
  (the node-list template, `Prog.toTemplate`), `ZInQ.Syntax.rawInverseXFormula` (readable formula
  for the semantics chapters).
- Draft: a line-by-line transcription of `EllipticCore.inverseX via addCore` as a `Prog` action, with
  `rawInverseXTemplate.parameterCount = 7` and witness count `0`; for example
  `def rawInverseXTemplate : Template := rawInverseXProg.toTemplate "raw_inverse_x" 7`.
  Keep the JS evaluation order of every builder call (it fixes variable indices and node
  order for the cross-check).
- Mathlib: none (syntax only).
- Upstream reuse: none.
- Finite computation: no (its counts are covered by the template witness-count check).
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
