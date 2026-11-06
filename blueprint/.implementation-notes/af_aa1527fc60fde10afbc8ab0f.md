# Implementation note: Quadratic-field pairs and point-code formulas

- Lean names: `ZInQ.Syntax.Pair` (= `Poly × Poly` inside `Prog`), `ZInQ.Syntax.Prog.fmul`,
  `fadd`, `fneg`, `fconj`, `fnorm`, `feq`, `fnonzero`, `fdiv`, `ZInQ.Syntax.Prog.isO`,
  `finite`, `peq`, `curve`, `neg`, `gen` (generator point with rational constants),
  `zGadget`, `inverseXGadget`.
- Draft: Lean transcriptions of `EllipticCore` methods in construction/rational-elliptic-core.js,
  each a `Prog` action returning node handles/formulas, e.g.
  ```lean
  def fmul (u v : Pair) : Prog Pair := do
    let a ← add (← mul u.1 v.1) (← scale 2 (← mul u.2 v.2))
    let b ← add (← mul u.1 v.2) (← mul u.2 v.1)
    pure (a, b)
  ```
  Keep the JS evaluation order exactly (argument order of `add`, `mul`, `scale`), since it
  fixes node and variable order for the cross-check.
- Mathlib: none (syntax). For semantics see the pair-arithmetic note.
- Upstream reuse: none.
- Finite computation: no.
- Difficulty: low-medium (~150 lines of transcription).

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
