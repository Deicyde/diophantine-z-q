# Implementation note: Formulas and their polynomial compilation

- Lean names: `ZInQ.Syntax.Formula`, `ZInQ.Syntax.Formula.compile`,
  `ZInQ.Syntax.Formula.Holds`, `ZInQ.Syntax.Prog`, `ZInQ.Syntax.Prog.toTemplate`,
  gadgets `ZInQ.Syntax.Prog.nz`, `ZInQ.Syntax.Prog.pos`, `ZInQ.Syntax.Prog.rational`.
- Draft:
  ```lean
  inductive Formula
    | eq (a b : MvPolynomial ℕ ℤ) | atom (f : MvPolynomial ℕ ℤ)
    | and (fs : List Formula) | or (fs : List Formula)
  noncomputable def Formula.compile : Formula → MvPolynomial ℕ ℤ
    | .eq a b => a - b | .atom f => f
    | .and fs => (fs.map fun φ => φ.compile ^ 2).sum
    | .or fs => (fs.map Formula.compile).prod
  def Formula.Holds (x : ℕ → ℚ) : Formula → Prop
  ```
  (nested-inductive recursion on `List Formula`: use `attach` or a mutual helper.)
  `Prog` is a free monad: `| pure | fresh (k : ℕ → Prog) | call (t : TemplateRef) (args) (k) |
  rational (u q : ℤ) (k) | node (op) (k)`; `Prog.toTemplate name p` runs it from counter `p`
  and appends the global equations: polynomial `compile (.and (eqs ++ [φ]))`.
- Mathlib: none beyond `MvPolynomial` ring operations.
- Upstream reuse: `ZInQ.EquationCompression.compile` has the binary version of the same
  compilation (`conj` ↦ sum of two squares); ours is n-ary and must be n-ary to match the
  specification's polynomial exactly (a binary nesting changes the polynomial).
- Finite computation: no.
- Difficulty: medium (~250 lines: formula type, free monad, three interpreters).

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
