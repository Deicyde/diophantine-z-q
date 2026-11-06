# Implementation note: Natural constructions and their macros

- Lean names: `ZInQ.Compiler.Formula.NatProg` (or the syntax chapter's `ZInQ.Syntax.Prog`
  specialized), macros `lt`, `divides`, `congruent`, `odd`, `alpha`, `power`, `binomial`,
  `orthogonal`, `mask`, `bitAnd`, and the mode flag `PowerMode := flat | hierarchical`.
- Draft:
  ```lean
  inductive Formula | eq (a b : MvPolynomial ℕ ℤ) | atom (f : MvPolynomial ℕ ℤ)
    | and (fs : List Formula) | or (fs : List Formula)        -- syntax chapter's type
  structure BState where (next : ℕ) (explicit : List (ℕ × VarKind)) (blocks : List ℕ)
  abbrev NatM := StateM BState
  def fresh : NatM (MvPolynomial ℕ ℤ)
  def lt (a b : MvPolynomial ℕ ℤ) : NatM Formula := do
    let d ← fresh; pure (.eq b (a + 1 + d))
  def alpha (X b N : MvPolynomial ℕ ℤ) : NatM Formula := do
    let r ← fresh; let s ← fresh; ... -- order r s t u v w x y
    pure (.and [← lt 3 b, .eq (1 + b*u*t) (u^2 + t^2), ...])   -- order of the JS builder
  def power (mode : PowerMode) (P Q R) : NatM Formula
  ```
  Evaluate the list arguments with `do`-notation left to right so that witness allocation
  follows the JS argument evaluation order (this only matters for the byte-level
  cross-check, not for semantics).
- For node lists use the syntax chapter's `dag` interpreter (hash-consing keyed by node
  descriptor, formulas also hash-consed); for semantics use `Formula` directly.
- Mathlib: `MvPolynomial.X`, `StateM`.
- Upstream reuse: none (the upstream `BitwiseMacros`/`BinomialDigit` predicates are the
  semantic targets, not constructions).
- FINITE COMPUTATION: no. Difficulty: medium (≈150 lines, mostly transcription of
  `construction/integer-diophantine-compiler.js`).
