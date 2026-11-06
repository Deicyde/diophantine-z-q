# Implementation note: Syntax heights

- Lean names: `ZInQ.Size.nodeHeights : List ℕ → Template → List ℕ`, `ZInQ.Size.templateHeight`,
  `ZInQ.Size.libraryHeights : List Template → List ℕ`, `ZInQ.Size.recipeHeight`,
  `ZInQ.Size.Maj`.
- Draft:
  ```lean
  def nodeHeight (lib : List ℕ) (hs : List ℕ) : Syntax.Node → ℕ
    | .var _ => 0 | .const _ => 1 | .fixed _ => 1
    | .add j k | .mul j k => 1 + max (hs.getD j 0) (hs.getD k 0)
    | .psi _ a _ => 1 + (List.ofFn fun i => hs.getD (a i) 0).foldl max 0
    | .guard _ a => 1 + (List.ofFn fun i => hs.getD (a i) 0).foldl max 0
    | .call t args _ => 1 + lib.getD t 0 + (args.map fun j => hs.getD j 0).foldl max 0
  def templateHeight (lib : List ℕ) (τ : Syntax.Template) : ℕ :=
    (τ.nodes.foldl (fun hs n => hs ++ [nodeHeight lib hs n]) []).getD τ.root 0
  def libraryHeights (L : List Syntax.Template) : List ℕ :=
    L.foldl (fun lib τ => lib ++ [templateHeight lib τ]) []
  def recipeHeight : Syntax.Recipe → ℕ  -- model: max 4 (callee max + 3) + 2; comp: max + 2 / + 1
  def Maj (B h : ℕ) (P : MvPolynomial ℕ ℤ) : Prop := ...
  ```
  Computable on purpose (used by the finite check `template_heights`). Use `Array` in the
  compiled path if convenient; proofs only need the `List` version.
- Mathlib: none.
- Finite computation: no (definition).
- Upstream reuse: none; mirrors construction/bound-ordinary-integer-polynomial.py.
- Difficulty: low.

Shared design (majorant notes): `Maj B h P : Prop := if h = 0 then P.totalDegree ≤ 1 ∧ l1 P ≤ 1
else P.totalDegree ≤ B ^ (8 * h) ∧ l1 P ≤ 2 ^ B ^ (8 * h)` (helper def in `ZInQKernel/Size/Majorant.lean`).
Heights are computed on the syntax chapter's node lists (`ZInQ.Syntax.Template.nodes`, produced by
`Prog.dag`), so they depend only on syntax, never on the values of fixed expressions.
