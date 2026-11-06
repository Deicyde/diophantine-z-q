# Implementation note: Witness scope of constructed templates and recipes

- Lean names: `ZInQ.Syntax.Template.WellScoped`, `ZInQ.Syntax.Prog.toTemplate_wellScoped`,
  `ZInQ.Syntax.translate_wellScoped`, `ZInQ.Syntax.Recipe.comp_wellScoped`,
  `ZInQ.Syntax.Template.vars_denote_lt`.
- Draft:
  ```lean
  structure Template.WellScoped (t : Template) : Prop where
    blocks_disjoint : t.witnessBlocks.Pairwise (fun b b' => Disjoint (Ico b.1 (b.1+b.2.1)) (Ico b'.1 (b'.1+b'.2.1)))
    blocks_in_range : ∀ b ∈ t.witnessBlocks, t.parameterCount ≤ b.1 ∧ b.1 + b.2.1 ≤ t.variableCount
    no_escape : ∀ i ∈ t.varNodeIndices, ∀ b ∈ t.witnessBlocks, i ∉ Ico b.1 (b.1 + b.2.1)
  theorem Template.vars_denote_lt (h : ...) : ∀ i ∈ (t.denote lib).vars, i < t.variableCount
  ```
- Proof: allocation-monotonicity lemma for `Prog` and for `translate`; `MvPolynomial.vars_bind₁`
  for the call case of `vars_denote_lt`.
- Mathlib: `MvPolynomial.vars_bind₁`, `MvPolynomial.vars_add_subset`, `MvPolynomial.vars_mul`,
  `Finset.Ico`, `Disjoint`.
- Upstream reuse: none.
- Finite computation: no (generic). Fallback for any template whose program resists the
  generic proof: `decide` on the concrete `Template` value (at most 2,682 nodes, cheap).
- Difficulty: medium (~250 lines).

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
