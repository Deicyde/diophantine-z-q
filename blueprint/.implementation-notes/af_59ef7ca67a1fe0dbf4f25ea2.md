# Implementation note: Variable, degree and coefficient bounds

- Lean name: `ZInQ.Size.Pstar_size`.
- Draft:
  ```lean
  theorem Pstar_size (hCAT : CatalogueBound) :
      Syntax.Pstar.totalDegree < hyperoperation 4 2 7 ∧
      ∀ m : Fin 292890231905 →₀ ℕ, (Syntax.Pstar.coeff m).natAbs < hyperoperation 4 2 8
  ```
  This is exactly the first two conjuncts of `ZInQ.FrozenTarget` (ZInQKernel/Target.lean) for the
  witness `Syntax.Pstar : MvPolynomial (Fin 292890231905) ℤ`; the variable count is built into the
  type (from the witness accounting, which justifies `killCompl` losing nothing).
- Proof: `Pstar_degree_coeff`, `literal_cutoff` (third conjunct), `tower_bounds`, `lt_of_le_of_lt`.
- Mathlib: `hyperoperation`.
- Finite computation: no.
- Upstream reuse: `ZInQ.NumericalTowerBounds` via `tower_bounds`.
- Difficulty: trivial (assembly).

Shared design (majorant notes): `Maj B h P : Prop := if h = 0 then P.totalDegree ≤ 1 ∧ l1 P ≤ 1
else P.totalDegree ≤ B ^ (8 * h) ∧ l1 P ≤ 2 ^ B ^ (8 * h)` (helper def in `ZInQKernel/Size/Majorant.lean`).
Heights are computed on the syntax chapter's node lists (`ZInQ.Syntax.Template.nodes`, produced by
`Prog.dag`), so they depend only on syntax, never on the values of fixed expressions.
