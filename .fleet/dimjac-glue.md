# dimjac-glue (fleet summary)

**Result: `ModularSplit.DimJac.H0DifferentialsEqHolo` is proved in Lean, with no hypotheses, and so is the row
`ZInQ.Contrib.CurvesG.DimJacobianEqGenus`.** There is no literature leaf and no open glue.

- `scratch/dimjac-glue/DimJacGlue.lean` (about 680 lines, no sorry) compiles with `lake env lean` in about 10 s,
  once the CloudW07 oleans are built (I copied them from the modular-split worktree).
  `#print axioms` for `ModularSplit.DimJac.h0DifferentialsEqHolo` and `ModularSplit.DimJac.dimJacobianEqGenus`
  gives `[propext, Classical.choice, Quot.sound]`. The statement is a verbatim copy, checked against
  modular-split's file with diff.
- The proof uses Mathlib (Kähler differentials, the valuative criterion, Jacobson spaces, the DVR TFAE, sheaf
  gluing), the vendored Jacobian library (`kaehlerSectionsEquiv`, `H.zeroLinearEquiv`) and the kernel's
  `Contrib.Dim` cotangent dimension. The steps, each a compiled lemma:
  1. `Φ_U : Γ(U, Ω) → Ω_F` on affine opens, injective because `Ω_A` is projective.
  2. These glue to a global `Φ`, injective by sheaf locality.
  3. The image lies in `holoDiff`, since every place has a center (valuative criterion).
  4. The image contains `holoDiff`: stalks at closed points are DVRs, an ideal argument on each affine, then
     gluing.
  5. `H⁰ = Γ`, and ℚ-linearity is automatic.
- Report: `docs/research/dimjac-glue.md`. Log: `scratch/dimjac-glue/log.md`.
- Remaining: none for this row. To integrate, copy the file into `ZInQKernel/Contrib/` and fill the bundle field
  `dimJacobianEqGenus` with `ModularSplit.DimJac.dimJacobianEqGenus`.
