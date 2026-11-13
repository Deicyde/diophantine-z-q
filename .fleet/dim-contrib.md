# dim-contrib (2026-11-13)

**Result.** curve-infra's and infra-smooth-dim's dimension theory is now 11 modules under
`ZInQKernel/Contrib/Dim/`, in namespace `ZInQ.Contrib.Dim`. Each module builds with `lake build`,
with no sorry and no `set_option`. All 26 main theorems use only
`[propext, Classical.choice, Quot.sound]`. The full report is `docs/research/dim-contrib.md`.

- **Algebra.** For a domain `R` of finite type over a field `K`: `dim R = trdeg_K R = trdeg_K Frac R`.
- **Schemes.** For `X` integral and locally of finite type over `K`: `dim X = trdeg_K K(X)`.
- **Smooth schemes.** At every closed point of a scheme smooth of relative dimension `n` over
  `K`, the local ring is regular of dimension `n`. A nonempty such scheme has `dim X = n`.
  Integrated with the above, `trdeg_K K(X) = n`.
- **Integral morphisms.** An integral morphism does not raise dimension, and a surjective
  integral morphism preserves it.
- **Kernel forms.** curve-infra's 8 named Props are carried over, including the forms over the
  kernel's `ffAlgebra`. A script checked that their texts match curve-infra's up to one rename.
- **Kernel Props closed.** `HodgeLattice.lean` closes the kernel's `RegularAtOrigin`,
  `DimAtOrigin`, `DimBaseChange` and `TangentDimAtOrigin`. With them it proves
  **`ZInQ.Contrib.Dim.hodgeLatticeTheorem : ZInQ.DefFaltings.HodgeLatticeTheorem`, with no
  hypotheses**.

**Statement check.** No conclusion is weaker than its docstring claims, and nothing is vacuous.
The check found hypotheses stronger than needed; the adopted modules fix them:
- an unused hypothesis `hU` in infra-smooth-dim's chart lemma;
- `trdeg = 1` where `≤ 1` suffices (AlgDep);
- `IrreducibleSpace` where `Nonempty` suffices (`dim X = n`);
- `IsFinite` where `IsIntegralHom` suffices;
- a same-universe restriction in Noether normalization, now removed;
- a misleading name, `trdeg_eq_of_isLocalization`.

**Check file.** `scratch/dim-contrib/Check.lean` is contrib-check plus 3 imports and 26
`#print axioms` lines. It compiles, and all 39 axiom lines are standard.

**Remains.**
- `ZInQKernel.lean` does not import the new modules; the integrator decides whether it should.
- infra-smooth-dim's curve-facts closures (SmoothStalkDimOne, C1a, C1) wait for curve-facts to be
  integrated. They would be short modules on top of `Contrib/Dim/SmoothStalk`.
- No human has reviewed this work.
