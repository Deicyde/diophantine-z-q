# dim-contrib results log

Base 80b032c9 (wip/integrate-w43) + merge origin/wip/curve-infra (0eb4618a).

## Statement check (read against docstrings and sources)
See docs/research/dim-contrib.md §1 for the table. Findings (VERIFIED: read):
- curve-infra `algDepOfTrdegOne`: hypothesis `trdeg = 1` stronger than needed (`trdeg ≤ 1` suffices; same proof).
- infra-smooth-dim `topologicalKrullDim_eq_of_smoothOfRelativeDimension`: `[IrreducibleSpace X]` stronger than needed (`[Nonempty X]` suffices: every closed point has stalk dim n, every point specializes to a closed point).
- infra-smooth-dim `topologicalKrullDim_eq_of_finite_surjective`: `[IsFinite f]` stronger than needed (`[IsIntegralHom f]`).
- curve-infra `trdeg_eq_of_isLocalization`: name/docstring say "localization", hypothesis is `IsFractionRing` (conclusion narrower than the name).
- universe restrictions: `exists_dim_eq_trdeg` needs K, R in one universe; `height_isMaximal_mvPolynomial` and the presentation theorem take `ι σ : Type` (matches Mathlib's `IsStandardSmooth`, which quantifies over `Type`); the named Props are in universe 0.
- No conclusion weaker than its docstring claims; no vacuous hypothesis found.
