# kolyv-weil: results log

- **VERIFIED (Git):** started at `a04588b4f`, fork PR #90's head. The refreshed
  `origin/main` (`b0be9b78e` at start) lacks the `PoleS12` modules; PR #90's
  squash is not in that snapshot. No prior task log existed.
- **VERIFIED (source):** `lem:forward-rank`, tex L1086–1109, uses BCDT Theorem A
  at L1092 and Kolyvagin Theorem 1 at L1093. `sec:rc` L1779–1786 spells out the
  associated conductor-level modularity. The prior AI reading pinned in
  `PoleS12/Leaves.lean` gives BCDT Introduction (6), p. 3, and Kolyvagin's
  weak Weil hypothesis on p. 3 preceding Theorem 1 on p. 4. The literal
  “CST Thm 1.1” in the task's quoted ruling is not the citation at L1092;
  the task's detailed instructions match the manuscript (BCDT).
- **VERIFIED (source):** the old `hB`/`hK` pair feeds
  `PoleS12.kolyvaginRankOne_of_printed` through
  `poleCompleteness_of_restrictedConverseGenuine_final` and its `_mw`
  helper. Only `PoleRC.KolyvaginRankOne` is consumed. Original leaf bodies
  and `IsModular` are copied verbatim in `Original.lean`.
- **VERIFIED (source):** general `ModularCurve.modularFunctionField N` is in
  the vendored Anthropic FLT `Definitions/Def_ModularCurve_X0.lean` L259–260.
  `TYZGenus/X0.lean` works at level 32 and `X0RatStructure`/`X0ModuliGalois`
  are Props about values at points, not a rational function field or scheme.
  General local Artin conductors and actual elliptic Tate actions are
  available in `HDecomp/Conductor/LadicCond.lean` and vendored Tau Ceti's
  `AlgebraicGeometry/EllipticCurve/TateModule/Galois.lean`, respectively.
- **VERIFIED (Lean):** `Parametrization.lean` compiled. It reuses the rational
  (X₀(N)) function field, and encodes the nonconstant map as a ℚ-algebra map
  from the elliptic function field. `IsConductor` equates the factorization of
  the positive level with the Artin conductor of the actual rational Tate
  action at each prime. `IsConductor.unique` proves uniqueness of such a level.
- **VERIFIED (tool):** stock `autofold.py … --dry-run` rejects `hK` with
  `not a field of the current bundles: ['hK']`. It only folds H bundle fields.
  `autofold.json` records the exact `hK` proof and the manual consumer
  substitution that drops both old top-level binders.
