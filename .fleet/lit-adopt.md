# lit-adopt: the reduction drafts adopted as hypothesis files

## Files and declarations
- `ZInQKernel/Hypotheses/CR3Literature.lean` (namespace `ZInQ.Literature`, from
  `scratch/wk-cr3/Literature.lean`): `IsLContinuation`, `IsLContinuation.eq`, `GrossZagier`
  (renamed from `GrossZagierKolyvagin`), `RootNumberVanishing`, `TYZRow5b`,
  `analyticOrder_eq_one`, `certifiedRankTYZClRk_of_literature`, `Admissible5aNat`, `T5aCl`,
  `HeckeContinuation`, `TYZThm35ReadingA`, `tyzRow5b_of_readingA`, `completedL`,
  `FunctionalEquation5`, `rootNumberVanishing_of_functionalEquation`, two small `ℕ∞` lemmas.
  `FunctionalEquation5` now holds only for `0 < Re s < 2`; its docstring says why (Mathlib's
  `Complex.Gamma` is 0 at `0, −1, …`, so for every `s` the identity would force `L(C_d, 2) = 0`).
  `GrossZagier`'s docstring names Bump–Friedberg–Hoffstein 1990 (through Waldspurger) or
  Friedberg–Hoffstein 1995 as the source for `L(E^K, 1) ≠ 0`, drops Murty–Murty, and keeps the
  Kolyvagin remark. The module docstring has a Trust section for each Prop and the L-series.
- `ZInQKernel/Hypotheses/JHeight.lean` (namespace `ZInQ.JHeight`, from
  `scratch/wk-h/BackToU.lean`): `Fh`, `Gh`, `Jmap`, `cert_x`, `cert_y`, `G_ne_zero`, `C0`,
  `dvd_C0`, `abs_monomial_le`, `lower_bound`, `twelve_mul_ratHeight_le`, `heightX`,
  `JHeightBound` (docstring as specified), `heightH6_eq`, and
  `sixContactMin_of_jHeightBound : JHeightBound Mult.S_mul → SixContactMin`.
- `ZInQKernel/MainLiterature.lean` (namespace `ZInQ`) has three variants, each proved from
  `..._of_sixContactMin_certifiedRankTYZClRk`:
  `..._of_sixContactMin_tyzRow5b_functionalEquation5_grossZagier`,
  `..._of_jHeightBound_certifiedRankTYZClRk`, and
  `..._of_jHeightBound_tyzRow5b_functionalEquation5_grossZagier`.
- The three imports were added to `ZInQKernel.lean`, and eight `#print axioms` lines to
  `scripts/print_axioms.lean`.

## Checks
- `lake build ZInQKernel` succeeds. The new files raise no warnings except Mathlib's
  "module system" import notices.
- `lake env lean scripts/print_axioms.lean` gives 69 entries (61 before, plus 8). Every entry
  shows only `[propext, Classical.choice, Quot.sound]`.
- `scripts/check_target.py`: FrozenTarget matches the frozen statement.
- The new files contain no `sorry`, `axiom`, `native_decide`, `implemented_by` or `extern`.

## Deviations from the drafts beyond the listed changes
- CR3Literature does not import `RouteK.RankVariants`, because only the dropped main theorem
  used it. MainLiterature imports it instead.
- The last step of `IsLContinuation.eq` is split into two `have`s, and three proof lines in
  JHeight are rewrapped. Both changes keep lines within 100 characters; the proofs are
  unchanged.
- `SixContactMinAt` and `contactSupport_pos'` are dropped. Height and HeightMin have no
  general-`S` form of `SixContactMin`, so `sixContactMin_of_jHeightBound` is stated with
  `SixContactMin` directly and uses HeightMin's `contactSupport_pos`. The proof is otherwise
  as drafted.
- JHeight's module docstring is rewritten. It no longer mentions Tier 2 or `Arakelov.lean`,
  which was not adopted.
- In MainLiterature, the third variant is proved from the base theorem directly, not through
  the first variant, as step 3 asks.
- Two lines are longer than 100 characters: the `theorem` lines of the two variants whose
  required names are 109 and 108 characters long.
