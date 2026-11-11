# cr3-inf report

## Result
All steps are done. `lake build ZInQKernel` succeeds. `lake env lean scripts/print_axioms.lean` shows only
`[propext, Classical.choice, Quot.sound]` for all 59 entries, including the 9 new ones. There is no sorry.

New file: `ZInQKernel/RouteK/RankInf.lean`. It is imported from `ZInQKernel.lean`, and 9 entries were added to
`scripts/print_axioms.lean`.

### Definitions and lemmas (namespace `ZInQ.RouteK.Rank`)
- `InfinitelyManyPoints d := Set.Infinite {p : ℚ × ℚ | p.2 ^ 2 = p.1 ^ 3 - (d : ℚ) ^ 2 * p.1}`.
- `infPts_nonsingular`: an affine solution is a nonsingular point of `shortCurve (-(d:ℚ)^2)`, because Δ ≠ 0 when d ≠ 0.
- `infPtsMap`, `infPtsMap_bijective`: `Option {solutions}` maps bijectively onto the point type (none ↦ 0).
- `infinitelyManyPoints_iff_infinite_points`: `InfinitelyManyPoints d` holds iff the point type is `Infinite` (d ≠ 0).
- `exists_infinite_order_iff_infinitelyManyPoints (hd : d ≠ 0)`: C_d(ℚ) has a point of infinite order iff `InfinitelyManyPoints d`.
  - (→) `injective_nsmul_iff_not_isOfFinAddOrder`: the multiples of a point of infinite order are pairwise distinct.
  - (←) `fg_points` together with `AddCommGroup.finite_of_fg_isAddTorsion` (Mathlib): a finitely generated torsion group is finite.
- `CertifiedRankInf`, `CertifiedRankTYZInf`, `CertifiedRankTYZClInf`, `CertifiedRankDLInf`: the four Rk hypotheses with the
  conclusion `InfinitelyManyPoints` (for DL, at `D.d₁` and `D.d₁ * θ.natAbs`).
- Equivalences: `certifiedRankInf_iff_certifiedRankRk`, `certifiedRankTYZInf_iff_certifiedRankTYZRk`,
  `certifiedRankTYZClInf_iff_certifiedRankTYZClRk`, `certifiedRankDLInf_iff_certifiedRankDLRk`.
  - d ≠ 0 comes from d % 8 = 5.
  - For DL it comes from `D.d₁_mod hI` and `(slots_d₂_facts D hI).1`; the slot inputs `hI` are in scope under the binder.

### Main-theorem variants (namespace `ZInQ`)
`exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank{,TYZ,TYZCl,DL}Inf`. Each is one line
through the matching Rk variant.

## Docstrings
- The Inf forms have the same strength as the Rk forms and rest on the same literature. They differ only in that the
  trusted statement mentions no group law.
- "Infinitely many rational points on y² = x³ − d²x" is the classical statement "d is a congruent number" (for squarefree d).
- CertifiedRankDLInf still depends on the internal definitions `Inputs` and `Slots`.

## Problems / suggestions
None blocking. A possible follow-up: point the trust documentation (KERNEL_PLAN.md and the docs) at the Inf forms as the
group-law-free audit target.
