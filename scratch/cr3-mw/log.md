# cr3-mw log

## Plan (2026-11-10)
- Kummer.lean's `phi` is a function, not a hom. Finite index needs φ̂ additive
  ([E:2E] ≤ #im α · #im α' uses φ̂(Q1)-φ̂(Q2)=φ̂(Q1-Q2)). So: prove `phi` additive (RankMW/PhiAdd.lean).
- RankMW/Torsion.lean: twoTorsion_card.
- RankMW/Index.lean: generic finiteness of [E:2E] from finite Kummer images.
- RankMW/Image.lean: over ℚ, Kummer image ⊆ classes of signed divisors (p-adic valuations).
- RankMW.lean: fg_points via AddCommGroup.fg_of_descent' (scratch test T1 OK).

## Results (2026-11-10)
- RankMW/PhiAdd.lean: `mwPhi_add` (phi additive), `mwPhiHom`; helpers mwPhi_line / mwPhi_sum_sq /
  mwPhi_tangent (pure algebra; linear_combination coefficients from sympy division),
  mwAdd_of_line / mwDouble_of_line, mwPhi_neg, mwAdd_tZero_some, mwPhi_add_tZero,
  mwPhi_add_generic, mwPhi_double, mwPhi_double'.
- RankMW/Index.lean: `mwFiniteIndex_two_of_kummer` (generic field), mwPhiHat, mwKer_kummer_eq_range.
- RankMW/Image.lean: `mwKummer_range_finite` (c : ℤ ≠ 0), mwEven_padicValRat_x, mwSqc_eq_divisor.
- RankMW/Torsion.lean: `twoTorsion_card`, `mwTwoTorsion_iff`, `mwTwoTorsionPt`.
- RankMW.lean: `finiteIndex_two_points`, `fg_points`. Axioms: propext, Classical.choice, Quot.sound.
- lake build ZInQKernel.RouteK.RankMW OK.
