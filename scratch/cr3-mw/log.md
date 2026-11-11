# cr3-mw log

## Plan (2026-11-10)
- Kummer.lean's `phi` is a function, not a hom. Finite index needs φ̂ additive
  ([E:2E] ≤ #im α · #im α' uses φ̂(Q1)-φ̂(Q2)=φ̂(Q1-Q2)). So: prove `phi` additive (RankMW/PhiAdd.lean).
- RankMW/Torsion.lean: twoTorsion_card.
- RankMW/Index.lean: generic finiteness of [E:2E] from finite Kummer images.
- RankMW/Image.lean: over ℚ, Kummer image ⊆ classes of signed divisors (p-adic valuations).
- RankMW.lean: fg_points via AddCommGroup.fg_of_descent' (scratch test T1 OK).
