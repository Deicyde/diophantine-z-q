# wk-cr3 log

## Step 1 (sources read)
- Read: nt-tyz.md, cr3-trust.md, cr3-map-literature.md, slot-k.md §1, pc-audit §4.5, tyz-5b end,
  Hypotheses/CertifiedRank.lean, RouteK/Rank/Statements.lean, RouteK/RankDL.lean.
- Mathlib v4.35.0 has `WeierstrassCurve.LSeries` (AlgebraicGeometry/EllipticCurve/LFunction.lean:
  Euler product over primes of 𝓞 K, local factor from the minimal model: good 1 − a T + q T²,
  split/nonsplit multiplicative 1 ∓ T, additive 1), `analyticOrderAt` (Analysis/Analytic/Order.lean:49,
  `analyticOrderAt_ne_zero` :144), identity theorem `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
- Fork: `T5bCl`, `gCl` (Rank5b/Sec3/RedeiStatement.lean:49,55), `shortCurve_isElliptic`,
  `CertifiedRankTYZClRk` (Rank/Statements.lean:72). No point counting / L-function in the fork.
- Elementary check: every d in CR3's domain (d ≡ 5 (8), a | d, |a| ≡ 7 (8)) has ≥ 2 primes ≢ 1 (8)
  (a has a prime ≡ 3,7; d/|a| ≡ 3 (8) has a prime ≡ 3,7). So criteria with "all primes ≡ 1 (8)
  but one" (Tian 2014) never apply, for any slot choice.
