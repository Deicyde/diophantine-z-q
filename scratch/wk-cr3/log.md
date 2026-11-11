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

## Step 2 (Lean draft `scratch/wk-cr3/Literature.lean`)
- Compiled with `lake env lean` run in ~/dzq-check2 (prebuilt oleans at 520e27e5; `git diff
  520e27e5 66e9ce28` touches only KERNEL_PLAN.md, README.md). No errors, no sorry.
  `#print axioms`: propext, Classical.choice, Quot.sound for `IsLContinuation.eq`,
  `certifiedRankTYZClRk_of_literature`, `tyzRow5b_of_readingA` (out_literature.txt).
- Definitions: `IsLContinuation E F` (F entire, = Mathlib `E.LSeries` on Re s > 3/2);
  `T5aCl`, `Admissible5aNat` (row 5a with gCl).
- Props: `GrossZagierKolyvagin` (all E/ℚ elliptic: ord_{s=1} = 1 ⇒ point of infinite order),
  `RootNumberVanishing` (d ≡ 5: F 1 = 0), `TYZRow5b` (T5bCl d = 1 ⇒ ∃ F, ord ≤ 1),
  `HeckeContinuation` (∃ F for d ≠ 0), `TYZThm35ReadingA` (ord ≥ 2 ⇒ T5aCl = T5bCl = 0).
- Theorems: `IsLContinuation.eq` (uniqueness, identity theorem), `analyticOrder_eq_one`,
  `certifiedRankTYZClRk_of_literature : TYZRow5b → RootNumberVanishing → GrossZagierKolyvagin →
  CertifiedRankTYZClRk`, `tyzRow5b_of_readingA : TYZThm35ReadingA → HeckeContinuation → TYZRow5b`.

## Step 3 (functional equation; conventions check)
- Added `completedL N F s = N^{s/2}(2π)^{−s}Γ(s)F(s)`, Prop `FunctionalEquation5`
  (d ≡ 5 sqfree, N = 32d²: Λ(2−s) = −Λ(s)) and `rootNumberVanishing_of_functionalEquation`.
  Compiles; standard axioms (out_literature.txt).
- `conventions_check.py` (PARI, 20 squarefree d ≡ 5 (8), d < 4000): conductor 32d², root number −1,
  model y² = x³ − d²x globally minimal, Kodaira III at 2 and I0* at p | d (additive: Mathlib local
  factor 1, ellap = 0), ellap(p) = p + 1 − #C_d(F_p) for good p < 40. 0 failures
  (out_conventions_check.txt).

## Step 4 (main-theorem variant)
- Added `frozenTarget_of_sixContactMin_literature : SixContactMin → TYZRow5b → FunctionalEquation5 →
  GrossZagierKolyvagin → FrozenTarget` (via RankVariants.lean:69). Compiles; standard axioms.
