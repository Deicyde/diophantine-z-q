# cm-points results log

Task cm-points, 2026-11-13. Statements, findings, compile outcomes. Marks: VERIFIED / STANDARD /
SPECULATIVE / UNVERIFIED (theorem numbers from memory).

## 06:42 start
- Fresh start (no earlier log). Branch wip/cm-points at 322303a2. origin/wip/x0-32 and
  origin/wip/ring-class do not exist yet (VERIFIED, `git branch -r`).
- Mathlib (pinned) has: `PeriodPair`, `weierstrassP`, `derivWeierstrassP`, `g₂`, `g₃`,
  `derivWeierstrassP_sq : ℘'² = 4℘³ − g₂℘ − g₃` (Analysis/SpecialFunctions/Elliptic/Weierstrass.lean);
  `WeierstrassCurve.LFunction` (coefficients a_m); `Affine.Point.map` (Galois action);
  `AlgHom.IsArithFrobAt`. No modular parametrization, no CM points, no ring class fields,
  no binary-form class group (VERIFIED by grep).
- `~/tyz-src` absent: TYZ line numbers are quoted from nt-tyz / rv-tyz-inputs / tyz-t1.

## 06:55 CM.lean statements compile (`lake env lean`, no errors)
- Defs: `galPt`, `ptsOver`, `ι₀`, `ιC`, `latA` (period pair with g₂ = −16, g₃ = 0, chosen),
  `IsUnifImage`, `aCoeff`, `modParam`, `HeegnerForm`, `HeegnerForm.tau/lat/latN/conj`,
  `heegnerPt`, `sqrtD`, `IsFrobAbove`, `conjPrimeLat`, `IsHomothetic`, `tyzForm`,
  `tyzHeegnerPt`, `tyzZn`, `genusSum`.
- Leaves: `CMAlgebraic`, `CMFieldOfDefinition H`, `ShimuraReciprocity`, `CMComplexConj`.
- Normalization check (VERIFIED by hand): for y² = x³ + 4x, x = ℘, y = ℘'/2 gives
  y² = x³ − (g₂/4)x − g₃/4, so g₂ = −16, g₃ = 0; dx/(2y) = dz.

## 07:25 Package.lean statements compile (`lake env lean`, no errors)
- Needs `lake build ZInQKernel.Contrib.TYZDecomp.Leaves` first (builds lean/ ZInQ helpers).
- Defs: `Module GaussianInt PtA` (via `[i]`), `ptT = (2, −4)`, `tauG y = y • ptT`, `Pseq`
  (TYZ recursion by well-founded recursion), `EpsClasses`, `oddPartSqfree`, `betaOneSign`,
  `IsBetaOneLift`.
- Leaves: `IContained Hn`, `NormalFields Hn`, `Lemma318 Hn`, `GenusPtsDefined Hn Z`,
  `Thm35First ℓ Z`, `Lemma321 Z`, bundled `GenusPointLeaf ℓ Hn`.
- betaOneSign check (by hand): D = −1: sgn −1, odd part −1 ≡ 7 (mod 8) → −1; product +1, so a
  β₁-lift fixes i (TYZ L2581) ✓. D = 2 → +1; D = −2 → −1 (consistent: √−2 = i√2).

## 08:20 Glue proved (Package.lean builds, `lake build ZInQKernel.Contrib.TYZGenus.Package`)
- CM.lean: `mem_ptsOver_iff` (A(K) = points with coordinates in K), `iPt_mem`, `galPt_mem`,
  `galPt_iPt` (F4: σ fixing i commutes with [i]) — VERIFIED (compiled).
- Package.lean: `ptT_add_self : T + T = (0,0)`, `four_zsmul_ptT`, `tauG_eq_zero :
  tauG y = 0 ↔ twoTwoI ∣ y` (TYZ L1386 for the pinned τ), `galPt_tauG` (β_τ),
  `fixes_i_of_isBetaOneLift`, `Pseq_eq`, `Pseq_mem`, `genusData_of` (core: pinned objects give
  `PropN.GenusData ℓ n`), `genusPackage_of_genusPointLeaf`, `genusPointLeaf_of_split`,
  `genusPackage_of_split`, `tyzThm35ReadingA_of_split`.
- `#print axioms tyzThm35ReadingA_of_split`: [propext, Classical.choice, Quot.sound] (VERIFIED).
