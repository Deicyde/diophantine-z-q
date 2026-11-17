# eps-splitting results log

Base: wip/hgz-steps 92fd272e, merged origin/main (e1b31749) as dc6321558.

## Statements and compile outcomes

- `scratch/eps-splitting/QuadInt.lean` (development file, imports Mathlib + `ZInQKernel.Contrib.OneProof.GrossZagierScheme.EpsD`):
  - `exists_int_repr`: for `D` a fundamental discriminant (`Int.IsFundamentalDiscr`), `D < 0`, `[K:ℚ] = 2`, `δ² = D`:
    every `x ∈ K` integral over `ℤ` is `a + b θ`, `θ = (D + δ)/2`, `a b ∈ ℤ`. VERIFIED (compiles).
  - `adjoin_thetaO_eq_top`: `Algebra.adjoin ℤ {θ} = ⊤` in `𝓞 K`. VERIFIED.
  - `minpoly_thetaO`: `minpoly ℤ θ = X² − D X + (D² − D)/4`. VERIFIED.
  - `isInertIn_iff`, `isSplitIn_iff`, `isRamifiedIn_iff`: transfer through Mathlib's Kummer–Dedekind
    (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`, `ZModXQuotSpanEquivQuotSpan`,
    `ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'`). VERIFIED.
  - `splitType_of_irreducible`, `splitType_of_eq_mul`, `splitType_of_eq_mul_self`. VERIFIED.
  - `splitType_epsD`: `SplitType K p (epsD D p)` for every prime `p`, i.e.
    `(IsSplitIn K p ↔ ε_D(p) = 1) ∧ (IsInertIn K p ↔ ε_D(p) = −1) ∧ (IsRamifiedIn K p ↔ ε_D(p) = 0)`. VERIFIED (compiles, 01:5x).
  - `epsD_eq_one_iff_isSplitIn`, `epsD_eq_neg_one_iff_isInertIn`, `epsD_eq_zero_iff_isRamifiedIn`,
    `epsD_prime_trichotomy`, `quadCharPrime_eq_epsD`, `quadChar_eq_epsD` (`quadChar K n = epsD D n` for all `n`). VERIFIED.
- `ZInQKernel/Contrib/OneProof/GrossZagierSplit/QuadSplit.lean` = reorganized `QuadInt.lean` (definitions only need
  `[Field K]`); `lake env lean`: no errors, no warnings. VERIFIED. Copy: `scratch/eps-splitting/QuadSplit.lean`.
- `ZInQKernel/Contrib/OneProof/GrossZagierSplit.lean`: leaf `GZSplit.GrossZagierCurveAtSplit` / `GrossZagierCurveCdSplit`
  (Heegner hypothesis `IsSplitIn K p`, twist `quadChar K`), bridges `grossZagierCurveAt_of_split`,
  `grossZagierCurveAtSplit_of_curveAt` (equivalence), `grossZagierCurveCd_of_split`, `grossZagierCurveCdSplit_of_curveCd`,
  `grossZagierAlgOptCd_of_split : GrossZagierCurveCdSplit → GZAlg.GrossZagierAlgOptCd`.
  - build1 (`lake build ZInQKernel.Contrib.OneProof.GrossZagierSplit`): GrossZagierScheme tree built; GrossZagierSplit
    failed only on a missing `open HeckeRing.GL2` (`Newform`). Fixed; `lake env lean` on the file: no errors. VERIFIED.
- build2 (`lake build +Main +Discharges +GrossZagierSplit`): 14,283 jobs, no errors. VERIFIED.
- `#discharges`: `DISCHARGES [hGZ] by ZInQ.GZSplit.grossZagierAlgOptCd_of_split, still assumes [ZInQ.GZSplit.GrossZagierCurveCdSplit]`,
  standard axioms; 39 open, 11491 checked, 52 discharge one. VERIFIED (`Discharges-output.txt`).
- FoldCheck: `frozenTarget_split` and the five key theorems have standard axioms. VERIFIED (`FoldCheck-output.txt`).
- Rating: `GZSplit.GrossZagierCurveCdSplit` LEAF, printed form (direct instance); equivalent to `GZSch.GrossZagierCurveCd`
  in Lean (both directions). GZ locators UNVERIFIED (no copy on host).
