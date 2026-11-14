# tyz-321 results log

Target: `CMBridge.Lemma321Five` (TYZ Lemma 3.21(1)), copied verbatim with all of
`scratch/cm-bridge/Bridge.lean` (§0–§15) into `scratch/tyz-321/L321.lean`; new work in §16.

## 2026-11-13 22:40 start
- Merged origin/wip/cm-bridge: already contained in base (no-op).
- Build: `lake build ZInQKernel.Contrib.TYZGenus.ShimuraFricke` started (no build artifacts in worktree).

## Numerics (wlat.py, exact arithmetic in K = Q(sqrt(-n)))
- For b = a ∩ O4, a = (m, sqrt(-n) - 1), m = (n+1)/2, Q = [16(n+1), -8, 1] (tau = (1+w)/(8m)):
  the word `WT` (tau'' = W(tau + 1/4) = -1/(32 tau + 8)) satisfies
  b·(<1,tau''>, <1/32,tau''>) = c·(<1,tau>, <1/32,tau>) with c = (-1 + ((n+3)/2) w)/(n+4),
  for all 10 tested n = 5, 13, 21, 29, 37, 53, 61, 69, 77, 85. VERIFIED (computed).

## 2026-11-13 23:20 compile 1 (VERIFIED, `lake env lean scratch/tyz-321/L321.lean`, 0 errors, no sorry)
- `T321.lemma321Five_of (hβ : BetaOneLiftExists) (hz : ZnOverH4) (hc : TYZThm36ConjFive)
   (hw : TYZThm36OneFive) (hk : KerFixesZnMod) (hg : BetaOnGenus5) : Lemma321Five` — the core glue
   (TYZ's proof of Lemma 3.21(1), for any lift σ, every e | n, e ≡ 5 (8)).
- `znOverH4_of : Shimura.ShimuraReciprocityModFn → ZnOverH4`.
- `tyzThm36ConjFive_of : CMAlgebraic → TYZThm36ConjFive` (z̄_n = −z_n + τ(1)), via
  `yC_add_quarter : yC (z + 1/4) = I * yC z` (eta), `xC_add_quarter : xC (τ + 1/4) = −xC τ` (theta form),
  `toC_iPt_of_quarter` (φ(τ+1/4) = [i]φ(τ)), `tyzForm_conj_tauH` (τ_{Q̄} = W T₄ W τ_Q), Fricke (tyz-cm).
- helper: `exists_acts4_of_fix` (an automorphism of Q̄ fixing K_d acts on H_{d,4} as an Artin symbol).
