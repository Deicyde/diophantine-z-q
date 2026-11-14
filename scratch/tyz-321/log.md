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
