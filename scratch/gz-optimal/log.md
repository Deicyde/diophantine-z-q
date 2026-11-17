# gz-optimal results log

Base: wip/gz-moduli 85111fc7. Build tree: reflink copy of the gz-moduli worktree's .lake/build and lean/.lake/build.

## Statements read (VERIFIED, in the tree)
- Target leaf: `ZInQ.GZModuli.GrossZagierModuliCd` (ZInQKernel/Contrib/OneProof/GrossZagierModuli.lean:155),
  = ∀ d ≡ 5 (8) squarefree, `GrossZagierModuliAt (shortCurve (-(d:ℚ)^2))` (line 136): every φ = (X, Y) with
  `IsModularParam N E X Y` (X, Y ∈ ℚ(X₀(N)), Weierstrass eqn, pole at ∞).
- Consumer: `grossZagierFormulaCd_of_moduli : GrossZagierModuliCd → GZHL3.GrossZagierFormulaCd`; it applies the leaf only
  to φ = weierPt E L (c φ_f), c ∈ ℚ^×, c Λ_f ⊆ L (`GZHL3.GrossZagierFormulaAt`).
- After heegner-32 (origin/wip/heegner-32 718d8d4c) and gz-conj, the C_d split of hL3 is GrossZagierFormulaCd (+ hCM) only;
  X0ModuliGaloisMero is no longer used (heegner-32 .fleet summary, VERIFIED read).
- Tau Ceti canonical height: `canonicalHeight_nonneg`, `canonicalHeight_eq_zero_iff_isOfFinAddOrder` (Northcott free over
  number fields), `canonicalHeight_zsmul` (VERIFIED read).
- Mathlib `WeierstrassCurve.LFunction` uses `W.minimal R` locally: model-independent (VERIFIED read,
  Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean).
- Additivity of weierPt: heegner-32's `weierPt_short_add` (y² = x³ + Ax only) from vendored FLT
  `PeriodPair.isUniformization_toPoint` (VERIFIED read). Not in base; to be reproved for a₁ = a₂ = a₃ = 0.

## Computations
- PARI `ellweilcurve` (scratch/gz-optimal/py/optimal_cd.py): Smith invariants of L_{E'} in L_f over the isogeny class
  of C_d; [1,1] marks the X₀(N)-optimal curve. d = 5 (N = 800): C_5 optimal, class smith [[1,1],[2,1],[2,1],[2,1]].
  d = 13 (N = 5408): C_13 optimal, same pattern. (VERIFIED, computed)
- Numerical Λ_f vs L(C_d) (scratch/gz-optimal/py/periods_cd.gp, periods_cd.py; output periods_cd_out.txt):
  Ψ(γ) = φ_f(γτ) − φ_f(τ) for γ = [a,b;c,e] ∈ Γ₀(N), c = kN (k ≤ 1 or 2), a ≤ 25 (80 for d = 77), τ = (−e+i)/c,
  q-series to |q|^M < 1e-17, written in the basis E.omega of L(C_d). For d = 5, 13, 21, 29, 37, 53, 61, 69, 77, 85,
  93, 101, 109 (13 values): all coordinates integral (max error ≤ 1e-18) and the sampled periods span L (index 1;
  d = 77 needed the larger sample). So numerically Λ_f = L(C_d), c₀ = 1: C_d is X₀(N)-optimal with Manin constant 1.
  (VERIFIED, computed; a sample, not a proof that every Ψ(γ) lies in L.) PARI ellweilcurve for d = 21 overflowed 14 GB.

## Lean (ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean), `lake env lean`, COMPILED (VERIFIED)
- §1 `weierPt_add'` (a₁=a₂=a₃=0 models, from vendored FLT isUniformization_toPoint), `weierHom`, `weierPt_sum`,
  `weierPt_zsmul`, `weierPt_eq_zero_iff`, `isOfFinAddOrder_iff` (torsion of a K-point from its complex parameter).
- §2 `real_rel`, `int_rel`, `rat_mem_int` (rational multiplier of a lattice is an integer), `exists_int_mul_mem` (finite index).
- §3 statements: `periodLattice` (Λ_f), `IsOptimalParam`, leaf `GrossZagierModuliOptAt`/`Opt`/`OptCd`, GLUE `CdOptimal`,
  `StrongWeilOptimal`/`Cd`, `AnalyticIsogenyRational`.
- §5 `grossZagierModuliOptAt_of_moduliAt` (short E), `grossZagierModuliOptCd_of_moduli`: new leaf ⇐ gz-moduli's leaf.
- §6 `core_selfOptimal`, `core_transfer`; §7 `grossZagierFormulaCd_of_selfOptimal` (route A),
  `grossZagierFormulaCd_of_transfer` (route B); §8 `ModularParamAnalyticAt/Cd`, `grossZagierModuliCd_of_transfer`.
- `lake build ZInQKernel.Contrib.OneProof.GrossZagierOptimal(.NonVacuous)` OK; Check.lean: standard axioms for all main
  theorems (out_check.txt); Target.lean: verbatim copy of GrossZagierModuliAt/Cd, `rfl` (VERIFIED).
- #discharges (discharges-output.txt): 61 open, 3011 theorems checked; no GZOptimal line (hL3 is a top-level frozenTarget
  argument for all E; the C_d theorems are not field types), as for heegner-32/gz-conj/gz-moduli (VERIFIED).
- Merged origin/wip/heegner-32 (718d8d4c) and origin/wip/gz-conj (2c7ce521): clean. MainEdit.lean:
  `frozenTarget_gzoptimal` (hL3 → GrossZagierModuliOptCd + CdOptimal) and `frozenTarget_gzoptimal_transfer`
  (hL3 → GrossZagierModuliOptCd + StrongWeilOptimalCd + AnalyticIsogenyRational), standard axioms (VERIFIED).
- Periods, more d (periods_cd_out2.txt, out3.txt): d = 133, 141, 149, 157 index 1 (a ≤ 25); d = 165 index 2 with a ≤ 25,
  index 1 with a ≤ 80, k ≤ 2. All coordinates integral (≤ 1.4e-18). Total 18 values of d, 5 ≤ d ≤ 165: Λ_f = L(C_d)
  numerically (VERIFIED, computed, sample).
- Report docs/research/gz-optimal.md written; autofold.json (route A), autofold-routeB.json.
