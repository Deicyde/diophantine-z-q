# theta-wp8 results log

## 2026-11-15 setup
- Merged origin/wip/jacobi-lambda (b6fc38e9) and origin/wip/gz-heegner (58a780e4) into wip/theta-wp8: clean.
- Target: `X0EtaRoute.ThetaWeierstrass8` (ZInQKernel/Contrib/OneProof/X0ModuliUsed/EtaRoute.lean:919).

## Proof plan (VERIFIED numerically, scratch/theta-wp8/num/check.py, 4 random w, err < 1e-38)
Notation: ϑ(z) = jacobiTheta₂ z w, s(z) = ϑ(z + (1+w)/2) (zeros exactly Λ = ⟨1,w⟩), c = 1/2 + w/8.
- (P1, Liouville) h(u) = (℘(u) − ℘(c))·s(u)²/(s(u−c)s(u+c)) is exactly 1- and w-periodic, meromorphic
  with order ≥ 0 everywhere, order 0 at u = 0; so h ≡ K ≠ 0 off its singular set.
- Hence wpRatio(1/2, 3w/8, c) = R := s(a−c)s(a+c)s(b)²/(s(a)²s(b−c)s(b+c))
  = ϑ(1/2+3w/8)ϑ(1/2+5w/8)ϑ(1/2+7w/8)²/(ϑ(w/2)²ϑ(3w/4)ϑ(w)).
- (P3, series split) θ₃(w) − θ₂(w) = θ₄(w/4), i.e. ϑ(0) − e^{πiw/4}ϑ(w/2) = jacobiTheta₂ (1/2) (w/4).
- (P2+P4, triple product, Q = e^{πiw/8}) θ₃/θ₂ = 1 − 2R reduces to products ∏(1 ± Q^{16n+k}) and
  the even/odd product split.

## Compile results (all VERIFIED, `lake env lean` / `lake build`, Lean 4.35.0, Mathlib v4.35.0)
- scratch/theta-wp8/ThetaZeros.lean (dev file, 870 lines): compiles; `ThetaWP8.core` axioms [propext, Classical.choice, Quot.sound].
  - Part A: `sF_add_one`, `sF_add_w`, `sF_eq_factor` (s = (1 − e(−y))·G), `hasDerivAt_sF_zero` (s'(0) = 2πi A³),
    `sF_ne_zero` (zeros ⊆ ℤ+ℤw, triple product), `sF_add_lat`, `sF_lat`, `sF_simple`.
  - Part B: `reg`, `reg_eventuallyEq`, `reg_analyticAt`, `reg_add_period`, `isBounded_range_of_periodic`.
  - Part C: `hF_add_one`, `hF_add_w`, `hF_local` (4 cases), `hF_const` (∃ K ≠ 0, h ≡ K off singular set).
  - Part D: `theta_gp` (triple product at base Q = e^{πiw/8}), `gp_shift`, `gp_split`, `gp_pm`, `euler16`,
    `theta4_quarter` (θ₄(w/4) = θ₃ − θ₂ by even/odd series split), `val_t0/t2/t4/u/f4`, `prod_identity`.
  - Part E: `core` (any PeriodPair with ω₁ = 1, ω₂ = w).
- ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean (new, imports X0ModuliUsed): `lake build` OK (12995 jobs).
  `ThetaWP8.thetaWeierstrass8 : X0EtaRoute.ThetaWeierstrass8` (exact statement), `xEtaWeierstrass`,
  `tyzThm35ReadingA_noHX`, `frozenTarget_noHX` (binders of `ZInQ.OneProof.frozenTarget` minus `hX`).
- #discharges (scratch/theta-wp8/Discharges.lean → discharges-output.txt): 63 open hypotheses, 2103 theorems,
  7 discharge one (the same 7 pre-existing ones; `hX` is a plain argument of frozenTarget, not a bundle field).
  All five new theorems and `ZInQ.OneProof.frozenTarget`: standard axioms.

## gz-heegner `X0ModuliGaloisMero` (subtask 2)
- Used in `heegnerC_fixed` (Heegner.lean l. 1033–1123) at the newform level N, g = xPar, yPar (VERIFIED, read).
- C_d form: d ≡ 5 (mod 8) squarefree, conductor 32d² (VERIFIED, PARI, num/conductor.py: 800, 5408, 14112, 26912,
  43808, 89888); a_13(C_1) = 6 vs a_13(C_5) = −6, a_5(C_1) = −2 vs a_5(C_13) = 2 (VERIFIED, PARI).
- Verdict: never N = 32; the eta route does not cover it; the hL3 fold keeps X0ModuliGaloisMero.

## Deliverables
- docs/research/theta-wp8.md; scratch/theta-wp8/autofold.json (manual fold; hX not a bundle field).
