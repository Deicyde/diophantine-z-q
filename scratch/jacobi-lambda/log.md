# jacobi-lambda results log

Target: `ZInQ.GZWeil.JacobiLambdaDeriv` (ZInQKernel/Contrib/OneProof/GrossZagierHeegner/WeilTheta.lean, gz-weil f4a06a48):
`∀ t, 0 < t.im → HasDerivAt (fun s => thetaTwo s ^ 4 / thetaThree s ^ 4) (π * I * (thetaTwo t ^ 4 / thetaThree t ^ 4) * thetaFour t ^ 4) t`.

## Survey (VERIFIED, read)
- Mathlib v4.35.0: `jacobiTheta₂` (TwoVariable.lean) with `jacobiTheta₂_add_left`, `_add_left'`, `_neg_left`,
  `hasFDerivAt_jacobiTheta₂`, functional equation; `jacobiTheta` bounds `norm_jacobiTheta_sub_one_le`.
  No theta-constant identities (no Jacobi quartic, no Landen), no modular forms for Γ(2), dimension formula only level one.
- Kernel: gz-theta triple product `jacobiTheta₂_eq_jtpP`; gz-weil product forms at 16τ.

## Route chosen
Landen recursion: with h = θ₂/θ₃, F = h'/h − (πi/4)θ₄⁴ satisfies F(τ) = (θ₄²/θ₃²)(τ) F(2τ) (from Landen + Jacobi quartic),
and F(σ) = O(e^{−π Im σ}); iterate to get F = 0.

## Compile outcomes
- 05:25 `Dev.lean`: duplication formula `jacobiTheta₂_mul_jacobiTheta₂`
  θ(z,τ)θ(w,τ) = θ(z+w,2τ)θ(z−w,2τ) + e^{2πiz+πiτ}θ(z+w+τ,2τ)θ(z−w+τ,2τ): VERIFIED (compiled; numerically checked dup_check.py).
- 05:35 Landen identities `landen_three`, `landen_four`, `landen_two`, `landen_three_four` and `jacobi_quartic`
  (θ₃⁴ = θ₂⁴ + θ₄⁴): VERIFIED compiled, axioms [propext, Classical.choice, Quot.sound].
- 05:55 exponential bounds for Im s ≥ 1: ‖T(s) − 2‖, ‖θ₃(s) − 1‖, ‖θ₄(s) − 1‖ ≤ 3e^{−π Im s}
  (T(s) = jacobiTheta₂ (s/2) s, θ₂ = e^{πis/4}T): VERIFIED compiled.
- 06:15 Cauchy estimate `norm_deriv_le_of_bound`, nonvanishing `thetaFour_ne_zero`, `thetaThree_ne_zero`, `thT_ne_zero`,
  `thetaTwo_ne_zero` on ℍ (by iterating Landen up to Im ≥ 1; no products), and the recursion
  `Fq_rec : F τ = (θ₄(τ)²/θ₃(τ)²) F(2τ)` with h = θ₂/θ₃, F = h'/h − (πi/4)θ₄⁴: VERIFIED compiled, standard axioms.
- 06:45 full proof `jacobiLambdaDeriv'` in Dev.lean: VERIFIED compiled, standard axioms.
- 06:55 contributor file `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean` (imports WeilTheta):
  `lake build ZInQKernel.Contrib.OneProof.GrossZagierHeegner.JacobiLambdaDeriv` success (11342 jobs).
  `Check.lean` → `out_check.txt`: verbatim copy of the Prop ↔ gz-weil's constant by `Iff.rfl`;
  `ZInQ.GZWeil.jacobiLambdaDeriv`, `etaModelDifferential`, `modularParamC1`, `shimuraCMParamCd`,
  `grossZagierHeegnerCd_of_leaves4` all [propext, Classical.choice, Quot.sound]. VERIFIED.
- 07:10 `Discharges.lean` → discharges-output.txt: 65 open, 1526 checked, 6 discharge one (same six as base; new theorems
  discharge none directly, as expected). `MainEdit.lean` → out_mainedit.txt: `frozenTarget_jacobiLambda` (hL3 → 4 leaves),
  standard axioms. autofold.json dry run: "not a field of the current bundles: ['jacobiLambdaDeriv']" (expected at this base).
- Report docs/research/jacobi-lambda.md written.
