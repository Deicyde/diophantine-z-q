# period-num results log

Task period-num (2026-11-13). Base: fork main 57a7fa26 + merge of origin/wip/period-map (6e458879).
Targets (namespace `HSyn.G0Split.FibreQM.PeriodMap`): `S8Nonzero` (scratch/period-map/part_light.lean),
`S8WeightExact` (scratch/period-map/part_order.lean).

## Setup
- No `~/pyenv`, no sympy/mpmath on this host (VERIFIED: `~/pyenv/bin/python` missing, uv offline has no sympy).
  Numerics are pure python3 (`py/num0.py`, floats; `py/polyred.py`, exact `Fraction` polynomial reduction).
- `PNBase.lean` = `scratch/period-map/PMLight.lean` verbatim (= light_base + part_light + part_theta + part_siegel +
  part_order; `cmp` VERIFIED). Compiled to `olean/PNBase.olean` with `lake env lean -o` (1m29s, 0 errors, axioms standard).
  `dev.sh` checks development files importing `PNBase`.

## S8Nonzero: findings
- `Ω(√2+i) = [[(−1+i)/2, 1], [1, −1+i]]` exactly. VERIFIED: `py/num0.py` (floats) and `py/polyred.py`
  (exact: `Nf(√2+i) − Ω₀·dF(√2+i)` reduces to 0 mod `√2²−2, i²+1`; the quotients are the linear_combination coefficients).
- `Σθ_m⁸(Ω₀) = −33.90792957610…` (py/num0.py, |n_k| ≤ 12), every θ_m⁸ is a negative real numerically.
- Off-diagonal entry 1 ⇒ θ_{(a,b)}(Ω₀) = exp(−πi a₀a₁/2)·ϑ[a₀, b₀+a₁](w₁)·ϑ[a₁, b₁+a₀](w₂), w₁ = (−1+i)/2, w₂ = −1+i
  (cross term exp(2πi x₀x₁) = exp(2πi n₀n₁)·exp(πi(a₁x₀ + a₀x₁))·exp(−πi a₀a₁/2)).
- Hence Σθ⁸ = (Z₀⁸ + Z₁⁸ + T⁸)(P₀⁸ + P₁⁸ + Q⁸), Z_b = ϑ[0,b](w₁), T = ϑ[1,0](w₁), P_b = ϑ[0,b](w₂), Q = ϑ[1,0](w₂);
  P_b real, Q = e^{−iπ/4}·(positive), T = e^{−iπ/8}·(real), Z₀ ≈ 1.0037 − 0.4158i, Z₁ = conj.

## S8Nonzero: Lean (part_nonzero.lean; DevNonzero.lean = import PNBase + the same text)
- DevNonzero iterations 1-6: errors fixed (rewrite side of `exp_add_int_mul`, linear_combination coefficients of `I_sq`,
  `Summable.tsum_pos` name, `Complex.exp_int_mul` argument order, sum over the 10 chars via `Finset.sum_insert (by decide)`).
- Final DevNonzero: 0 errors, 9s; `s8Nonzero_proof : S8Nonzero`, axioms `[propext, Classical.choice, Quot.sound]`. VERIFIED.
- run_full1 (`build.sh`: PNFull.lean = period-map light files verbatim + part_nonzero.lean, `lake env lean`): 0 errors,
  all axioms lines standard, 24s. VERIFIED.
- Proof structure (all compiled): `omega_s2I`, `thetaConst_split`, `th1_zero_two`, `th1_one_two`, `th1_one_one`, `P_real`,
  `Q_eq`, `T_eq`, `th1_zero_zero`, `th1_zero_one`, `jt_approx` (tail ≤ e^{−2π}/(1−e^{−π})), `exp_bounds`
  (0.135 < e^{−π/2} < 0.227, tail ≤ 1/380, from Mathlib's `Real.exp_one_gt_d9`/`lt_d9`, π ∈ (3,4)), `re_pow8_neg`,
  `re_Z0`, `re_Z1`, `thetaSum8_s2I`, `s8Nonzero_proof`.
- py/nonzero_num.py (nonzero_num_out.txt): splitting VERIFIED to 1e-15 for all 10 chars; F1 = −11.646, F2 = 2.9115,
  F1·F2 = S = −33.9079; Re Z_b⁸ = −1.941; T⁸ = −7.764; P₀ = Q·e^{iπ/4} = 0.91358, P₁ = 1.08643.
