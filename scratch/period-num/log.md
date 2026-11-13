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
