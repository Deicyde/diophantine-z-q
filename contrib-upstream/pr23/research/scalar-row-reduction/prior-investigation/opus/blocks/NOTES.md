# Non-detector, non-scalar blocks of #13 (380): accounting and savings search

Directory: this folder. Source: copy of `/tmp/codex-glazer389-review-3j08z564/cube/build/cube45/builder.cjs`
(`base_builder.cjs`), the package `construction/` copied from `$SP/pr13`, and the #9/#12 helper scripts in
`tools_copy/`. `measure.py` = node builder + `compile_ir.py` (count before the four pole factorizations);
`finalize.py` = omission + `run_pipeline.py --orders 2` + the two transport scripts, adapted exactly as
`detector-cube-reuse/reproduce.py` does. Baseline reproduces 397 raw -> 384 compiled -> **380 final**, transport PASS.

## 1. Exact accounting of the final 380 (MEASURED from the actual IRs)

| block | raw | final | contents of the final coordinates |
|---|---:|---:|---|
| base | 61 | 59 | input 1; 9 charts x 4 = 36; lambda + 2 Gaussian witnesses; 12 detector pole + 4 scalar pole witnesses; 3 anchor. (scalar.preparationU/V unused, omitted) |
| point_modules | 18 | 18 | x=h^2 (A,S,T,Z) and f=g^2 (H,UA..UZ): 9 K-coords |
| five_differences | 30 | 30 | V0: f, primaryRatio kH, kV; V1..V4: inverseRoot tau, f=tau^2, scaledK M (6 each) |
| parameters_and_logarithms | 70 | 60 | G12 logs V0,V2,V3,V4: fSquare,w^2,w^4,u,eta = 10 each; G2 log V1: fSquare, eta = 4; L1..L4, LP1..LP4 = 16. The 10 `logV*.polynomial` are eliminated by the compiler |
| direct_tests_and_shared_symmetric_coefficients | 53 | 53 | inputProduct 1; Lucas C, AT, F = 6; test squares 2 (order 12) + 10 (order 45); mixedTestProduct 2; order-1 symmetric 20; order-45 symmetric 12 |
| fixed_height_scales | 8 | 8 | A.x*S.x, *T.x, *Z.x (C0,C1), C0^2, (C0+C1)^2 |
| subtotal | 250 | **228** | |
| detectors / scalar / anchor / factored_v | | 122 / 25 / 1 / 4 | |

Free reuse already present: all 8 order-1 test squares (U.f = g^2, and conj f(V)^2 = the log's fSquare),
the H and UA test squares (H.x, UA.x), U/V `parameters()` (no z), the logs' degree-12 polynomial (eliminated).

Version 13 comparison: V13's corresponding blocks total 210, but with a different chart/difference model
(biquadratic V points, odd witnesses, hybrid detector holding its symmetric data); the chart port is already
measured as 0 and the rational log as +8. No other V13 block pays less for the same object: V13 logs are
also 10 per G-log, V13 height scales cost 9, V13 stores 8 order-1 test squares that #13 gets free.

## 2. Exhaustive affine-alias check (MEASURED, finite computation)

`sample.py` evaluates the raw IR over F_p (p = 1e9+7, sqrt 2 exists) on the actual chart varieties
(A,S,T,Z square-abscissa, four reciprocal U charts, joint H curve, lambda chart; every gate solved, all
chart and gate rows verified zero). `alias.py`: 422 samples, matrix [1 | 397 coordinates] has full rank 398.
**No coordinate is an affine combination of the others on the chart variety**, so no cube-reuse-type
alias exists anywhere in the raw circuit. (Finite check over one prime; not a proof, but an exact
rank certificate for the generic point mod p.)

Near-eliminability scan (`subst.py`): in my blocks the only coordinate blocked by a single row is
heightProduct C1 (row: scale1=(C0+C1)^2); storing U=C0+C1 instead is the same count.

## 3. Candidates

### A. Drop the three order-1 primary tests g(U_S), g(U_T), g(U_Z)  — MEASURED -15 (final 365), NOT SOUND AS IS
Patch: `droptests.py` (filters PU[2..4] from `tests`, order-1 groups [3,2]). Compiled 369, final 365,
transports PASS (`finalize.py drop3U_32`). Partial: one test -4 (376 final), two -8 (372 final).
Groupings [5] or [2,3]: 371/369 compiled.

Why it is plausible: L_i = z(U_i)/z(H) with v(z(H)) >= 45, and LP_i ~ (u_i-n_i)/(h-1) exactly on
E_1(p'). If v_p(h-1)=0 then LP_i is integral, the order-45 cross test makes L_i integral, hence
v(z(U_i)) >= 45 and the order-1 test is implied.
Obstruction (exact): if p | h-1 then p does not divide h, so H in E_45(p) forces [N_p]P to have depth >= 45
at p (an elliptic-Wieferich-type prime, not excludable). Then U_i outside E_1(p) is compatible with
the cross test (both ratios have valuation <= -45, requiring p^45 | h-1), and F(L) = 0 mod p^45 says
nothing about the labels. The current proof (geometry_round4, "One of h,h-1 is a p-unit") uses the U test
exactly in this case. Required for acceptance: a proof that excludes or neutralizes this case at every
consumed contact prime, or a cheaper test enforcing p | h or integrality of LP_i. Completeness is
unaffected (dropping tests only weakens the predicate). I found no such argument; order-0 integrality
tests need a 1/E weight per detector and look more expensive.

### B. Measured regroupings/orders (all worse; MEASURED compiled counts, baseline 384)
input test to order 12: 387 ([3] + 45:[3,2]), 389 (45:[5]); H test to order 12: 387;
order-45 single block [6]: 391; order-1 [8]: 398; order-1 [5,3]: 389.

### C. Count-neutral rewrites (reasoned, not built)
- kV removal via logV0*(x_P fV + j_P s - 1) = -h_P s out0: needs out0 stored (+2) for -2: 0.
- Lucas with LP_i instead of L_i; l_i-normalized cross tests; tests on tau instead of f(V_i);
  heightProduct as (AS)(TZ) or via h-products: all equal cost.

## 4. Tightness reasons (ESTIMATED arguments, no proofs)
- Each order-45 log needs G_n with 4(n+1) >= 45, n >= 11 (G12 precision 51 capped by prime 53).
  Degree >= 9 in w needs three K-gates after w; two gates reach only degree 8.
- Lucas F has degree-4 monomials a^2tb and a^2b^2: at least two K-products before F; F must be stored
  for its square.
- Test values must be affine for their squares to be quadratic, so each L_i and LP_i quotient costs 2.
- The scales must be squares of degree-1 rationals, hence C0 and U stored + two squares + two K-products.
- Lambda needs two Gaussian witnesses: completeness takes lambda-32/1225 = p/(D0 w)^2 with p a Gaussian
  prime (round5 detector_final), so a single square is impossible.
