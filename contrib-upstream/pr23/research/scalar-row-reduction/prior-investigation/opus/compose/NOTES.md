# compose: stacking pow46/pow48/pow50 + tri + A (+ tau, ri31) — 2026-11-09

These are author exploration notes. They are not reviewed and claim no arithmetic acceptance.
Every build uses a copy of the #13 pipeline (`work/`), driven by `drive.py`. The driver applies the frontier
detector transform, or the weight47 `powinv` transform, and then the sibling patches without changes.
The pipeline steps are:
node builder -> compile_ir -> checker.cjs (gate identities; 0 unverified in every build) -> omit unused ->
run_pipeline --orders 2 -> four conic transports with check_transport (PASS in every build).
Balancing uses an integer two-phase precise LP (`tools/weights.py`, from coeffrows), followed by
`tools/balance_weights.py`. Each table is then verified twice: by `tools/check_diagonal_weights.py`
(the adapted independent checker) and by `tools/verify_diag.py` (rows, table, content 1, x0^4 coefficient 1). Both report PASS for every row below.
No compile-time hacks and no post-compile hand edits were used.

Reproduction: `build/p46`, `p46_tri_2016`, `p46_tau_2016` and `p46_tau31_2016` have final IRs byte-identical to
frontier `vpow46_2016` and scalarpoles `f376`, `f374` and `f374_31`.

## Results (all MEASURED)

| build | vars | digits | E | LP spread |
|---|---|---|---|---|
| p46_triA_2016 | 376 | 426 | 2016 | 9/41 |
| p46_triA_2010 | 376 | 425 | 2010 (sharpened) | 9/41 |
| i50_triA_2016 | 376 | 426 | 2016 | |
| p46_triA31_1956 / _1944 | 377 | 421 / 418 | Lucas k=46 package / sharpened | |
| i48_triA31_1704 / _1692 | 377 | 368 / 365 | Lucas k=48 | |
| i50_triA31_1518 / _1512 | 377 | 328 / 327 | Lucas k=50 | |
| p46_tau_2016 | 374 | 485 | 2016 | 1/4 (sibling fractional: 509) |
| p46_tau31_1956 | 375 | 471 | 1956 | 1/4 |
| i50_tau31_1518 | 375 | 367 | 1518 | 1/4 |

## Minimum anchor exponent (tools/minE.py; exact integers, margins as in frontier/anchor_frontier.py)

The scalar order-47 margin c*^(32*47-577) > (4H)^(32*47) is extrapolated from the order-31 form.
It gives E >= 1368, so with ri31 the Lucas margin binds. The minimal E values are:
k=46: 1956 (sharpened 1944); k=48: 1704 (1692); k=50: 1518 (1512).
Without ri31 the order-31 scalar margin pins E at 2016 (sharpened 2010) for every k >= 46.

## Independent checks (tools/indep_check.py; imports no stack code)
- `gates RAW K` evaluates every raw-IR gate modulo 2^127-1 at 3 random base points. In every detector it asserts
  q12=q1^23, mixedHigh=q1^46, q_K=q1^(2K-1), and power2 and power3 equal to q_K^2 and q_K^3. A negative control is included.
  PASS for pow46 (base build and triA), powinv48 and powinv50.
- `rowop` (sympy, raw IR): only the two w-definition rows change. Each changes by an exact constant combination of the
  S.chart.x.{0,1} definition rows, (-39/8, 18) and (9/2, -39/4). PASS.
- `tri` (sympy and Groebner over QQ, raw IR):
  - The differing rows are W2.def, T.def, Bh.def and secondConic. The pole's Bh is rescaled by the constant
    mu=184460384539620, so the compiled pole changes beyond a simple rename.
  - Explicit maps are used in both directions:
    - Forward: T := 42 r W2 and Bh := mu Bh.
    - Backward: W2 := N^2, T_old := rhs and Bh := Bh/mu.
  - Under these maps every target row lies in the source ideal, which includes the unchanged r*ri-1 row. PASS.
- This check proves that tri and A preserve the zero set. It does not establish the arithmetic theorem.

## tau vs A (task 2)
- A's w row equals h_S times tau's row (w = h_S tau), so the two rows have identical spread.
- A's advantage comes from the anchor N(w) = N(h_S tau): it lets the h_S weight enter the anchor. The anchor N(tau) cannot.
- On tau, A has no quadratic analogue: tau*x_P*h_S^2 is cubic.
- A greedy constant-row-op search on the binding rows of p46_tau_2016 (`tools/lp/rowops.py`) finds no improving operation,
  so the spread stays at 1/4. The binding rows are tau.def, S.chart.x.1.def and anchor.
- Restoring w as a coordinate costs +2, which gives 376, the same count as A alone. A is therefore not subsumed by tau, and the two do not combine.
