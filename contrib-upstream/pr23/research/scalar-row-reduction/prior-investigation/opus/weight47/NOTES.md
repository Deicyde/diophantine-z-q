# weight47: higher-order detector weights at the order-45 coordinate budget

Directory: `$SP/explore/weight47/` (SP = session scratchpad). Builds use a copy of #13's research
packages in `repo/research/`; the driver is `repo/research/weight47/run.py` (variants rinv, cube_q1, powF, powinv).
No arithmetic acceptance. All counts below are MEASURED with the actual pipeline (compile_ir, checker.cjs
gate check, unused-slot omission, run_pipeline --orders 2, four conic transports, balance, diagonal check).

## Measured builds (anchor 3^2016)

| build | order | weights (per detector) | normalization | coords/res | monomials | digits |
|---|---|---|---|---|---|---|
| build/powinv48 | 48 | q1^4(shared with E1.power4), I=1/q1^3, q1^10=q1^7/I, q12=q1^20/I, mH=q12^2, q48=mH^2/I | q_m=q1^(2m-1) | 377/346 | 25,965 | 646 |
| build/powinv50 | 50 | q1^8=(q1^4)^2, I=q1/q1^8, q12=(q1^8)^2/I, mH, q50=mH^2/I | q_m=q1^(2m-1) | 377/346 | 25,968 | 646 |
| build/powF47 | 47 | q1^6,q1^12,q12=q1^23,mH, q47=mH^2/F | e^93 delta^-97 A^-5 (needs C=sqrt(A) unit) | 377/346 | 25,989 | 646 |
| build/rinv47 | 47 | R=1/E, q5=q1^3E/R, q11=q5^2/R, q12=q11^2/R, mH, q47=mH^2/R | e^93/delta^3 (round-6 form) | 380/349 | 25,992 | 646 |
| build/cubeq1_46 | 46 | #13 cube chain, q46=mH^2/q1 | e^91/delta^3 | 380/349 | 26,025 | 646 |

Each build: gate-check passed_exact_algebra_checks with 0 unverified, transport PASS, diagonal PASS.
Digits 646 = 28902*3^1344 at E=2016. No digit gain over order 46 at present: E is bound by the scalar margin
(sibling `frontier/NOTES.md`), so orders 48/50 matter only if that margin improves (Lucas bound falls with k).

## Checks run
- `check_semantics.py` / `check_pow377.py` / `check_powF47.py`: evaluate the actual raw-IR gates at random
  rationals (Fractions), recover t, A=t/lambda (=scale0/scale1), e=(A delta)^5/F, and assert exact semantic
  values of q1, E, q12, mixedHigh, q_N, q_N^2, q_N^3 in all three detectors, plus the one-place normalization
  identity 1+R(D delta^s/R^m)^2 (s=-(2m-1); powF47: extra factor A^-5 = C^-10). Negative controls (wrong
  exponent; #13's cube47 IR checked against q1-powers) are rejected.
- `diff_rows.py`: by-name raw row diff. Sibling 377 (vpow46_2016) vs my cube_q1 order 46: deletes 9 eCubed/eSixth/
  eTwelfth rows, adds 6 q1Sixth/q1Twelfth rows, changes only 3 q12 rows; guards identical; 352 rows unchanged.
- `identities.py` (sympy): R-inverse chain and normalization identities.

## Searches (all exhaustive in the stated monomial model)
Model: stored monomials; a gate adds one coordinate v with z*v = x*y (x,y,z stored or 1), plus free quadratic
Q = delta^k (k<=8, from G=t^2*M times cubics). Base per detector: delta,delta^2,delta^3 (affine aliases), q1..q1^4, E;
optionally F (e-exponent -1, carries A^5 for r>0) and r>0 items C, A, A*delta, (A delta)^2, (A delta)^4.
Targets: q12, q12^2, q_N, q_N^2, q_N^3 (all must be coordinates). Budget = all new detector-weight coordinates
(order-45 #13 = 8; sibling = 7).
- `search.cpp` + drive*.py: fixed normalizations. delta^-1 weights: order 45 needs 8, 46/47 need 9 (with or without
  delta^k Q extras). Grid of delta exponents (|b|<=13): order 47 at 8 only via R=1/E (b=-3), or F (r=0 only).
- `search2.cpp` + drive2.py: free odd negative delta exponents for the q12 family and the q_N family (and optionally
  free even C exponent). Budget 7, N=47..51:
  - delta-only normalization, valid in all 3 detectors (rA, freeA=0): N=48: 5 chains, N=50: 12; N=47,49,51: none.
  - with A-normalization (freeA=1): solutions for every N=47..51.
  - detector 0 alone (A=1, F free): N=47..51 all feasible.
- `onedim.py`: 1D relaxation by total order at the five roots of F (covers e, delta, A, C, F, affine products of
  linear factors, degree<=8 Q). Budget 6 is infeasible for every N in 13..51, with or without F. A hand proof:
  every stored e-exponent lies in [-1,4], so after one intermediate the next gate has e-exponent <= 19 < 23.

Not covered: non-monomial intermediates (affine combinations whose cancellations change valuations),
sign-ambiguous rows v^2=Q, changes to the mixed (order-12) block or to E/R, regrouping of symmetric blocks.
Nothing is shared between the three detectors (different t).

## Obligations (none reviewed)
- All q1-power routes: one-place lemma with semantic test D*delta^-(2m-1) (sibling's list 1-6). delta>0 and is a unit
  at consumed primes; contact valuations of q_m unchanged (-(2m-1)); real decay O(lambda^-(2m-1)); p=2,3,17 valuations
  -> infinity. Denominators are q1, q1^3, q1^8 and their inverses, all >0 since q1*F=A*U^4>0 and F>=0 on the chart.
  No new guard and no zero branch. Order m in 48..51 also needs the bc51100 precision-51 argument rewritten for general m
  (primary progression Pi^(m-1), Lucas margin b*^(16m-577) increases with m, identity branches unchanged).
- powF47: also needs v_p(C_r)=0 at every consumed contact prime. The v6 source (version6/.../diophantine_optimization_20261106_v3.tex
  ~l.2822) chooses primes "beyond all prime factors of the fixed coefficients and scales"; confirm the current #13
  completeness keeps this. q47 = mH^2/F: F>0 already established.
- rinv47: normalization delta^-3 is the round-6 form; R=1/E>0.
