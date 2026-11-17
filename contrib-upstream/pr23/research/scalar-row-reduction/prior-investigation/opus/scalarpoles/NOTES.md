# Scalar / pole / anchor savings above #13 (380) — notes, 2026-11-08/09

All counts MEASURED with a copy of the stack pipeline (`measure.py`: node builder ->
compile_ir -> checker.cjs -> omit unused -> run_pipeline --orders 2 -> four-conic transport
(+check) -> balance). Baseline reproduced exactly: 380 vars, table sha 373c624d...

| Variant (patches.py name) | Vars | Rows | Max digits (E) | Status |
|---|---|---|---|---|
| base380 | 380 | 349 | 682 (2130) | reproduced |
| tri: T defined by ri*T = 42 N^2 (drops W2) | **379** | 348 | 682 (2130), diag checker PASS | exact identity |
| tau: tri + tau=w/h_S chart, proxy Re(k_H tau), guard 1/proxy | **377** | 346 | 539 (2144), 536 (2128) | new local args |
| tauf0: tau but guard on f0=tau0^2+2tau1^2 | 378 | 347 | LP spread 1/4 | fewer args |
| tau31: tau + ri31, leaf y=t/r^32 (scalar order 47) | 378 | 347 | 537 (2136) | |
| f376: sibling 377 (order-46) + tri | 376 | 345 | (std balancer) | exact identity |
| f374: sibling 377 + tri + tau | **374** | 343 | 509 (2016) | |
| f374_31: f374 + ri31 (scalar order 47) | 375 | 344 | 497 (1968) | |

Digits for tau-family use LP-optimal fractional diagonal weights (lp_local.py, spread 1/4,
units E/16 or E/24) via balance_frac.py; every one rechecked by verify_diag.py (rows,
quartic table, content 1, x0^4 coefficient 1). The baseline LP optimum is 1/3 (dual
certificate of the other session); the tau rows remove that obstruction.

## Obligations
tri: r*ri=1 is retained, so ri!=0 and T=42N^2/ri=42rN^2=rho*W^2. Bijection with old witnesses
(W2:=N^2). No arithmetic change.

tau: (1) tau=(h_P j_S - h_S j_P)/(x_P x_S + D) equals w/h_S because x_S=h_S^2 (algebraic);
tau^2=f(S-P) as rational functions. (2) Chain leaves C,D0 replaced by tau0,tau1: positive
valuation of tau at both places <=> of f(Q)=tau^2; descent bounds unchanged (order 31).
(3) Proxy Re(k_H tau): tau*k_Q = -h_P/h_S + O(p^m); h_P=-1+7/4 sqrt2 has norm -41/8, so a unit
off {2,41}; need h_S/h_P == 1 mod p at both places for Q deep, and an explicit precision check
at the nonunit place above 41 (rework of geometry_round5 two-place proxy lemma). (4) Anchor uses
N(tau): v3(tau)=v3(w) once h_S is a 3-unit (after the unchanged oddness step, which uses only
anisotropy); v2(tau)=v2(a-1)+3/2 so coefficients 2-integral. Rework arithmetic_round8 anchor
section. (5) Guard 1/Re(k_H tau): soundness Q=O => tau=0 => proxy 0. Completeness needs the
proxy nonzero at the chosen point (p-adic congruence at a prime of r outside the exceptions, or
real-analytic avoidance on the H-neighbourhood) -- unproved; tauf0 (378) avoids it.
(6) New E must be a multiple of 16/24 for the fractional scaling and satisfy the margins.

ri31: +1 coordinate, proxy bound t > 32 + 451/32 => order 47. Without extra coordinates the
order cannot exceed 31 in this cost model: bound = j + m3/2 + m2/4 + m1/8 + (2m0+1)/32 with
j<=16, m<=15 gives 30.09; a larger r-exponent needs another Laurent step (exponents 2^k-1).

## Negative results
- Detector poles already use preparation zero (detector_round7.tex ~193-220; pole(...,false)).
- T cannot be removed: e*b with b=42rN^2 needs N and one more coordinate (N,T) in every
  rescaling tried (1/N, rN, square scalings of s,v,Q).
- Pole p2/q2/v: conic coefficient is a nonconstant square class; reparametrizations tried
  (line through (17,0), H-coordinate form, e elimination) all keep 7 coordinates.
- Shared factoring coordinate / product of pole inputs: parity of other inputs uncontrolled.
- Anchor physicalA: Theta inherently quadratic (needs both coefficients of w at 3 via the
  anisotropic norm); no linear substitute.
- V13 one-place tree: Norm(f(H)) is a free left leaf, but the stack's proxy needs H and Q
  formal at a common place and depth of (a-1)/h, not of k_H; one-place leaves allow k_H deep
  via v_p(h). Estimated -3/-4 only with a new local lemma that fails as stated. Not built.
