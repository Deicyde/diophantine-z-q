# Frontier: detector order k, anchor E, alpha, weight circuit (2026-11-09)

Author exploration, not reviewed. No arithmetic acceptance. All builds are from copies in `work/`.

## Headline

**377 variables / 646 digits (MEASURED)**: order-46 high tests, anchor 3^2016, and the uniform
weight normalization `q_m = q1^(2m-1)`. That is the semantic test `D_j/delta^(2m_j-1)`. Each
detector's weight chain is `q1^6=(q1^3)^2`, `q1^12`, `q12=q1^23=(q1^12)^2/q1`,
`mixedHigh=q1^46`, `q46=q1^91=mixedHigh^2/q1`, then powers `q1^182` and `q1^273`.
That is 7 gates, against 8 in #13 (`e3,e6,e12,q12,mixedHigh,q45`, plus 2 powers).
This saves one coordinate per detector.

- `build/vpow46_2016/MEASURED.json`: 377 coords, 346 residuals, 25,968 monomials, max coeff 28902*3^1344
  (646 digits, 2146 bits). Gate checker passes with 0 unverified gates, the transport check passes, and the diagonal check passes.
- `build/vpow45_2130`: 377 / 682 digits (same chain with order 45: `q45=q1^89=mixedHigh^2/q1^3`).
- `build/vpow46_2010`: 377 / 644 digits. This relies on the other session's sharpened consumers
  (NEXT_PR.md). I checked that its exact Lucas test also passes at m=46, E=2010 (`sharpened_check.py`).
- Sanity: `build/v45_2130` reproduces #13 exactly (table sha 373c62…, 380/682).
- Intermediate: `build/v46d3_2016` = 380/646. It uses order 46 with only the last weight changed to
  `mixedHigh^2/q1 = e^91/delta^3`, which is the round-6 normalization.
- `check_pow_chain.py` independently decodes the raw IR gates. In all 3 detectors they give
  q1^{2,3,6,12,23,46,2k-1,2(2k-1),3(2k-1)}.

## Why the normalization is admissible (proof obligations)

Lemma v5-one-place (quartic_v10.tex:11031–11061) takes arbitrary D_j in K. With R=1/E=1/(e*delta):
`1+R((D_j delta^s)/R^m)^2 = 1+e^(2m-1) delta^(2m-1+2s) D_j^2`. Round 6 used s=-(m+1), giving delta^-3.
Round 7 used s=-m, giving delta^-1. Here s=-(2m-1), giving `(e/delta)^(2m-1)=q1^(2m-1)`. Obligations:
1. Soundness: delta is a unit at consumed primes. This is the round-7 claim, unchanged and independent of s. So v(D_j)>=m_j.
   R, the trace and B are unchanged.
2. Contacts: v(q_m)=-(2m-1), the same as now. The opposite-place odd valuation and the unit trace are unchanged.
   For the promoted order-12 test g_A: 1-24+2*45>0, unchanged.
3. Real infinity: q_m=O(lambda^-(2m-1)), so W=1+O(1/lambda) and 0<B<17 still holds eventually.
4. p=2,3,17: v_p(q_m)=(2m-1)(nu+4(eta+alpha)) tends to infinity as nu grows (round-7 leading-term valuations).
5. Positivity: q1>0. The new quotient denominators are q1 and q1^3 only.
6. Order 46 (from bc51100 higher-detector-precision): G12 precision 51>=46; primary progression Pi^45;
   all primary identity branches; Lucas `b*^(16*46-577)>(24H)^368` at E=2016 (passes; Lucas-only
   minimum is 1956); scalar c*^415>(4H)^992 at E=2016 (binding). Input order 12 is unchanged.
None of these has been reviewed. Points 1–5 need a written application like detector_round7.tex.

## Anchor vs order (anchor_frontier.py, exact integers, package consumers 7H, |F|<5B^4, b*=c*/2)

Minimum E (a multiple of 6) = max(scalar order-31 margin = 2016, Lucas margin). Digits come from
28902*3^(2E/3), which matches 682@2130 and 646@2016 exactly.

| k | E | digits | gates (q1-power) | vars | status |
|---|---|---|---|---|---|
| 37 | 16656 | 5303 | 8 | 380 | est |
| 38 | 8280 | 2639 | 8 | 380 | est |
| 39 | 5610 | 1789 | 7 | 377 | est |
| 40 | 4290 | 1370 | 7 | 377 | est |
| 41 | 3510 | 1121 | 8 | 380 | est |
| 42 | 2988 | 955 | 8 | 380 | est |
| 43 | 2622 | 839 | 7 | 377 | est |
| 44 | 2346 | 751 | 8 | 380 | est |
| 45 | 2130 | 682 | 7 | **377** | MEASURED |
| 46 | 2016 | 646 | 7 | **377** | MEASURED |
| 47–51 | 2016 | 646 | 8 | 380 | est |

The k>=46 rows are bound by the scalar margin. The minimum scalar-only E by scalar order s is:
28:2364, 31:2016, 32:1932, 33:1860, 34:1794, 36:1686, 40:1536. At k=46 the Lucas bound alone is 1956
(about 625 digits). So the scalar order is now the digit bottleneck: s>=33 would let k=46 reach E=1956.

## Circuit search

- `chain_search.cpp` is an exact IDDFS over (e,delta) monomials. Its base is q1, E, q1^2..q1^4 plus the affine
  delta, delta^2 and delta^3. Gates have the form X*Y/Z. With strict delta^-1 weights: k=45 needs 8 and k=46 needs 9 (8 with
  delta^-3). With |d|<=7 there is no 7-gate chain (`chain_grid_d8.txt`).
- `eonly.py` is the e-exponent projection, a relaxation of every monomial model. It finds no 6-gate chain for any
  input order j in {10,11,12} and any k in 37..51 (`eonly6.txt`). 7-gate chains exist exactly for
  j=12 and k in {39,40,43,45,46}, plus some j=10/11 cases at k<=42. Every e-chain is realizable
  as q1-powers, which gives the table above. 7 is minimal in this gate model, and k>=47 needs 8 because 2k-1>92.
- Not explored: the stored F has e-exponent -1 but carries A^5, so it helps only detector 0 (A=1).

## Alpha slack (alpha_slack.py, float ESTIMATE)

alpha=18+6*eps comes from the Euler-product cutoff. Here eps=1/192 (primes<53, constant 32/9), and the "3" is
fixed by the level, character and Javanpeykar inputs. Lowering eps raises H. The best value, eps≈1/384–1/768,
gives E(45) 2130→2124 (−2 digits). k>=46 is unchanged because the scalar margin binds. k=36 never becomes
admissible (it needs alpha<18). Computing the exact product instead of 32/9 at eps=1/192 gives scalar 2010
at k>=46. This is minor and overlaps the other session's height work.
