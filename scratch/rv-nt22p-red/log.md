# rv-nt22p-red log

Python env: /tmp/rvred-venv (cypari2 2.17, gmpy2, numpy, mpmath). Recreate with
`~/bin/uv venv /tmp/rvred-venv && VIRTUAL_ENV=/tmp/rvred-venv ~/bin/uv pip install cypari2 gmpy2 numpy mpmath`.

## Step 1 (reading): definitions used

- Manuscript slope predicate lines 1177-1191; completeness lines 1705-1758; PC Thm 5.2 line 1002.
- Lean: `GoodSlope` (PatternSlopes.lean:27), `poleInput`, `pole_input_valuations` (PoleValuations.lean),
  `slope_complete`, `weak_approx_q`, constants (Certificate/Constants.lean):
  B_p = 4 on S_ht, 1 otherwise; C_p = 14B_p; E_p = 52C_p + v_p(12) + 4; ell0 = 12 P_s^2916 H^732.
  `IsOddContactPrime t p`: v_p(t-c) positive and ODD for some c.
- PC (Pole.lean:62): IsSquare B.den, 0 < B < 1/2, v_p(B) >= 4 on S0 = {2,3,5,7,13}.

## Step 2 (reading): first hand checks of Lemma P / Prop AP

- Lemma P(1): R0 = v^2 F(u,v)/(u-v)^8 for t=u/v. CORRECT. Hypothesis "u-cv, u-v prime to l" is
  automatic when l | v and gcd(u,v)=1 (remark, not a defect).
- Lemma P(1) square claim: product prod(1 - c v/u) == 1 mod l^e. CORRECT for l odd, e>=1; l=2, e>=3.
- With eta = -1 (F(t)<0): R0 l^{-2e} = -(square)(1+O(l^e)); a square in Q_l iff -1 is a square:
  l = 5, 13 YES, l = 3, 7 NO, l=2 NO. So the "control" fails only at l = 2, 3, 7 (to confirm numerically).
- Lemma P(3) valuation bookkeeping: v(C) = v(D) - e(k-1); v(RC^2) >= 2E + 2alpha - 46e. CORRECT.
  Trace at ramified 2: v_2(Tr x) >= floor((m+3)/2) for v_P(x) = m/2: fine.
- Observation: E_l = 2916 + v_l(12) on S_ht, so even with alpha = 0 (old q) the bound
  v(RC^2) >= 2E + 2e - 48e > v(12) holds for e <= 126 at l in S_ht. B_l = 4 is far from sharp.
  (To confirm numerically: old choice of q already works at S_ht primes for 5 <= e <= 126.)
- Catalogue = first 22 primes > 324 in each unit class mod W = 4 P_s; every prime 324 < p < W is
  itself the first prime of its class, so S_b contains ALL primes < W ~ 10^137. Pattern primes are
  above that; all prime factors of v below W are old primes (B_p = 1 for 324 < p).
