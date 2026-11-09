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

## Step 3: library + batch 1 (Lemma P(1)-(2) locally)

- `slopelib.py`: independent implementation (R0, field 2, Lemma P hypotheses, Hensel square root,
  weak-approximation q = m/(Dpole L^k) with CRT residue targets, model test values in Z[sqrt2],
  v_p(B) via PARI p-adics with precision tracking, B real via mpmath). Model S_b = S_ht ∪ H,
  H = [331, 337]; ell0 = 12 P_s^2916 H^732 exactly (383,613 digits). Smoke test `t_smoke.py` OK.
- `b1_lemmaP1.py` (output `b1_out.txt`), 30 inputs: l=2 e=1..5; l in S0 with e=1,5,40;
  l = 11, 331, 317; v = 2^7 3^6 5^5 7^5 13^5 at each S0 prime; 5 controls with F(t)<0.
  * Under the hypotheses of Lemma P: v_l(R0) = 2e, v_l(t-1) = -e, R0 square, and the Hensel
    q0 = w/l^e gives v_l(1 - R0 q0^2) >= N in 25/25 cases. Lemma P(1)-(2): CORRECT.
  * l = 2, e = 1, 2: R0 is a non-square in 2000/2000 random samples (not "often": always).
    Proof: unit part == (1+6k)*5 mod 8 (e=1), == 5 mod 8 (e=2), k odd. So e >= 3 is sharp.
    Harmless: e <= 4 = B_2 is covered by field 2.
  * Controls F(t) < 0, eta = -1, e = 5: R0 square at l = 5, 13 (2000/2000), non-square at
    l = 2, 3, 7 (0/2000). "Lemma P must fail for F<0" is true only at l in {2,3,7}; at
    l == 1 mod 4 it holds (since -1 is a square). Not a defect; the hypothesis F(t) > 0 could be
    weakened to "eta R0 l^{-2e} is a square in Q_l".

## Step 4: batch 2 run 1 (partial), AP instance search, first end-to-end instance

- b2 run 1 (`b2_out_partial_run1.txt`, 16 of 30 inputs before I stopped it to speed up the
  library): every input with the modified q passed (v_l(B) >= 4 on S0, no odd negative valuation on
  the model S_b, 0 < B < 1/2). Rerunning all 30 with the faster library (`b2_out.txt`).
- Library fix: at split primes the norm W0^2 - 2 W1^2 loses all precision when one embedding of
  W is a unit and the other has large negative valuation (selected primes); now each embedding
  sqrt2 -> +-r in Q_p is computed separately.
- Independent density count (`dens.py`): 1,925 good slope primes among odd primes < 2e5 (share
  0.107), all in the class p == 1 (8), (7/p) = -1; agrees with nt-22p/[RP].
- `ap_search.py`: sieve + PARI ellcard search for genuine instances of the 14-point set of
  Prop AP. Admissibility: for A = -70 (|S+| = 11) v must be divisible by 2, 3, 7, 11; for |S+| = 14
  by 2, 3, 7 (or 2, 7). Hits (all values good slope primes):
  A=-70: v=480480=2^5·3·5·7·11·13 x=6455441; v=2^10·3·5·7·11·13 x=249339257, 522677321;
  v=2^5·3^5·5·7·11·13 x=654796201, 835325417; v=2^3·3·5^5·7·11·13 x=2046031433;
  v=2^3·3·5·7^5·11·13 x=2733858433, 4249498417. (Further runs in progress.)
- `b3_ap.py` on A=-70, v=480480, x=6455441: t1 = 6935921/480480, t2 = -35764721/480480, t3 = -10.
  Fields 1, 2', 3, 4 hold for all three (Lemma P branch at 2 for t1, t2, e = 5). v_2(B) = 6096,
  6100; other S0 primes 5834; v_p(B) = 1 at all 6+6 selected primes; only negative valuations
  at u - v (resp. u - (A'-1) v), even (-216), and at the auxiliary prime (even); 0 < B < 1/2.
  t3 = -10: eta = -1, all fine. ALL OK.

## Step 5: more instances, sign batch, Lemma P(3) isolation

- More genuine instances (ap_runs_out.txt, ap_runs2_out.txt): A=-70 v=2^3·3·5·7·11·13^5
  x=7409892761, 8739955537; A=-70 v=2^3·3·5·7·11·13·331^2 x=2924927297, 9413594497;
  A=-69 (|S+| = 12, first sign case, boundary A'+60 = 1) v=480480 x=2547011473;
  A=-40 (|S+| = 11, first case) v=2^5·3^5·5·7·13 x=752276761, 937852193.
- b4_signs.py (b4_out.txt): 28 values of A incl. -75..-63, the case change at A = -69/-70, A with
  |S+| = 11, 12, 13, +-10^6; 200 random (x, v) each incl. v = 2^40, 3^30·7: t1 > max S+,
  t2 < -60, F(t1), F(t2) > 0, t1, t2 not in C ∪ {1}: no failure. Sign step: CORRECT.
- Correction to nt-22p §3.3 remark 1: K_A = A + 130 for A' + 60 >= 1 and K_A = -A - 8 = |A| - 8
  otherwise (not "|A| + 71"). No consequence.
- b5 part B run 1 (b5B_out_run1_unforced.txt): with v_l(ell0) = 0 and e <= 4 (field 2 holds,
  ball not forced) v_l(B) < 0: expected, the old argument needs E_l. With e = 7 at 2 and e = 9 at
  3 (Lemma P ball) v_l(B) = 362, 460 >= 4, and the old q gives -2548, -3288: Lemma P(3) works
  with E_l = 0, and the implementation detects failures. Rerun with ball forced: b5B_out.txt.

## Step 6: Lemma P(3) isolation (b5B_out.txt), report parts 1-2 drafted

- b5 part B (ball forced, v_l(ell0) = 0), 10 slopes x 2 choices of q: Lemma P ball gives
  v_l(B) = 166, 362, 58, 460, 108, 208, 58, 308, 1508, 3008 (all >= 4); old q gives
  -1094, -2548, -360, -3288, -724, -1456, -366, -2196, -10980, -21948 (~ -366e, as predicted by
  v(B) = 18(E + alpha) - 366e for unit test values). Lemma P(3): CORRECT; N sufficient, not sharp.
- b2 (rerun) so far: all modified-q inputs pass; controls with old q at e = 200 fail as predicted
  (v_3(B) = -20690 vs predicted 18*2917 - 366*200 = -20694).
- slopelib fix: log10(R0) via mpmath (float overflow for v ~ 10^300). Restarted b5 A and C.
- Report docs/research/rv-nt22p-red.md: verdict, findings F1-F7, step checks 2.1-2.3 written.
