# el-e4 log

## Definitions
- E4 (el-gadget) = M1 (el-cert), same normalization: Theta0 = Tr W0^{-1}, W0 = prod_j (1 + R0 C_j^2),
  B = R0 a^2 / Theta0^2, a = 1 - R0 q^2. theta = 1 witness (rs-pole 2.2(2)): e = A = mB, z = B c,
  c^2 = m(m - B) gives polePoly = 0 (from Hypotheses/Pole.lean: r1 = 0, Az^2 = eH since H = m B^2 (m - B)).
- Completeness curve: C_m : h^2 = m(m Theta0^2 - R0 (1 - R0 q^2)^2), m in multiplier set
  (Lean: signed divisors of 2730, 64 values; L7: m0 k^2, m0 | prod_{p<=324} p signed, k bit-integer).

## Step 1. locsol.py (p-adic local solubility of y^2 = quartic, recursive Hensel on residue discs)
- t0_locsol_check.py: 30/30 agree with el-cert's local obstruction lemma (p in 11..43, random R0, m, Theta0
  with v_p = 1,2); 5/5 curves with a q=0 point found soluble at 2,3,5,7,11,13. VERIFIED.

## Step 2. Jacobian and descent structure (s2_jacobian.py)
- C_m: h^2 = a q^4 + b q^2 + c, a = -m R0^3, b = 2 m R0^2, c = m(m Th0^2 - R0) (even quartic).
- Jac(C_m) = E_J : y^2 = x(x^2 - 4 m R0^2 x + 4 m^3 R0^3 Th0^2)  [VERIFIED 20/20 random: same j, same a_p];
  = quadratic twist by m B0 of y^2 = V(V^2 - 4 B0 V + 4 m B0), B0 = R0/Th0^2 (algebra).
- C_m is the covering of class d = -m R0 (mod squares) for the 2-isogeny psi: E -> E_J,
  E : y^2 = x(x^2 + b x + a c) (standard 2-isogeny descent: N^2 = d M^4 + b M^2 e^2 + (ac/d) e^4).
  So C_m(Q) != empty  <=>  -m R0 in alpha(E(Q)) subset Q*/Q*^2, alpha(x,y) = x, alpha(T) = ac.
  alpha(O) = 1 needs -mR0 square; alpha(T) = ac == d needs m(m Th0^2 - R0) square (the q = 0 point).
  Otherwise a point of infinite order of E in a prescribed class is needed.

## Step 3a. Real instances, first pass (s3_real_local.py, first version)
- Input: n = 1..5, kappa = 1, (h, s0) in {(2,3),(3,5),(2,7),(5,2),(3,4),(4,7)}; Theta0 from Lean formulas
  (k0.py copied from scratch/el-qfree). num Theta0: 248-1530 digits; trial division to 1e7.
- Outcome: all 30 are NOT honest (2 v_p(Theta0) >= v_p(R0) at some odd-valuation contact prime): kappa = 1
  tests are not deep. So C_m is insoluble at those contact primes for all 64 m (as soundness demands).
  Honest instances need astronomically deep kappa (el-cert) and cannot be computed; kappa = 1 data is used
  only as a proxy for the prime factors of Theta0 (as rv-elim3 did).
- Soundness/honest-prime lemma L1 (proof): p odd, p not | m, v_p(R0) = k odd, 2 v_p(Theta0) < k  =>
  C_m(Q_p) != empty (q = 0 disc: f(q) = m^2 Theta0^2 (1 - B(q)/m), v_p(B(q)) > 0 for v(q) >= 0).
- Slope site under M1: B = l^2 a^2 R0 / Theta0^2, a = 1 - R0 q^2: curve h^2 = m(m Theta0^2 - l^2 R0 a^2)
  is C_m with Theta0 -> Theta0 / l (same family).

## Step 3b. Local lemmas (proofs) used to decide primes >= 13
For p odd, p not | m R0 (f = m(m Th0^2 - R0 a^2), a = 1 - R0 q^2):
- L2: v_p(Th0) < 0 => soluble (q = 0 disc, f = m^2 Th0^2 (1 + O(p))).
- L3: v_p(Th0) = 0, p >= 13 => soluble. f mod p = -m R0^3 (q^2 - r1)(q^2 - r2), r1 != r2. If squarefree: Weil,
  #smooth affine pts >= p + 1 - 2 sqrt p - 6 > 0 for p >= 13. If r_i = 0 (p | m Th0^2 - R0): f = c q^2 (q^2 - r),
  conic y'^2 = c(q^2 - r) has >= p - 5 > 0 points with q, y' != 0 (p >= 7). Hensel.
- L4 (el-cert lemma; rv-elim3 VERIFIED): v_p(Th0) >= 1 => soluble iff (R0/p) = 1 or (-m/p) = -1.
- L5: C_{m0 k^2}(Th0, R0) = C_{m0}(k Th0, R0) (h -> h/k); C_m(Th0, s^2 R1) = C_m(Th0/s, R1) (q -> q/s).
  So only the square class m0 matters, and k only adds primes p | k to num Th0: k never removes an obstruction.
- Remaining: p <= 11, p | m, p | R0 with even valuation: decided by locsol.

## Step 3c. Real-instance proxies (s3_real_local.py, final; s3_out.json, s3_out.txt)
- Odd-valuation contact primes skipped (proxy is dishonest there; honest => L1 soluble when v_p(B) > v_p(m),
  +2 at p = 2). Obs = {p | num Th0 found (trial div 1e7), p not | 2R0, (R0/p) = -1}.
- Obs sizes 0..7 (median 3); cofactors of 195-1449 digits unfactored (so survivor counts are UPPER bounds).
- m in signed divisors of 2730 (64) locally soluble at all decided primes: per instance
  8,4,16,4,16,8, 16,0,8,32,64,4, 32,16,32,2,32,16, 8,0,8,0,8,8, 2,8,8,2,8,0.
  4/30 have 0 survivors already; extra failures at p = 2 (even v_2(R0), n = 4) in 4 instances.
  Expected ~5 further prime factors per cofactor (log log heuristic), half obstructing => most instances
  locally insoluble for all 64 m. Matches el-cert X3b and rv-elim3 c2.

## Step 4. L7 group G = <-1, p <= 324> (s4_l7_linear.py)
- Affine F2 system (-m0/p) = -1 on Obs, m0 in G avoiding Obs: solvable 30/30 proxies.
- Random r obstruction primes > 400: solvable 30/30 for r <= 60; 26/30 r=65; 13/30 r=68; 4/30 r=70; 0/30 r=80.
  So any FIXED finite multiplier group of F2-rank g fails once num Th0 has > ~g obstruction primes;
  omega(num Th0) is unbounded over instances (heuristic), so no fixed group is locally complete for every
  choice; completeness must use the per-instance freedom (kappa, h, s0) -- no theorem controls the prime
  factors of Th0 (an elliptic-net value). L7 also costs ~61 bits per pole call (el-cert) and needs v_p(m)
  even at p > 324 only, i.e. Lemma 5.1 at 17 <= p <= 324 must be supplied otherwise at the test site.
