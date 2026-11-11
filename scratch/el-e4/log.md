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
