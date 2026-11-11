# rv-elim3 log (adversarial review of el-cert, el-k3, el-qfree)

## Step 0. Read the three notes; claims to test
- el-cert: M1 soundness (Phi(B), B = R0' a^2/Theta0^2 => 2v(Theta0) < v(R0')); local lemma at p | Theta0, (R0/p) = -1.
- el-k3: NS(Xbar) rank 20 disc -16 from 40 curves; NS^G rank 8, even, D^2 = 0 mod 4; H^1 = 0; case B parity.
- el-qfree: multiplier window (v_p(m) even >= 0 above 324; v_p(m)=0 where v_p(B)=1; M finite); Hom(Jac Y_theta, C1) claim; theta=1 criterion.

## Step 1. Pole system (ZInQKernel/Hypotheses/Pole.lean:39)
A = mB, H = A(A - B^2); (A, r1) on y^2 = x(x^2 - e^2); (Az^2, z r2) on y^2 = x(x^2 - (eH)^2); eHzw = 1.
Derivation (L7 generalized): if a = v_p(A) is odd and a - 2b > 0 (b = v_p(B)), no p-adic solution.
The proof never uses b < 0. Hence for b >= 1 odd and v_p(m) even > b, no Q_p solution:
this re-derives el-qfree's completeness constraint (v_p(m) = 0 where v_p(B) = 1) without Loc/beta.
Trivial witness: e = A, r1 = 0, z^2 = H, r2 = 0 solves the system when m(m - B) is a nonzero square.

## Step 2. Necessity of the multiplier window (q1_window.py) — VERIFIED
Inputs: p in {331, 337, 1009}; m = p (v=1), p^-2 (v=-2), p^3 (v=3); B = m(1 - c^2) with c = 1/p, 1+p, 1/p^2.
Then m(m-B) = (mc)^2, trivial witness e = A, r1 = r2 = 0, z = sqrt(H) solves the system exactly.
Outcome: 9/9 solved with v_p(B) = -1. So any m with v_p(m) odd or negative at p > 324 breaks
SC1 globally (not just "for this proof"). el-qfree S2 window (v_p(m) even >= 0) is necessary and
sufficient. Completeness constraint v_p(m) = 0 at b = 1: VERIFIED by Step 1 derivation.

## Step 3. el-cert local lemma rerun (c1_local.py) — VERIFIED
Inputs: 26 random (p, m, R0, T), p in {7,29,31,37,41,43}, seed 7, (R0/p) = -1, v_p(T) in {1,2}.
Outcome: el-cert's brute-force locsol (mod p^3) agrees with "(−m/p) = −1" in 26/26 (10 soluble, 16 not).
Proof (independent): v(a(q)) = min(0, 2v(q)) <= 0 since x^2 - R0 y^2 is anisotropic mod p, so
f(q) = -m R0 a^2 (1 + O(p^{2v(T) - 2v(a)})) has even valuation and unit class -mR0; the point at
infinity has the same class (-mR0^3). Hypothesis p | num Theta0 only needs v_p(Theta0) >= 1.

## Step 4. el-cert X3b independence model on real data (c2_theta0_primes.py) — VERIFIED
Inputs: 12 real test-site instances from el-qfree/k0.py (Lean formulas): n in {1,2,3}, kappa = 1,
(h, s0) in {(2,3),(3,5),(2,7),(5,2)}, eta = 1; Theta0 = poleTheta(R0, C) (M1). Trial division of
num Theta0 (248-1315 digits) up to 2e6; primes 13 < p, p not dividing R0.
Outcome: (R0/p) = -1 at 32 of 70 such primes (no bias toward +1). Obstruction primes per instance 1-5
(from the partial factorization only). Signed divisors m of 2730 surviving all found obstructions:
8,4,16,8,16,0,8,32,32,16,32,2 of 64 (upper bounds). One instance (n=2,h=3,s0=5) already kills all 64.
Conclusion: the el-cert local obstruction is real on genuine data even at kappa = 1; X3b's model is
consistent with it. No refutation.
