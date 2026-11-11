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
