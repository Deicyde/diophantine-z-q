# el-cert log

Marks: VERIFIED / STANDARD / SPECULATIVE. Worktree base e3612538.

## S1. Why s = l0 a / Theta has its form (traced in Lean)

- Test site (`SixLocalTests.lean`): R0 = eta 2730^6 F(t), a0 = 1 - R0 q^2, R = R0 a0^2,
  W = prod_j (1 + R C_j^2), Theta = Tr W^-1, input B = R/Theta^2. Slope site
  (`SlopePredicate.lean`): R0 = eta F(t)/(t-1)^8, R = l^2 a^2 R0, W_g = prod_j (1 + R C_gj^2),
  Theta = Tr sum_g W_g^-1. (VERIFIED)
- Soundness consumes Phi only via `pole_step` (TestDivisibility:225) / `pole_obstruction` in
  `common_group_of` (CommonGroup:114): Phi(R/Theta^2), v_p(R) = r odd => 2 v_p(Theta) < r.
  Then factor valuations min(0, r + 2v(C)) (`vp_one_add_mul_sq`) and the trace bound give
  "tests small". (VERIFIED)
- Role of a = 1 - R0 q^2: `testR_val` / `contact_valuations_of` prove v_p(a) <= 0 at every contact
  prime (v_p(R0) odd => no cancellation in 1 - R0 q^2). So r = v(R0) + 2v(a) <= v(R0); a smaller r
  only strengthens the conclusion of tests_small. This is the only property of a used. (VERIFIED)
- Role of q in completeness: only to put B in the PC-admissible box (0<B<1/2 via a ~ 0 at the real
  place, v_p(q) >= C_p on S_b, square denominator). (VERIFIED, cr3-map-needs L2/L3)

## S2. Modification M1 ("frozen Theta"): build W from R0' (q-free), keep a in the numerator

- Test: W0 = prod (1 + R0 C_j^2), Theta0 = Tr W0^-1, B = R0 a0^2 / Theta0^2.
- Slope: W_g = prod (1 + l^2 R0 C_gj^2), Theta0 = Tr sum W_g^-1, B = l^2 a^2 R0 / Theta0^2.
- Soundness: Phi(B) gives 2v(Theta0) < v(R0') + 2v(a) <= v(R0') = k. That is exactly the hypothesis
  the existing proofs derive at q = 0 (a = 1, r = k), and the remaining argument does not see q.
  So M1 soundness = existing soundness at q = 0 + (v(a) <= 0). (VERIFIED by reading pole_step,
  tests_small, testR_val, common_group_of, contact_valuations_of)
- Positivity: eta makes R0 > 0, K0 = Q(sqrt2) totally real, so each factor >= 1 in both embeddings,
  W0 > 0, Theta0 > 0: the guards W != 0, Theta != 0 hold for all q. (VERIFIED, elementary)
- Budget: same operation count (R0 instead of R inside W). (VERIFIED by inspection of formulas)
- Effect: s = a/Theta0 has degree 2 in q (was ~ deg 50 test / ~ 600 slope).

## S3. With an explicit Phi-witness the open set U is irrelevant

- `Test` (SixLocalTests:66) and SlopePred need only the guards + PoleSoluble(B). If
  m(m - B) = c^2 (theta = 1) then Phi(B) by the 2-torsion witness (rs-pole 2.2(2)). No
  admissibility (0<B<1/2, square den, S0 valuations) is needed for that. (VERIFIED: reading)
- M1 + theta=1 target: Y^2 = m^2 Theta0^2 - m R0' (1 - R0 q^2)^2, a genus-1 quartic in q.

## X1-X2 (script x1_genus.py, PARI, < 3 min)

- X1: M1 valuation logic, k odd in 1..11, v(Theta0) in -6..11, v(q) in -12..11: Phi(B) => 2v(Theta0) < k
  with 0 counterexamples. (VERIFIED)
- X2: genus of the theta=1 curve y^2 = m(m N^2 - R0 a^2 D^2) (Theta = N/D reduced), toy tests
  (random C in Q(sqrt2), R0 = 7/3, m = 3):
  test site original: deg_q s = 50, squarefree degree 100, genus 49;
  slope site original: deg_q s = 518, degree 1036, genus 517;
  M1 (both sites): degree 4, genus 1. (VERIFIED, exact)
