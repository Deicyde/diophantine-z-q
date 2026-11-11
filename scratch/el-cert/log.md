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

## X3. Arithmetic of the M1 theta=1 curve C_m: Y^2 = m^2 T^2 - m R0 (1 - R0 q^2)^2 (T = Theta0)

- Lemma (local obstruction). p odd, p !| 2mR0, v_p(T) >= 1, (R0/p) = -1. Then C_m(Q_p) != {} iff
  (-m/p) = -1. Proof: R0 nonresidue => 1 - R0 q^2 never in pZ_p for q in Z_p, and for v(q) < 0 the
  term R0 q^2 dominates; so f(q) = -m R0 A^2 (1 + O(p)) with A != 0, a square iff (-mR0/p) = 1.
  (VERIFIED: derivation; x3_local.py brute force mod p^3, p in 11..23, 26/26 agree)
- X3b (x3_stats.py, 200 trials per row): obstruction primes r ~ Poisson((1/2) log log N),
  N = num(Theta0), primes ~1e12 with (R0/p) = -1, R0 = 2730^6 F(7). P(some m locally unobstructed):
  log10 N = 1e3: DL8 0.430, signed divisors of 2730 0.785, group <-1, p<=324> (2^67) 1.000
  log10 N = 1e6: 0.120, 0.425, 1.000
  log10 N = 1e9: 0.015, 0.115, 1.000
  Honest Theta0 has height ~ kappa^2 h(P0) with kappa a common multiple of group orders, so
  log10 N is astronomically large: with 6 multiplier bits theta=1 is locally impossible for most
  instances; the L7 multipliers m0 k^2, m0 | prod_{p<=324} p, clear the local obstruction but cost
  61 more bits per pole call (~61 x 8.3e6 = 5.1e8 variables to save). (VERIFIED as stated; the
  Poisson model is SPECULATIVE)
- X3c (x3_points.py, ~8 min): 30 toy instances R0 = |F(n)|, n = 1..30, T random (num <= 3000,
  den <= 300), m in DL8 (240 curves). Jacobian rank bounds (ellrank): (0,0) 61, (1,1) 104, (0,2) 66,
  (1,3) 9. Points of naive height <= 2000 on C_m: 0 curves, 0/30 instances. Rank 0 proven for 25%
  of Jacobians (then C_m(Q) is finite, possibly empty). (VERIFIED, exact PARI; 2730^6 dropped)

## S4. Structural lemmas (any redesign of the thin/explicit kind)

- L-A (degree). If f in Q(R0)(u) is nonconstant and v_p(f(u)) <= gamma for all u in P^1(Q_p)
  (or >= gamma), then deg f >= 2: a degree-1 map is a bijection of P^1(Q_p) and hits p^(gamma+1).
  So every free parameter enters B through a map of degree >= 2. (VERIFIED, elementary)
- L-B (no algebraic witness). Honest test instances (t = n, V0 = [kappa]P0, V1 = [kappa n]P0) are
  Zariski dense in A^1 x E x E (the slices Gamma_[n] have unbounded degree); the bad instances
  contain {t in a p-adic open set} x {pairs of multiples}, also Zariski dense. A witness given by a
  rational map of instance data that zeroes polePoly on the honest locus zeroes it generically,
  hence at some bad instance, contradicting Lemma 5.1. So any completeness proof needs a
  non-algebraic existence theorem. (VERIFIED as an argument; density of the slice union by the
  degree argument)
- L-C (uniform anisotropy is valuation-only). Uniform in the instance, the only input at a
  contact prime is v_p(R0) odd; residue symbols (b/p) cannot be forced for all contact p by a fixed
  b in Q(t)* (Chebotarev). Forms anisotropic by valuations alone have at most d variables in degree
  d (monomials with distinct v mod d); examples: x^2 - R0 y^2 (d=2), N_{Q(R0^(1/4))} (d=4).
  (STANDARD ingredients; the "at most d variables" claim for all uniform forms is SPECULATIVE)
- Consequence (Kodaira). The theta=1 locus over a parameter family of this kind is the double
  cover of P^(n-1) branched along {F = +-c G}, degree 2d, n <= d: K = (d - n)H >= 0. Best case
  n = d = 2 is M1's genus-1 curve; n = d = 3 a K3, n = d = 4 a CY3. Never rational, so no
  Hasse-principle theorem applies; L-B forbids uniform sections. (SPECULATIVE beyond n = d = 2)
- Conic gadgets cannot replace Phi: a Hilbert-symbol obstruction (a(B), b(B))_p depends on unit
  parts mod p, so no conic family is obstructed exactly when v_p(B) is negative odd for all large p.
  Fat (open-set-complete) sound Phi' therefore needs genus >= 1 fibres, whose completeness is a
  Hasse principle for 2-coverings, i.e. CR3-type. (VERIFIED for diagonal/norm conics with
  coefficients polynomial in B by the leading-term computation (B, cB^d)_p = ((-1)^d c / p)^v;
  general claim SPECULATIVE)

## S5. Variants tried (all reduce to S4)

- R2 multiplier as a free square, m = m0 k^2: theta = 1 for k = (u + m0 B/u)/(2 m0), any u.
  Soundness (L7) needs v_p(k) >= 0 at contact primes for every witness. Available p-integral
  families: 1/(1 - R0 q^2), Z[t] (t is p-integral at its contact primes), bit-integers. Fibre
  product with u-conic: genus 1 / K3 (L-A). Uniform Poonen-type T_{a,b} (quaternion) definitions of
  intersections of Z_(p) need (a,b)_p = -1 at all contact p: no uniform b (L-C). (VERIFIED: algebra)
- R3 additive Theta shift Theta = Theta0 + R0 h, v_p(h) >= 0: with g = 1 the theta=1 condition is the
  rational conic m^2 T^2 - m R0 = Y^2, T = (u + mR0/u)/(2m); h = (T - Theta0)/R0 must be a value of a
  p-integral family (1/A(q2)): bidegree (2,2) curve, genus 1. With both g = A(q1) and h = 1/A(q2):
  tridegree (2,2,2) in (P^1)^3, a K3. (VERIFIED: algebra)
- R4 one-curve torsion target (t1 = inf): Phi <= E_{B(m-B)} point with x in mB Q*^2: quartic in t,
  same fibre-product counting (genus >= 1 in each parameter). (VERIFIED: rs-pole 2.2(3) algebra)
