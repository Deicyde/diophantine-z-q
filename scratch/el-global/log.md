# el-global step log

Marks: VERIFIED (script here or proof), STANDARD (reference), SPECULATIVE.

## Definitions (step 1)

- `A = Res_{K0/Q} E`, abelian surface over Q; `A(Q) = E(K0) = Z P0 + T` (T = E[2], order 4; index_two_E = 8).
- Data space `Y = A^1_t x A^1_q x {eta, bits} x A^m` (data labels: [n]P0, [h]P0, [s0]P0, [h-k]P0, [s0-kn]P0).
  Tests (SixLocalTests.lean:40): D1 = w([h]P0), D2 = w([s0]P0), D3 = w([h-k]P0)^*, D4 = w([s0-kn]P0)^*,
  D5 = z([s0]P0)/z([h]P0) - t, D6 = (z([s0-kn]P0)/z([h-k]P0))^* - t; w = 1/x, z = -x/y.
- Label gadget: `X ⊂ Y x A^s x A^w` (s extra labels, w further witnesses), Phi'(y) :<=> X_y(Q) nonempty.
  A finite correspondence Z ⊂ Y x A^s is part of the equations of X.
- Honest set `H ⊂ (Y x A^s)(Q)`: honest data plus the labels the honest prover uses; `V' = Zariski closure of H`.
- Soundness notions, for p > p0:
  - LUS: no x in X(Q_p) over Bad_p.
  - label-global: no x in X(Q_p) over Bad_p whose label coordinates lie in A(Q)^s and data labels in A(Q)^m.
  - MW-adelic: no adelic family whose labels come from one element of the closure Zhat P0 + T of A(Q) in A(A_f).
  - global: no x in X(Q) over Bad.
- V' is *t-free* if V' = A^1_t x pr(V') (t algebraically independent of the other coordinates on H).

## Step 2: Theorem GG, statements (proofs in step 3)

Hypothesis (P11): on the slice {labels fixed, q fixed}, B has an odd pole (order 11) along t = c for every
contact c (rv-barrier C5 with arbitrary D_j; E1 below with genuine label coordinates).

- **GG-A (label slicing, local, unconditional).** If X -> Y x A^s has RC generic fibre (R1 of rv-barrier),
  then for honest data labels lab0 and labels L0 in A(Q)^s outside a proper Zariski-closed set there is a
  positive-density set of p and x in X(Q_p) over Bad_p with data labels lab0 and label L0. So the
  globality of L adds nothing to local soundness. (Lemma G' applied to the slice {lab0} x {L0}.)
- **GG-B (explicit completeness => global unsoundness, unconditional).** If V' is t-free and the honest
  non-label witnesses are values of a Q-rational map Lam on V', then X has bad rational points: all
  coordinates honest except t (and Lam). No RC hypothesis.
- **GG-C (RC completeness => global unsoundness under Colliot-Thelene's conjecture).** If V' is t-free and
  X -> V' has RC generic fibre, then CT's conjecture (X(Q) dense in X(A)^Br for smooth proper RC X)
  gives rational bad points close to an honest point at any finite set of places other than p (in
  particular real-close: the Close conjunct still holds). Unconditional where the slice total space has
  weak approximation (e.g. Q-rational with a point; quadric bundles of rank >= 5).
- **GG-D (residual cases).** If V' is not t-free, or X -> V' is not RC, completeness needs per instance a
  rational point on a non-RC variety (column form: a curve of genus >= 1 in (q, L); t-slice through a
  fixed label: a curve of genus >= 2 by Riemann-Hurwitz over the six contacts) or a point of A(Q)^s on
  a proper subvariety H_{n,lab} (a Mordell-Lang intersection). Neither is supplied by holding a label.

## Step 3: E1 (VERIFIED, `e1_slice_pole.py`)

Input: 5 genuine label pairs (n, kappa) in {(2,1),(3,1),(5,2),(-3,1),(4,1)}, h = 2kappa, s0 = 2kappa n,
tests D_j from [h]P0, [s0]P0, [h-kappa]P0, [s0-kappa n]P0 on E/K0 (exact, Fractions), q = 3/7, eta = 1;
6 contacts each: 30 cases. Laurent series in e = t - c.
Outcome: v_e(Theta) = 6 and v_e(B) = -11 in 30/30 cases. So (P11) holds on slices with genuine labels
(rv-barrier C5 had used arbitrary D_j). A first run with (-7,3), (11,1) hit the 600 s cap after 19 cases
(all -11); those pairs were replaced.

## Step 4: E3 (VERIFIED, `e3_nondeep_bad.py`)

Input: t = n integer (n = 271..332), kappa' = 1 (not deep), h = 2, s0 = 2n, eta = sign F(n), q = 0; the
first 30 pairs (n, p) with p > 324, v_p(F(n)) odd. p-adic arithmetic in K0 (x) Q_p, precision p^400.
Outcome: v_p(B) = -11 in 30/30 cases (v_p(F) = 1 in all). So data honest in every coordinate except the
depth of kappa is bad at every odd contact prime > 324. This is the "kappa-deformation" used in GG-B.

## Step 5: E2 (VERIFIED, `e2_mw_sieve.py`)

Input: all primes pi of K0 of norm < 20000, pi not over 2 or 7 (2258 primes: 2240 of degree 1, 18 of
degree 2); m_pi = order of P0 mod pi (PARI nfmodpr + ellorder).
Outcome: fraction with gcd(m_pi, M) = 1: M=2: 0.588; 3: 0.753; 6: 0.446; 30: 0.307; 210: 0.285.
Depth identity v_p(x([k m]P0)) = -2(v_p(k) + r) checked p-adically (precision p^80) at 10 (p, embedding)
pairs, p in {17,23,31,41,47}, k in {1, p, 2p, p^2}: 10/10.
Use (Lemma MW): an obstruction that uses L in Z P0 + T only through local conditions at a fixed finite set
of auxiliary places is a congruence condition on the index k mod a fixed M; depth at a bad pi needs only
m_pi | k (and a p-power), which is compatible by CRT whenever gcd(m_pi, M) = 1, a set of primes of positive
density (Chebotarev in K0(E[l]) for odd l; empirical 0.59 for l = 2). So such soundness is not uniform in
p (rv-barrier N3).

## Step 6: proofs (VERIFIED as proofs from the STANDARD inputs named)

Notation: A' = Zariski closure of A(Q) in A; A'(Q) = A(Q), so labels range over A'. For fixed n the data
labels are morphisms of Q = [kappa]P0: [h]P0 = [2]Q, [s0]P0 = [2n]Q, [h-kappa]P0 = Q, [s0-kappa n]P0 = [n]Q.
(H-mult): for each honest n the honest rule works for all kappa in a finite-index coset of kappa0(n)Z
(kappa0(n) = the deep modulus of exists_common_smul_mem_Ek), at a fixed q0.

- **L1 (rigidity, STANDARD).** Every rational map from a rational variety to an abelian variety is
  constant (Milne, Abelian varieties, Cor. 3.9). Hence A'(Q(t,q)) = A'(Q).
- **L3 (kappa-direction dichotomy).** Fix honest n, q0. W_n := closure of the honest (Q, L, w) over the
  coset Omega_n = (coset of kappa0 Z)P0; W_n -> A' generically finite if the rule is algebraic.
  CDJLZ (Corvaja-Demeio-Javanpeykh-Lombardo-Zannier, Compositio 158 (2022); recalled form: for ramified
  covers Y_i -> A and a Zariski-dense finitely generated Omega in A(k), some finite-index coset of Omega
  misses every pi_i(Y_i(k))) => honest points over a finite-index coset lie on a component W° whose
  normalization is etale over A'; by Serre-Lang (Mumford, Abelian varieties, §18) W° is an abelian
  variety, psi = phi + c with phi an isogeny of degree delta, c in A'(Q). w is constant on W° (proper).
  Non-dominant components and non-geometrically-irreducible ones carry finitely many honest points
  (Faltings / Mordell-Lang for the cyclic group Z P0 in connected A'; geometric irreducibility).
- **Isogeny lifting.** [delta]A'(Q) ⊂ phi(W°(Q)) (phi o phi' = [delta]). If w0 lies over Q0 = [kappa0 j0]P0
  then w0 + phi'([u]P0) lies over Q0 + [delta u]P0. Take u in 1 + m_pi Z: kappa' = kappa0 j0 + delta u is
  not divisible by m_pi when m_pi does not divide delta (true for all but finitely many pi, since each
  m has finitely many pi with m_pi = m). The points {w0 + phi'([u]P0)} form a coset of an infinite cyclic
  group, Zariski dense in W°, so they meet the open V'° where the witness formula satisfies X (V'°
  contains the honest points). By E3 the data (n, kappa') is bad at p. => **GG-B**, unconditional.
- **GG-C.** If the label correspondence involves only data labels (Z ⊂ A'^m x A'^s), freeze an honest
  (lab0, L0) in Z(Q) with P11 on its slice S = A^2_{t,q} x {(lab0, L0)} and S meeting the RC locus.
  X_S -> S RC fibration over a rational base: its smooth proper model is RC (GHS, JAMS 16 (2003), Cor. 1.3)
  and has the honest rational point x_h. Lemma G on S (rv-barrier R2: transversal t-line through a general
  point of {t = c}, GHS section over a number field K, evaluate at t = c + p for p split in K) gives
  x_p in X_S(Q_p) over Bad_p with rational base point. For alpha in Br(X~_S) (finite mod Br Q), alpha is
  constant (= 0) on X~_S(Q_p) for p outside a finite set (Br Z_p = 0). So (x_h at v != p, x_p at p) lies
  in X~_S(A)^Br. Colliot-Thelene's conjecture (X(Q) dense in X(A)^Br for smooth proper RC X; CT 2003)
  gives x in X_S(Q) near x_p at p (still bad: open condition) and near x_h at any finite set of other
  places (in particular real-close: t ~ n). Unconditional if X_S is Q-rational.
- **L4 (twist lemma).** If the honest labels are algebraic over (t, q, lab), apply L3 over the generic
  point of (t, q): under (H-mult) the components carrying honest points are, over Q(t,q), torsors whose
  structure map to A' is phi + c with phi a constant isogeny (finite subgroup schemes of A'[N] over
  Q(t,q) are constant) and c in A'(Q) (L1); the only (t,q)-dependence is a twist class
  xi in H^1(Q(t,q), ker phi). A rational point over Q exists iff xi(t,q) = -delta_phi(Q - c), where
  delta_phi(A'(Q)) is finite and unramified outside a fixed set S_A (weak Mordell-Weil). If xi is
  ramified along a curve {g = 0} then honest (n, q) must lie on the thin set where xi(n,q) is in that
  finite set: the images of rational points of finitely many covers T_i -> A^2_{t,q}. On each T_i the
  labels no longer depend on (t, q) (twist trivial), so the GG-C slice argument runs on T_i whenever
  T_i is rational and {t = c} pulls back with an odd component on a smooth model. Otherwise T_i is
  LUS along the contacts and by Theorem G (column form) its fibre over t = n is a curve of genus >= 1:
  completeness is a per-instance point on a genus >= 1 curve (rv-barrier N1). If xi is ramified along
  {t = c'} only, xi(n) is ramified at every large p with v_p(n - c') odd, so completeness fails for all
  n outside a thin set (this is rs-global C3 in general form).
- **Lemma MW** (step 5) and **Remark H**: the only information in L in Z P0 + T beyond its closure
  Zhat P0 + T in A(A_f) is archimedean (Z is discrete in Zhat x R), i.e. the canonical height
  h^(L) = k^2 h^(P0). Using it needs an upper bound for h^(L) in terms of the data; bad data may carry
  labels of any height (the adversary chooses them), so this is a height hypothesis of SixContactMin's
  kind, not a replacement for CR3.
