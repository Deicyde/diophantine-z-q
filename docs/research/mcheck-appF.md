# mcheck-appF: line-by-line check of Appendix F, odd theta forms and the unaveraged comparison (O.7)

Scope. This report covers tex L8408-9405 of `diophantine_zq.tex`. That is ex:app-theta-form (statement L8408-8429, proof
L8430-9099) and ex:app-theta-comparison (statement L9101-9117, proof L9120-9405). The range comes from the appendix
map, `docs/research/mcheck-rc-app.md` ("Elliot's largest own steps", item 1). For setup I read L8206-8407 (the
definition (O.1), ex:app-detector and (O.2)). For the uses I read L2072-2090, L2440-2560 ((3.7) and (3.8)), L2585-2590,
L9407-9445 ((O.8)) and L10176-10200 ((F.5) and (F.6)).

No network was available. Print locators are quoted as the manuscript gives them. Anything I say about a print from
memory is marked UNVERIFIED. This range contains no Gross-Zagier or TYZ argument. (O.7) is a reduction identity of
Gross type (CM points reduced at an inert prime), not a height formula. CST Theorem 1.1 and Kolyvagin Theorem 1 are not
used in L8408-9405. They enter only next door, in ex:app-detector and in (O.8).

Scripts and their outputs are in `scratch/mcheck-appF/`. All are pure Python. Each one has negative controls: a
deliberately wrong input that must fail, and does.

| script | output | content |
|---|---|---|
| `s1_local.py` | `s1_local.out` | 48/48 PASS: c_0 and v2 c_0 = 9, Minkowski step, nilpotent sign, residue line at l_0, 2-power characters, alpha(-1) bookkeeping, dyadic projectors, the Atkin-Lehner root flip, norm forms and Gram determinants, the dyadic Fourier transform, line counts, nonintegral neighbours, the algebra behind (O.6), the characters psi and eta, the biquadratic discriminant, the orbit count |
| `s2_weil.py` | `s2_weil.out` | 20/20 PASS: Weil indices computed as Gauss-integral phases at v = 2, 3, 5, 7, oo. Checks the index identity, gamma(1)^4, gamma(Q)^2, r_Q cocycle, (O.5a), the W U W scalar, the product formula, (O.5c) and the explicit symbols, the Fourier operator identity (finite model and real place) |
| `s3_toy_theta.py` | `s3_toy_theta.out` | 27/27 PASS: a global model of (O.4), (O.6) and (O.7) on B = (-1,-3) (l_0 = 3, class number one) with h_* = -7 and -31 and P = 1. Uses exactly the tex weights |
| `s4_rootnumber.py` | `s4_rootnumber.out` | 2/2 PASS: w(E) = -prod w_p and w(E^{h*}) = w(E) chi_{h*}(-N), with root numbers computed from L-series (4 curves x 8 twists) |
| `s5_convention.py` | `s5_convention.out` | 4/4 PASS: the classical character is prod alpha_p(d), not its inverse (order-4 character mod 17); theta(m tau) carries (m/d) |

## Conclusion

**This part of Appendix F holds as written, relative to the cited prints and to standard facts about supersingular
reduction. I reached no "error" verdict, so `.fleet/mcheck-appF-verdict.md` was not written.**

- **Every computation, identity and constant in the range checks.** This covers the following:
  - c_0 = |GL_4(F_3)| = 24,261,120 with v2 c_0 = 9, and the Minkowski injectivity argument;
  - all local weights and their conjugation and scaling laws, (O.3), and alpha(-1) = 1;
  - the Weil-index calculus (O.5a)-(O.5c) and the scalars in the operator relations of the double cover;
  - the extracted characters psi = eta_B(m/.), eta = eta_B chi_{h*} and psi/eta = chi_{-1};
  - the local counts behind (O.6) and the passage to (O.6);
  - the orbit count c_0/2 per oriented class-group torsor, 2^{omega(N)+1} tuples, and v2 a_M(D_w) = 9 + omega(N) + c_w.
- **A global model reproduces both (O.6) and (O.7).** It is a weighted ternary theta series with the tex's local
  weights on a class-number-one definite algebra (s3).
  - The recurrence holds on 1,617 (p, n) pairs per case, and fails if s or (-n/p) is altered.
  - H(m) = ±12 h(F), with every orientation contributing the same weight. This is the l_0 sign cancellation of
    L9343-9364.
  - For D > 1, H(mD) = 0, because the genus character sums to zero.
  - The number of supported embeddings is exactly (|R^x|/2) h(F) 2^{omega(N)+1}.
- **No class number is divided out, and none hides in a normalization.** Each oriented tuple contributes an actual
  Pic(O_F)-torsor. The factor c_0/|R_z^x| is an integer, and so is c_0/2.

**Gaps filled (all small, at the level of presentation; each is labelled where it occurs in the table):**

- **F-a**, L9067-9081: moving the neighbour operator onto P_M. I wrote out the step. Write w_i = |R_i^x| and
  theta_j for the weighted theta of class j. Then
  sum_i (1/w_i) P(i) chi(i) sum_j N_ij theta_j = sum_j theta_j (1/w_j) sum_i N_ji P(i) chi(i).
  This uses N_ij/w_i = N_ji/w_j. A neighbour has chi(i) = chi(j) chi_{h*}(p), and sum_i N_ji P(i) = a_p P(j).
  The total is therefore chi_{h*}(p) a_p H(n). The tex states this in two sentences.
- **F-b**, L8579-8592: in the formula for alpha(-1), the final factor (-1) is (-1/l_0). It equals -1 because
  l_0 ≡ -1 mod 2^M with M ≥ 2 (L8437). The tex does not say so at that point.
- **F-c**, L9113 against L9372-9377: (O.7) is printed "mod 2^M". The proof gives the congruence modulo 2^M O, in the
  fixed character ring O. Every use is a 2-adic valuation, and zeta is a unit of O, so this is harmless.
- **F-d**, L9293-9295 and L9324: zeta_M(D) is defined up to chi_F of the reference class, which is a sign. It is still a 2-power
  root of unity in the fixed field, which is all that is used.

**Not checked (marked unverified in the table):**

- **The cited prints.**
  - Cornut-Jetchev, §§3.1-3.3, §3.6, §§4.9-4.10, Thm 3.1, Cor 3.2, Lemma 2.1(ii). This includes its hypotheses
    H.1-H.3 and the "integer 2" in H.2. It is a 2010 preprint cited by URL, which I could not read.
  - Weil, Acta 111: I.13-I.14, II.25-II.30, III Thm 6.
  - Voight, Main Thm 14.6.1 and Prop 14.6.7.
  - Jetchev-Kane, §§1.1-1.2 and 2.5.

  I checked the identities taken from Weil numerically (s2, s5). The content taken from CJ is the standard statement
  that conductor-one CM points reduce at an inert prime equivariantly and bijectively onto oriented optimal
  embeddings, with one l_0-sign. That is consistent with s3, but s3 tests only the quaternion side.
- **Standard facts used without a print.** These are the Hecke and Atkin-Lehner compatibility of
  P_M = lambda_M(L pi_{l_0}(.)) on supersingular points (L8476-8494), and that Frobenius is the right action of the
  division uniformizer.
- **Three structural arguments, read but not computed.** These are holomorphy at the cusps (L8953-8966), uniqueness
  of the normal form for the double cover (L8784-8800), and the lower-unipotent depth argument (L8644-8676).

**Where (O.7) is used, and whether the statement proved is the statement used:**

| use | tex | what is used | matches? |
|---|---|---|---|
| (3.8) | L2522-2534 | the identical formula, for admissible D with (D/l_0) = 1, with c_0 ≠ 0 fixed and zeta a root-of-unity phase; a_M(D) = 0 when (D/l_0) ≠ 1 | yes. The vanishing statement is the l_0 support rule (L8551-8562): Q_B(x) must be a nonzero square mod l_0. (3.8) cites CJ Thm 3.1, as the proof does |
| phase removal | L2081-2084 | zeta is a unit root of unity, so integer representatives at precision 2^{M_theta} | yes (F-c, F-d) |
| (O.8) | L9425 | lower bound for v2 a_M(D) by the native index of P_D; visibility | yes. For (D/l_0) ≠ 1, a_M(D) = 0 and (O.8) holds trivially |
| D = 1 | L2585-2588 via (O.8) | (O.7) at D = 1 (F = Q(sqrt h_*)) | yes. D = 1 is in the filter, and the genus character is trivial (L9189-9190) |
| (F.6) nonempty | L10194 | v2 a_M(D_w) = c_theta + c_w, from (O.2) and (O.7) | yes. This is L9391-9398, with (D_w/l_0) = 1 by (O.2) |

## Table

Verdicts: **OK** (checked), **OK+fill** (checked after a labelled gap fill), **unverified** (not checked; reason
given). "s1:..." points to the check in that script.

### ex:app-theta-form

| tex | step | verdict | reason |
|---|---|---|---|
| 8408-8429 | statement: H_M well defined mod 2^M, g_M in M_{3/2}(Gamma_0(K), psi), psi = eta_B(m/.), eta = eta_B chi_{h*}, (O.6) at all indices, lifts lose no precision, sieves preserve | OK | proved by the rows below; psi/eta = chi_{-1} (s1) |
| 8430-8438 | Fr^2 = 1 on E[2^M]; lambda_M(Fr P) = lambda_M(P); l_0 ≡ -1 mod 4, so (m/l_0) = 1 | OK | bC = b; det C = -1; (m/l_0) = (-1/l_0)(h_*/l_0) = 1 (s1, last check) |
| 8439-8461 | kappa_M(P) = F Q_P - Q_P on E(F_{l_0^2}) is well defined, additive, with kernel 2^M E(k_0), and is an isomorphism onto E[2^M]; Frobenius sign +1; the witness value is the cocycle at sigma^2, so v2 = a+1 | OK | F = 1 on E[2^M]; both groups have order 2^{2M}; Fr acts by C and bC = b; b(1+C)(v + d_tau) = 2b(v) = 2^{a+1} |
| 8462-8474 | B ramified exactly at l_0 and infinity; Eichler order of level N; supersingular pairs over F_{l_0^2} | unverified | Voight 14.6.1 and Jetchev-Kane 1.1-1.2, 2.5 (locators UNVERIFIED); standard (scalar-Frobenius models over F_{l^2}) |
| 8476-8494 | P_M = lambda_M(L pi_{l_0}(.)): T_p-eigenvalue a_p, W_{p^e}-eigenvalue w_{p^e} once L kills pi(W infinity), uniformizer eigenvalue +1 | unverified | standard Eichler-Shimura/Brandt compatibility; pi(Wx) = w pi(x) + pi(W infinity) checked by hand; no print cited |
| 8495-8498 | V = B^0, Q_B = Nrd = -x^2; 1_{R_p^0} at good p | OK | Nrd on B^0 equals -x^2 (s1) |
| 8498-8516 | odd p^e ‖ N: selected root r, integral projectors, (O.3), existence of alpha_p, scaling multiplier alpha_p(u), conjugation-invariance | OK | (x ± r)/(2r) integral at odd p; 2-primary character with alpha(-1) = -1 exists (s1) |
| 8517-8535 | p = 2: e_x = (1+x)/2, projectors (e_x - a')/r and (a - e_x)/r, exactly one is the identity on Z/2^e, e_{ux} = u e_x + (1-u)/2, root becomes ur even when the parities switch | OK | s1: dyadic projectors, idempotents of Z/2^e, parity switch |
| 8536-8550 | p ‖ m: nonzero nilpotent reduction, eps_p(g X_0 g^{-1}) = (det g/p) well defined; conjugation factor (det u/p); scaling factor (u/p) | OK | brute force over GL_2(F_p), p ≤ 11 (s1) |
| 8551-8562 | l_0: residue t beta, weight (t/l_0); a uniformizer gives -1; scaling gives (u/l_0); Q_B(x) = -t^2 beta^2 is a nonzero square, so (D/l_0) = 1 on extracted indices | OK | s1 for l ≡ 3 mod 4; fails for l ≡ 1 mod 4 (negative control) |
| 8563-8578 | supports compact open; f(u^{-1}xu) = chi_{h*}(Nrd u)^{-1} f(x), f(vx) = alpha(v) f(x); the field O is independent of M and l_0 | OK | combines the rows above; chi_{h*,p} restricted to units is (./p) at p ‖ m |
| 8579-8592 | alpha(-1) = (prod w_{p^e} chi(p)^e)(prod_{p‖m}(-1/p))(-1) = w(E^{h*}) = +1; w(E) = -prod w; w(E^{h*}) = w(E) chi_{h*}(-N) | OK+fill | F-b: the final (-1) is (-1/l_0). Formal identity checked in s1; root-number formulas checked from L-series in s4 |
| 8593-8597 | eta_B(d) = prod alpha_p(d) (inverse-idele convention) | OK | argued at L8903-8933 and L8989-9015; tested numerically in rank one with an order-4 character (s5); (O.6) does not depend on it (s = prod_{v≠p} alpha_v(p) is used directly) |
| 8598-8604 | c_0 = 24,261,120, v2 c_0 = 9, definition (O.4) | OK | s1 |
| 8605-8622 | R_z^x embeds in GL_4(Z), reduction mod 3 is injective on finite subgroups, so |R_z^x| divides c_0; independent of representatives; coefficients in O; a lift change of 2^M changes coefficients by 2^M O | OK | binomial argument checked on random matrices (s1); f's conjugation law against chi(Nrd) gives right-invariance; rational norms are positive |
| 8624-8643 | Weil operators: n(b), m(u), Weyl element; n(Z_p) fixes f_p; normalizations e_p, e_oo with product one | OK | product formula holds in this convention and fails in the opposite one (s2) |
| 8644-8676 | Fourier support in (L')^vee, so n^-(p^{A_p} Z_p) fixes f_p; every weight has a translation lattice | unverified | read; standard; not computed beyond the dyadic example in the next row |
| 8677-8687 | Q_0 at 2: dual (1/2)Z_2^3, vol 2^{-3/2}, F(1_{Z_2^3}) = 2^{-3/2} 1_{(1/2)Z_2^3}, depth two | OK | s1 (depth one fails: negative control) |
| 8688-8725 | gamma(ua)/gamma(a) = gamma(u)/gamma(1) (u,a)_p, derived from the index of the quaternion norm form; the diagonal factor is (u, det Q_B); no determinant character for Q_B; (u,m)_p for Q_B/m | OK | s2 at v = 2, 3, 5, 7, oo; the identity without the Hilbert symbol fails. Weil II.25, II.28 locators UNVERIFIED |
| 8726-8771 | operators U_Q, D, W_Q, M_Q; the Fourier formula (Weil I.14 Thm 2); F U(b) F = gamma(bQ) U(-1/b) D(1/b) F^{-1} U(-1/b); gamma(Q)^2 = (det Q,-1) gamma(1)^6, gamma(1)^4 = (-1,-1), r_Q(a) r_Q(b) = (a,b) r_Q(ab) | OK | the operator identity is checked in a finite model (p = 5..13) and at the real place; the scalar identities in s2 |
| 8772-8800 | the relations of the double cover; scalar of the last relation gamma(Q)^2 gamma(bQ)^2 = (-b,-1); one common double cover via normal forms | OK (scalars) / unverified (normal form) | I checked the relations by hand and their scalars in s2 (including gamma_Q^4 = (-1,-1) for W^2). The Bruhat normal-form uniqueness was read only |
| 8801-8816 | Q_0 operators are tensor cubes; the eigenvalue quotient is lift-independent; r_Q(a)/r_{Q_0}(a) = (a, det Q) | OK | s2 (O.5a); the claim without the determinant character fails |
| 8817-8868 | comparison at 2 and the extracted character: triangular factorization, both unipotents trivial, diagonal quotient (O.5a); the inverse convention cancels; the det convention (2A against A) cancels | OK | s2; the convention remarks follow because the Hilbert symbol has order two and squares cancel |
| 8869-8887 | (O.5b) alpha_p(a)(a, det Q)_p for every matrix of the congruence subgroup (multiplicativity via the upper-left entry mod p^{A_p}) | OK | a ↦ upper-left entry mod p^{A_p} is multiplicative on Gamma_0(p^{A_p}) |
| 8888-8902 | det squareclass 1 for Q_B and m for Q_B/m; (u,m)_p = (u/p)^{v_p m}; (u,m)_2 = (-1)^{(u-1)/2}, trivial on 1+4Z_2 | OK | s2 |
| 8903-8924 | eta_B(d) = prod alpha_p(d); (O.5c) prod_{p|2m}(d,m)_p = (m/d); division gives (-1/d) | OK | s2 ((O.5c) without the dyadic factor fails); s1 (psi/eta = chi_{-1}; (m/.) = chi_{4m} is even) |
| 8925-8937 | gamma = n^-(c/a) m(a) n(b/a); classical character eta_B(d), not its inverse; value one at -1 | OK | s5 (order-4 character mod 17: the ratio is chi(d); the conjugate fails); alpha(-1) = 1 above |
| 8938-8952 | no hidden level primes: sl_2(Z_p) is self-dual (det 2), the Weil constant is one, SL_2(Z_p) generated by its standard elements; conjugation by z is an isometry | OK | Gram det = 2 (s1); the generation statement is standard |
| 8953-8966 | Weil III Thm 6 gives invariance; holomorphy at the cusps via finite unions of lattice cosets and positivity | unverified | read; standard; locator UNVERIFIED |
| 8968-8988 | extraction: on the support, Q_B ∈ mZ with v_p = 1 at p | m; Q_B/m is integral; extra character (m/.); (O.5) | OK | s5 (theta(m tau) has (m/d)); s1 characters |
| 8989-9018 | direct check of the inverse convention via g_tau and the product formula for gamma_v and for measures | OK | product formula (s2); the conclusion matches s5 |
| 9019-9038 | extracted coefficients are exactly H_M(mn); measures do not enter the coefficients; no new level prime or dyadic root | OK | direct |
| 9039-9047 | p+1 neighbours = lines; preserved lines 1+(-n/p) (nilpotents included); all p+1 when x ∈ pR_p^0 (excess p) | OK | brute force, p = 3, 5, 7, 11 (s1); 1+(n/p) fails |
| 9048-9058 | nonintegral x = y/p: y̅ is a nonzero nilpotent, p | a, c and p^2 | c; exactly the kernel-line neighbour | OK | brute force mod p^2, p = 3, 5, 7: exactly one neighbour iff p^2 | Q(y) (s1); "iff p | Q(y)" fails |
| 9059-9066 | scaling gives s; nonintegral part s^{-1}H(p^2 n) - H(n); integral part (1+(-n/p))H(n) + p s H(n/p^2); sum | OK | s1 algebra; s3 global model |
| 9067-9082 | self-adjointness N_ij w_j = N_ji w_i; a neighbour changes chi by chi_{h*}(p); hence H(p^2 n) + s(-n/p)H(n) + p s^2 H(n/p^2) = s chi(p) a_p H(n) | OK+fill | F-a written out above; the global model (P = 1, a_p → p+1) satisfies it on 1,617 pairs per case (s3) |
| 9083-9093 | (O.6) with eta(p) = s chi(p), psi(p) = s(m/p), eta^2 = s^2; covers p | n and p^2 | n; zero and negative indices vanish | OK | s1 (psi(p) a_p fails); s3 |
| 9094-9099 | sieves preserve (O.6) outside the enlarged support | OK | p^2 n, n and n/p^2 share their status under conditions at other primes |

### ex:app-theta-comparison

| tex | step | verdict | reason |
|---|---|---|---|
| 9101-9117 | statement (O.7): H_M(mD) = c_0 2^{omega(N)} zeta_M(D) lambda_M(L P_D bar) mod 2^M for admissible D with (D/l_0) = 1 | OK+fill | F-c (mod 2^M O), F-d (zeta up to sign); proved by the rows below relative to the unverified CJ input |
| 9120-9135 | Q_B(x) = mD ⇔ x^2 = D h_*; with the 2-adic and other conditions, O_F → R_z is an optimal embedding (O_F maximal); all weights nonzero on embeddings | OK | -x^2 = mD; Dh_* ≡ 1 mod 8 (F split at 2), so x^2 is a unit square; v_p(mD) = 1 at p | m; residue nonzero at l_0 (s3 support count = 12 h(F)) |
| 9136-9149 | local orientations: one away from N l_0; two at p^e ‖ N (including 2); two at l_0; total 2^{omega(N)+1} | OK | standard local embedding numbers (1 + (d/p) = 2 split at p | N; 1 - (d/l_0) = 2 at the inert ramified prime); s3 confirms the factor 2 at l_0 (the count 6 h(F) fails) |
| 9150-9170 | rational embedding exists (Voight 14.6.7 (v)⇒(iii)); fixed tuple = F^x \ F̂^x z_0 R̂^x / R̂^x = Pic(O_F), an actual torsor | OK (math) / locator UNVERIFIED | Skolem-Noether and local conjugacy; optimality gives F̂^x ∩ z_0 R̂^x z_0^{-1} = Ô_F^x |
| 9171-9194 | f constant along the torsor (a centralizes x_0); chi(Nrd(a z_0)) = chi_F(a) chi(Nrd z_0); the genus character is unramified because the biquadratic discriminant is (Dh_*)^2; D = 1 gives the trivial character | OK | s1 (conductor-discriminant; D ≡ 3 mod 4 fails); s3 (D > 1 weights split evenly, D = 1 constant) |
| 9195-9264 | CJ specialization: F_CJ = Q, K_CJ = F, B_CJ = M_2(Q), S = {l_0}; H.1-H.3 (inert case); H = R̂_src^x, H_S = R̂^x; fine conductors 1; kappa = 1; sign fibre at l_0; Thm 3.1 and Cor 3.2 give an equivariant bijection onto one sign component | unverified | CJ preprint not available offline; hypotheses and the "integer 2" UNVERIFIED. The arithmetic I could check holds: (Dh_*/l_0) = -1 (s1), fine-conductor argument, F_{l_0}^x \ B_{l_0}^x / R_{l_0}^x ≅ Z/2 via v(Nrd) mod 2 |
| 9265-9296 | CJ §§4.9-4.10 identify the adelic map with geometric reduction; sum_a chi_F(a) P_M(z_a) = lambda_M(L P_D bar); Artin-convention and reference-point changes harmless | unverified (citation) / OK (bookkeeping) | additivity and specialization commute with the finite sum; chi_F quadratic; reduction lands in E(F_{l_0^2}) because l_0 is inert in F and splits completely in H/F |
| 9297-9307 | weights constant on R_z^x-orbits (units have norm 1); single phase chi(Nrd z_0) f(z_0^{-1} x_0 z_0) | OK | conjugation law with Nrd u = 1 |
| 9308-9328 | stabilizer O_F^x = ±1, orbit size |R_z^x|/2, so 1/2 per embedding class; x and -x lie in different l_0 tuples; reference contribution (c_0/2) zeta lambda_M(L P_D bar); zeta is a 2-power root of unity in the fixed field | OK+fill | F-d; s1 orbit arithmetic; s3 (12 = (|R^x|/2) · 2 at h(F) = 1, all weights equal) |
| 9329-9342 | Atkin-Lehner normalizer at p^e ‖ N reverses the root (weight alpha_p(-1)), and multiplies the norm-weighted value by w_{p^e} chi(p)^e; the product is 1 by (O.3) | OK (algebra) / unverified (P_M(zW) = w P_M(z)) | root reversal checked on the Eichler order [[Z,Z],[p^e Z,Z]] (s1; "preserves" fails); the AL eigen-relation of P_M is the standard fact in the L8476-8494 row |
| 9343-9364 | uniformizer at l_0 exchanges residue embeddings: weight (-1/l_0) = -1, norm chi_{h*}(l_0) = -1, P_M unchanged (Frobenius sign +1); product 1 | OK | s3: with l_0 = 3 all orientation weights are equal at D = 1 (|H(m)| = 12 h(F)) |
| 9365-9377 | all 2^{omega(N)+1} tuples contribute equally, giving c_0 2^{omega(N)}; no extra factor of two; c_0/|R_z^x| integral, so no precision loss | OK | s1 (c_0/4 per orbit fails); s3 count |
| 9378-9390 | precision: c_0/2 is an integer since -1 ∈ R_z^x; each orbit contributes (c_0/2) P_M(z); summing at precision M | OK | s1 |
| 9391-9405 | c_theta = 9 + omega(N); v2 a_M(D_w) = c_theta + c_w when M > c_theta + c_w | OK | zeta is a unit; v2(c_0 2^w) = 9 + w (s1); v2 lambda_M(Q bar) = c_w by (O.2) |

## Known issues

- **K1 (cited prints, UNVERIFIED).** The steps resting only on prints are marked unverified. The ones that carry
  weight are:
  - Cornut-Jetchev Thm 3.1, Cor 3.2, §3.6 and §§4.9-4.10, with S = {l_0}. This is the only input to the identity
    sum_a chi_F(a) P_M(z_a) = lambda_M(L P_D bar). As I recall, without the print, the content is standard. Gross's
    1987 description of reduction of CM points at an inert prime gives the same equivariant bijection (UNVERIFIED
    locator).
  - Weil, Acta 111, III Thm 6 (theta invariance), and I.14 Thm 2. The identities themselves were checked
    numerically.
- **K2 (standard facts used without a print).** These are the Hecke, Atkin-Lehner and Frobenius compatibility of
  supersingular reduction (L8476-8494, L9329-9364). They are standard. The tex gives the key line
  pi(Wx) = w pi(x) + pi(W infinity), with L killing the cuspidal term.
- **K3 (scope of the global model).** s3 uses N = 1, l_0 = 3, class number one and P = 1 (the Eisenstein vector). It
  therefore tests:
  - the local counts;
  - the weights and their signs, including the l_0 orientation cancellation and the genus pattern;
  - the factor (|R^x|/2) · 2^{omega(N)+1}.

  It does not test level-prime orientations, a nonconstant P, or the CJ reduction identity. The level-prime sign is
  covered by the algebraic AL check in s1 together with (O.3).
- **K4 (presentation).** F-a to F-d above. None changes a statement.
- **K5 (inherited).** The editorial comments at L8222-8223 and L8407 ("baseline", "completion audit") remain; see
  mcheck-rc-app K6.
