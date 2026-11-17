# mcheck-rc-app: Appendices E-G of the manuscript mapped; updated conclusion on Theorem 5.3 (hyp:RC)

Scope. This report covers Appendices E (app:even-source, tex L6825-8205), F (app:odd-source,
L8206-9980) and G (app:endpoints, L9981-10935) of `diophantine_zq.tex`. I read them once in full, in
order. They extend the map of sections 7-9 in `docs/research/mcheck-rc-map.md`, whose rows are not
repeated here. No network was available. Print locators are quoted as the manuscript gives them, and
anything I say from memory about a print is marked UNVERIFIED. Arithmetic spot checks are in
`scratch/mcheck-rc-app/checks.py`, with output in `checks.out` (15/15 PASS).

## Conclusion (updated)

**With the appendices mapped, Theorem 5.3 follows, as far as the map shows, from the cited prints plus
Elliot's own steps. I reached no "error" verdict, so `.fleet/mcheck-rc-app-verdict.md` was not
written.** Every statement that sections 7-9 take from Appendices E-G is proved there by an argument
whose inputs are either earlier results of the manuscript or cited prints. The order of choices
(L9981-9994, L10151-10256, L10813-10861) is not circular:

- the even source (App E) and the rough companion come first;
- then the genus lower bound (F.4);
- then the odd minimum delta_o (F.5)-(F.7);
- only after that the odd coefficient rules, the address constructions and the final family (3.9).

This is a statement about the logical structure and about the algebra I could check. Elliot's large own
constructions in the appendices were read once for structure, not verified line by line. These are the
Weil-representation calculus (L8623-8960), the homological-perturbation models (L7386-7425), the
Kummer-duality length bookkeeping (L7631-7787) and the network degree count (G.1a).

### How the appendices feed the skeleton of mcheck-rc-map

1. **(3.2) and (3.3)**, the even side. App E builds one retained-smoothed Kato class Z_F for the whole
   family ((K1)-(K3)). The positive-complex scalar u^ev comes from it ((E.3)-(E.5)). Its central
   calibration (E.8) is v2 u_h^ev(0) = v2 L_*(h) - 2 omega(h) - s(h) + O(1). The -2 omega(h) is exactly
   the length-2 inertia invariants E[2] at each active prime, the BSD-shaped count. This gives the
   lower bound (E.9). Waldspurger's Cor 2 turns this into the weight-3/2 even form with
   a(D)^2 proportional to L_*(sigma D) ((E.10)-(E.11)), which has a finite minimum of v2 a(D) - omega(D).
   App G then gives the upper transfer (F.1)-(F.3) through the one-symbol address cube and the
   Boolean comparison of section 9.
2. **(3.8) and (O.8)**, the odd side. App F builds a fixed witness D_w and Chebotarev stages (O.2). It
   builds the actual ternary theta form g_M ((O.4)-(O.6)) on the definite algebra ramified at l_0 and
   infinity. Via Cornut-Jetchev's reduction map with S = {l_0}, it proves the exact unaveraged
   comparison (O.7): H_M(mD) = c_0 2^{omega(N)} zeta lambda_M(L P_D) mod 2^M, with v2 c_0 = 9 and
   2^{omega(N)+1} orientation tuples each contributing c_0/2. Visibility (O.8) follows. The
   arithmetic coefficient rules (O.9)-(O.12) realize the omission, contraction and isolation rules of
   ex:sec7-coefficient-rules.
3. **Odd minimum and the final family.** (3.4)+(3.5)+(F.3) give (F.4), hence (F.5). The ultrafilter
   minimum delta_o is attained ((F.6)), so a unit gives (F.7). App G's nonempty-seed proposition then
   gives the even K-split seed through an explicit mod-8 computation (H[p^3] = eta^2 (a_p - 1)(a_p - p
   - 1)/4, checked). That computation is specific to E_l (2-primary part of E_l(F_p) of order exactly 4).
   It also isolates branch 1: an odd unit at the empty configuration gives RC directly. The network
   construction (G.1a) produces the binary family (3.9) at one actual theta stage. L10862-10935
   restates the final contradiction of section 9, with the same constants as L5666-5735.

### Cited prints used by the appendices (locators as the manuscript gives them; all UNVERIFIED)

| print | statement used | where |
|---|---|---|
| Kato, Asterisque 295: (8.1.3) p.180, §8.2 pp.180-181, §§8.9, 8.11, (4.2.4) p.143, Thm 6.6 p.163, Prop 8.12 p.186, Thm 9.7 p.189, (12.2.1)-(12.2.3) p.220, §13.1 pp.224-225, Thm 13.4(1),(2), Thm 13.5(2), §§13.6-13.7 p.227 | retained-smoothed zeta classes; norm relations; explicit reciprocity (dual exponential = L-value with smoothing factor); finiteness of zero L-values; Euler-system divisibility at height-one primes (rational hypotheses only; part (3) not used) | L6890-7245 |
| Stacks Project Tags 03Q9, 03QA | higher direct image stalks, Leray: integral j_* condition | L6962 |
| Nekovar, Selmer complexes: Cor 4.1.3 p.96; 5.7.1.4-5.7.1.7 | lim^1 vanishing; orthogonal-Kummer Poitou-Tate sequence | L7079, L7696 |
| Waldspurger, JMPA 60: Prop 2 (§I.2 p.377), §I.3 pp.377-378, Prop 18 and proof pp.466-467, Cor 2 pp.483-484; Waldspurger, ICM 1983: Thm 1, Prop 1 | nonzero D_0-Whittaker member of the packet; unramified coefficient 1; the squarefree coefficient-square identity for a same-2-adic-squareclass pair, without (H2) | L7832-8010 |
| Ramsey, Ann. Inst. Fourier 56: Def 3.1, Thm 4.2, Rem 4.4 | algebraic section model for weight 3/2, used only over fields | L8042, L8064 |
| Dokchitser-Dokchitser, Crelle 658, Thm 1.8 | 2-parity: w(E) = -1 | L8249 |
| Bump-Friedberg-Hoffstein, Invent. 102, clauses (i), (ii) pp.543-544 | h_* < 0 with L(E^{h_*},1) != 0; D_w > 0 with L'(E^{D_w},1) != 0 | L8251-8260 |
| **Cai-Shu-Tian, ANT 8, Thm 1.1** | conductor-one unaveraged height formula: P_{D_w} nontorsion (L8269-8276); odd-sign D not a simple zero gives a torsion genus point, and a visible coefficient gives a simple zero ((O.8), L9437-9444) | L8269-8276, L9407-9445 |
| Serre, Invent. 15 | non-CM open image (central scalar, irreducibility; condition (v) of Kato 13.4) | L8319 (and, uncited, Kato condition (v) at L7228-7232) |
| Voight, *Quaternion algebras*: Main Thm 14.6.1, Prop 14.6.7 | existence of B ramified at l_0, infinity; F embeds in B | L8462, L9154 |
| Jetchev-Kane, arXiv:0908.3905, §§1.1-1.2, 2.5 | supersingular-pair and adelic descriptions | L8474 |
| Weil, Acta 111: I.13-I.14, II.25-II.30 (Prop 4, Prop 5), III Thm 6 (III.41) | Weil representation operators, Weil index, rational theta invariance | L8626-9008 |
| Cornut-Jetchev, 2010 preprint: §§3.1-3.3, 3.6, Thm 3.1, Cor 3.2, Lemma 2.1(ii), §§4.9-4.10 | equivariant bijection of the Pic(O_F)-torsor of CM points onto supersingular points with one sign fiber at S = {l_0}; identification with geometric reduction | L9197-9266 |
| Carayol, Ann. ENS 19: §§0.3-0.7, Thm A pp.409-411 | local-global compatibility at a conductor-one prime (normalization of rho_f) | L9778 |
| Casselman, Math. Ann. 201: Thm 1 pp.302-306, Cor p.306, Thm 4 p.313 | conductor-one representations are principal series with one ramified character; newvector line | L9803, L9860 |
| Hoffstein-Luo, MRL 4, p.436 | central nonvanishing with at most four prime factors and an arbitrary finite splitting set | L9995-10053 |
| lem:forward-rank (Kolyvagin Thm 1; Kato Cor 14.3), as in mcheck-rc-map | analytic rank 0 or 1 gives rank and finite Sha | L7624-7627, L7781-7783, L8272, L10111, L10279 |

### Elliot's largest own steps in the appendices

1. **Odd theta forms and the unaveraged comparison** (App F, L8408-9405, about 1,000 lines).
   - The weighted ternary theta series on the definite algebra, its exact transformation law
     (Weil-index calculus including p = 2, extraction by Q_B/m) and the all-index Brandt recurrence
     (O.6).
   - The orientation count giving c_0 2^{omega(N)} in (O.7).
   - Hard. Checked: (O.6) from the H-recurrence, c_0 and v2 c_0 = 9, the alpha(-1) = 1 sign
     bookkeeping, and the count 2^{omega(N)+1} times c_0/2. The Weil-index identities are standard but
     were not re-derived.
2. **Kato-system construction with uniform constants** (App E, L6846-7356, about 510 lines).
   - One class for the whole family; smoothing c = d_s = 1 + 2^e 3 N_odd F with v2 s_F = 2e (checked).
   - An integral j_* condition that survives ramified corestriction (Mackey).
   - The central normalization (K14), which has no phi(D) or 2^{omega} factor.
   - The height-one divisibility (K2), with the full-H^2 correction (K16).
   - Hard. This is the even analogue of K3 (no omega-dependent factor), and the text argues it
     explicitly (L7150-7170, L7350-7356).
3. **Coefficient rules** (App F, L9446-9976, about 530 lines).
   - Integer divisions (O.9)-(O.11) (shell parities checked).
   - A closed integral trace module.
   - The local identity (O.12) at a conductor-one prime (matrix identity checked).
   - The omission, isolation and graph-dependence rules.
   - Medium to hard.
4. **Positive complex and central calibration** (App E, L7367-7787, about 420 lines).
   - (E.3) uses the triviality of the 2-class group of Q(zeta_{2^n})^+ and a unit of norm -1. The
     odd count of negative conjugates was checked for m <= 15.
   - The length bookkeeping (E.6)-(E.8).
   - Medium to hard.
5. **Address constructions** (App G, L10554-10790, about 240 lines). Grounded-Laplacian network
   operators over F_2, and a combinatorial-nullstellensatz-type degree count for two symbols at once.
   The F_2 linear algebra of the singular and varying networks was checked for b <= 6. The degree count
   was read but not re-derived. Medium.
6. **Nonempty seed** (App G, L10274-10500, about 230 lines). Transport of the even source to E^k, plus
   the mod-8 contradiction. All displayed coefficient formulas were checked, and so was the order-4
   claim (1,028 pairs (l,p)). Medium.
7. **Ultrafilter odd minimum and table stabilization** (App G, L10151-10256, L10508-10552). Bookkeeping
   that avoids circularity. Medium.

### Every GZ/TYZ contact point (whole proof, now including the appendices)

There is no TYZ argument and no TYZ citation in sections 7-9 or in Appendices E-G. A grep for tyz,
Tian-Yuan-Zhang and Tian finds only the CST bibliography entry. GZ enters only through printed
statements. Contacts G1-G6 are as in mcheck-rc-map. The appendices add no new kind of contact; they
locate G2 and G3 precisely:

| # | tex | contact | kind |
|---|---|---|---|
| G1 | L2427-2439 (3.4); used again in (F.4) L10173-10178 and at L10870-10874 | CST Thm 1.1 applied twice (genus point and ring-class point), with a ratio of the two outputs | cites a print, plus about 10 lines of Elliot's own comparison. Quantitative: needs the exact c-dependence (item K3 below) |
| G2 | L8269-8276 (ex:app-detector) | CST Thm 1.1 at conductor one: L'(E^{(D_w)},1) L(E^{(h_*)},1) != 0, so P_{D_w} is nontorsion | cites a print; qualitative only |
| G3 | L9437-9444 ((O.8), "the height formula"); used at L2593-2599 (branch 1), (F.5)-(F.7), L10845-10850 | CST Thm 1.1 at conductor one: an odd-sign D that is not a simple zero has a torsion genus point; a nontorsion point gives L'(E^D,1) != 0 | cites a print; qualitative only |
| G4 | L4337-4339 (ex:arith-base-zero) | "conductor-one height formula": L'(E/K,1) = 0 makes the Heegner point torsion | cites a print; qualitative only |
| G5 | lem:forward-rank; in the appendices at L7624-7627, L7781-7783, L8272, L10111, L10279 | Kolyvagin Thm 1 / Kato Cor 14.3 | cites a print |
| G6 | sec 8-9 (L2834-3393, L4747-5205) | Kolyvagin-style derivative classes and switches | Elliot's own argument, not a GZ formula |
| (G7) | L9197-9266 | Cornut-Jetchev reduction map: CM points to supersingular points | cites a print. It is a Gross-type "special points" bijection, not a height formula; no GZ or TYZ argument is involved |

No step was found that needs a GZ or TYZ argument beyond a print. G2-G4 use only the qualitative
direction (height zero if and only if the derivative vanishes) and are insensitive to the constants.
G1 is the only quantitative use; K3 below sets out exactly what it needs.

## Appendix map

Columns: tex lines | label | claim | kind | size (lines) | depends on | GZ/TYZ contact | used in.
"Own" means Elliot's own argument. Print locators are as the manuscript gives them; none was checked
against a print (no network).

### Appendix E (app:even-source), tex L6825-8205

| tex | label | claim | kind | size | depends on | GZ/TYZ | used in |
|---|---|---|---|---|---|---|---|
| 6825-6845 | (intro, setup) | E fixed; Lambda=Z_2[[t]] real cyclotomic, A=Lambda[1/2]; arithmetic Frobenius | own (conventions) | 21 | sec 7 setup | none | - |
| 6846-6889 | ex:app-kato-system (statement) | one retained-smoothed class Z_F (K1) for the whole family with fixed denominator 2^{c_E}; one F_E in Lambda, F_E(0)!=0, with height-one divisibility (K2); central reciprocity (K3): v2 exp*(F_E(Z_F)_x(0)) = v2 L_*(h) + sum_{q|F, q not dividing h} v2 #E^h(F_q) + 2e + v2 F_E(0) + eps_h, eps_h bounded | own construction on Kato's Euler system | 44 | Kato (below) | none | ex:sec7-even-scalar (L1825-1966), ex:app-even-scalar |
| 6890-6985 | (proof par. 1-3) | fixed symbol combination xi with both Betti projections nonzero; smoothing c=d_s=1+2^e 3N_odd F (K5), central scalar s_F with v2 = 2e (K6); integral j_* condition survives ramified corestriction (Leray + Mackey (K7)) | cites Kato (8.1.3) p.180, 8.9, 8.11, 13.6-13.7, (4.2.4), Thm 6.6; Stacks Tags 03Q9, 03QA; own Mackey argument | 96 | - | none | (K1) |
| 6986-7040 | (proof par. 4) | primitive twisting y_m = cor(z_{Dm} (x) e_chi) (K8) is an Euler system with factor (K9) E_q = P_q(q^{-1} sigma_q^{-1}); discriminant 4h covered by repeated-two norms | cites Kato Prop 8.12, 13.1 pp.224-225; own | 55 | par. 3 | none | (E.1), (K2) |
| 7041-7099 | (proof par. 5) | coefficient map Phi_n (K10) is integral and equivariant; one class Z_F; exact identity (E.1) (Z_F)_x = prod_{q|F/d} E_q(chi_x) y_{2^inf}; (E.2) dyadic character in module action | own; cites Nekovar Cor 4.1.3 p.96 (lim^1) | 59 | par. 4 | none | (K1), (K3) |
| 7100-7202 | (proof par. 6) | central trace (K12) = unnormalized chi-sum; Kato Thm 6.6 + 9.7 give (K13) per_f = s_F L_{prime(2Nd)}(f,chi,1) b_eps e_B; descent via basis sqrt(h) e_chi gives (K14) s_F b_eps L_*(h)/h times omitted 2N factors; no phi(D) or 2^{omega} factor; E_q(0) = #E^h(F_q)/q | cites Kato Thm 6.6 p.163, Thm 9.7 p.189; own normalization | 103 | par. 5 | none | (K3) |
| 7203-7245 | (proof par. 7) | hypotheses of Kato 13.4(2) verified: generic sign components nonzero (via Kato 13.5(2) finiteness of zero L-values), rank-one eigenspaces, w=-1, irreducibility, open image condition (v); gives (K15); H^1_p free of rank one | cites Kato Thm 13.4(1),(2), 13.5(2), (12.2.1)-(12.2.2); Serre open image | 43 | par. 6 | none | (K2) |
| 7246-7356 | (proof par. 8-9) | cone (K16) from j_* to full cochains: D_q = E_q at inactive good, 1 at active good; F_2 (local at 2) and F_bad with F_E(0)!=0; length chain proves (K2); uniformity | own; Kato (12.2.3) p.220; local duality | 111 | par. 7 | none | (K2) |
| 7367-7385 | ex:app-even-scalar (statement) | positive complex C^+ (fiber of ordinary global to real cochains) has C^+ (x) B = B^2[-1] over B = O[G]; scalar u^ev in Lambda[1/2][G] with 2^{c_E} u^ev in Lambda[G], c_E independent of G | own | 19 | ex:app-kato-system; E[2](Q) = (Z/2)^2 | none | ex:sec7-even-scalar, (3.2) |
| 7386-7425 | (proof: finite free models) | continuous cochains over Artin quotients have compatible minimal finite free models; inverse limit of acyclic cones acyclic | own (nilpotent perturbation, Nakayama, Mittag-Leffler) | 40 | - | none | also sec 9 inner limit (L4391-4456) |
| 7426-7497 | (proof: residual positive complex) | 2-class group of K_n = Q(zeta_{2^{n+2}})^+ trivial (induction via unique dyadic prime); unit u = 1+zeta+zeta^{-1} has norm -1, signatures span; dim H^1(C_n^+) = 2^n+s_n-1, dim H^2 = s_n-1; hence generic rank one in degree one; (E.3) C^+ (x) B = B^2[-1] | own (classical; Weber-type parity argument) | 72 | Kummer theory, Brauer group | none | (E.3), (E.5) |
| 7498-7540 | (proof: (E.4)) | real invariant generator a, positive lift b of 2^{c_E+1} F_E Z_F; u^ev theta = 2^{-c_E} a wedge b = 2 a wedge z~ (independent of lift) | own | 43 | (E.3), (K1) | none | (E.7), (3.2) |
| 7541-7612 | (proof: (E.4a), (E.5)) | v_p(u_x^ev) = l(H^1/Rz) - l H^2 >= 0 at height-one p by (K2); so u^ev in A[G]; with (E.3) gives 2^{c_E} u^ev in Lambda[G] (E.5), no v2 abs(G) loss | own | 72 | (K2), (K16), (E.3) | none | (3.2), ex:sec7-even-upper |
| 7613-7630 | ex:app-central-calibration (statement) | at corank-0 constituent with finite Sha: v2 u_h^ev(0) = v2 L_*(h) - 2 omega(h) - s(h) + eps_h, abs(eps_h) <= C_loc; zero iff L_* = 0; hence (E.9) v2 L_*(h) >= 2 omega(h) + s(h) - c_E - C_loc whenever L_*(h) != 0 | own; uses lem:forward-rank | 18 | (E.4), (K3), lem:forward-rank | via lem:forward-rank (rank-0 case: Kato Cor 14.3 / Kolyvagin Thm 1, cited prints) | (3.2), (3.3a), ex:app-even-phase minimum |
| 7631-7787 | (proof) | Kummer-duality length formula (E.6); wedge and inverse determinant bookkeeping give (E.7) v2 u_h^ev(0) = v2 exp* z - s(h) - sum_v g_v + 2g + 1 - r_1 - e_2; real Kummer complex U_R; Selmer cone with H^2 length s(h); unused-prime terms v2 #E^h(F_q) of (K3) cancel against g_q; active good primes give g_q = 2 each, hence -2 omega(h) (E.8) | own; cites Nekovar 5.7.1.4-5.7.1.7 (Poitou-Tate) | 157 | (K3), (E.4) | none | (E.8)-(E.9), (3.2) |
| 7788-7811 | ex:app-even-phase (statement) | weight-3/2 cusp form g, a(D_0)=1, characters psi, eta with psi/eta = chi_{-sigma}; a(D) = z_D r_D, z_D a 2-power root of unity, r_D rational, r_D^2 = L_*(sigma D)/L_*(sigma D_0); recurrence (E.12); v2 a(D) - omega(D) has an attained minimum, fixed before later exclusions | own construction; Waldspurger | 24 | (E.9) | none (Waldspurger is not GZ/TYZ) | (3.3a), even symbol ex:sec7-symbol (L2006-2070), common family L2553-2575 |
| 7812-7934 | (proof: reference functional, local types) | nonzero D_0-Whittaker functional in the Shimura-Waldspurger packet of E^(sigma); local projection w = alpha-eigenvector with l(w) = 2 vol(K_R) l(v) != 0; scalar K_0 type; psi(-1)=1; support idempotent Pi_A; unramified c_p^0 = 1 at valuations 0, 1 | cites Waldspurger ICM Thm 1, Prop 1; Waldspurger JMPA Prop 18 and proof pp.466-467, sec I.3 pp.377-378; own local calculation | 123 | - | none | (E.10) |
| 7935-8020 | (proof: full-space comparison, (E.10)) | Waldspurger Cor 2 (pp.483-484) with k=3, chi=psi, chi_0 = psi chi_{-1}, n_1 = D_0, n_2 = D: a(D)^2 = psi(D/D_0) sqrt(D) L(E^(sigma D),1)/(sqrt(D_0) L(E^(sigma D_0),1)) a(D_0)^2; (H1) from Prop 2 p.377; (H2) not needed because D/D_0 is a 2-adic square (final paragraph p.484); proportionality on the whole eigenspace | cites Waldspurger JMPA Cor 2, Prop 2 | 86 | - | none | (E.11) |
| 8021-8130 | (proof: algebraic vector, Galois) | Ramsey's section model (Def 3.1, Thm 4.2; Rem 4.4) gives an algebraic g with a(D_0)=1 by flat field extension; elliptic eigenspace orthogonal to unary theta (eigenvalue bound); tau(a(D)) = nu(D/D_0) a(D), so a(D)/z_D rational (E.11) | cites Ramsey; own Galois argument | 110 | (E.10) | none | (E.11) |
| 8131-8205 | (proof: recurrence, minimum) | sieve B; T(p^2) recurrence (E.12) a(p^2 n) = {eta(p) a_p - psi(p)(-n/p)} a(n) - p eta(p)^2 a(n/p^2); closed form a(D m^2) = z_D eta(m) r_D prod A_{p,r}(D) with integer A_{p,r}; minimum of v2 a(D) - omega(D) exists by (E.9) + (E.11) | own (standard Shimura T(p^2) formula) | 75 | (E.9), (E.11) | none | ex:app-coefficient-rules, ex:sec7-coefficient-rules |

### Appendix F (app:odd-source), tex L8206-9980

| tex | label | claim | kind | size | depends on | GZ/TYZ | used in |
|---|---|---|---|---|---|---|---|
| 8206-8221 | (intro, (O.1)) | admissible D; K_D = Q(sqrt(D h_*)) imaginary, split at 2N, units +-1; unaveraged conductor-one genus point P_D = sum chi_{h_*}(N a) pi(x_D^[a]) (O.1) | own (definition) | 16 | sec 7 setup | none | (3.8), (O.7) |
| 8224-8248 | ex:app-detector (statement) | h_* < 0 odd with L(E^{h_*},1) != 0; D_w > 0 with L'(E^{D_w},1) != 0; fixed L with L P_D in the D-twist line and Q = L P_{D_w} nontorsion; stages (M, l_0, lambda_M) with v2 lambda_M(Q bar) = c_w < M fixed, Fr^2 = 1 on E[2^M], (D_w/l_0) = 1, (h_*/l_0) = -1, Frobenius sign +1 | own | 25 | DD, BFH, CST | cites a print (CST 1.1) | (3.7), (3.8), L2460-2551 |
| 8249-8268 | (proof: witness choice) | root number -1 by [dd, Thm 1.8]; BFH clause (ii) gives h_*, clause (i) gives D_w (pp.543-544) | cites DD Thm 1.8; BFH pp.543-544 clauses (i),(ii) | 20 | corank-1 hypothesis | none | - |
| 8269-8276 | (proof: P_{D_w} nontorsion) | P_D in E(F_D), F_D = Q(sqrt D, sqrt h_*); h_*-component rank 0 (forward rank-zero theorem); CST Thm 1.1 at conductor one: Rankin derivative L'(E^{(D_w)},1) L(E^{(h_*)},1) != 0, so P_{D_w} nontorsion | cites CST Thm 1.1 (conductor one; all primes of N split; extra units excluded) and lem:forward-rank | 8 | witness choice | **G2: cites a print (CST 1.1)**; forward rank-0: Kato/Kolyvagin print | Q nontorsion, (O.2) |
| 8277-8309 | (proof: multiplier L) | B = prod_{j,f<=4} #E(F_{p_j^f}) kills torsion over fields of degree <= 4; B_cusp kills cuspidal images (Atkin-Lehner translates); integral operator 4 e_D; L multiple of 4 B B_cusp makes L P_D a rational point of E^(D) | own | 33 | (4.1) cuspidal constant | none | (O.4), (O.7), (O.8) |
| 8310-8370 | (proof: Kummer image, sigma) | Kummer cocycle c_Q nonzero on H = ker rho_A by open image (central scalar z != 1); its span contains 2^a T; sigma = h tau with rho(sigma) = C, b c_Q(sigma^2) = 2^{a+1}; c_w = a+1 | own; cites Serre open image | 61 | Q nontorsion | none | (O.2) |
| 8371-8405 | (proof: stages, (O.2)) | Chebotarev primes l_0 with Fr = C mod 2^M, l_0 == -1 mod 2^M; kappa_M(P) = F^2 R - R onto E[2^M]; lambda_M = b kappa_M has Frobenius sign +1; v2 lambda_M(Q bar) = c_w (O.2) | own (Chebotarev) | 35 | sigma | none | (O.7), visibility at D_w |
| 8408-8429 | ex:app-theta-form (statement) | with c_0 = abs(GL_4(F_3)) = 24,261,120, H_M (O.4) is well defined mod 2^M; g_M = sum H_M(mn) q^n in M_{3/2}(Gamma_0(K), psi), psi = eta_B (m/.), eta = eta_B chi_{h_*}, psi/eta = chi_{-1}; recurrence (O.6) at all indices | own | 22 | ex:app-detector | none | (3.8), odd symbol, ex:app-coefficient-rules |
| 8430-8473 | (proof: finite-field map, supersingular set) | kappa_M iso E(k_0)/2^M -> E[2^M]; B ramified at l_0, infinity (Voight Main Thm 14.6.1); Eichler order of level N; supersingular pairs over F_{l_0^2} (Jetchev-Kane 1.1-1.2, 2.5); P_M(z) = lambda_M(L pi_{l_0}(z)) has Hecke eigenvalues a_p, Atkin-Lehner w_{p^e}, uniformizer +1 mod 2^M | own; cites Voight, Jetchev-Kane | 44 | (O.2) | none | (O.4) |
| 8474-8598 | (proof: local Schwartz functions, (O.3), (O.4)) | local weights at p | N (root character alpha_p with (O.3) alpha_p(-1) = w_{p^e} chi_{h_*}(p)^e), at 2 (integral projectors), at p | m (nilpotent sign), at l_0 ((t/l_0)); alpha(-1) = 1 using w(E^{h_*}) = +1; theta sum H_M (O.4); abs(R_z^x) divides c_0 (injectivity mod 3), v2 c_0 = 9 | own | 125 | (O.2) | none | (O.7) |
| 8623-8960 | (proof: transformation law) | Weil representation: lower-unipotent depth via Fourier support; Weil-index identity gamma(ua)/gamma(a) = gamma(u)/gamma(1) (u,a)_p from quaternion norm forms; operator construction of the double cover; eigenvalue quotient (O.5a)-(O.5b) alpha_p(a)(a, det Q)_p; reciprocity (O.5c); holomorphy at cusps; extraction by Q_B/m gives (O.5) psi = eta_B (m/.), eta = eta_B chi_{h_*} | own; cites Weil Acta 111 I.13-I.14, II.25-II.30, III Thm 6 | 338 | (O.3), (O.4) | none | g_M modular |
| 8961-9100 | (proof: recurrence (O.6)) | neighbor count 1 + (-n/p) preserved lines; nonintegral part; self-adjointness N_ij/w_i = N_ji/w_j; H(p^2 n) + s(-n/p) H(n) + p s^2 H(n/p^2) = s chi_{h_*}(p) a_p H(n), hence (O.6) a_M(p^2 n) = {eta(p) a_p - psi(p)(-n/p)} a_M(n) - p eta(p)^2 a_M(n/p^2) mod 2^M; sieves preserve it | own (Brandt-matrix computation) | 140 | P_M Hecke identity | none | ex:app-coefficient-rules |
| 9101-9117 | ex:app-theta-comparison (statement) | (O.7) H_M(mD) = c_0 2^{omega(N)} zeta_M(D) lambda_M(L P_D bar) mod 2^M, zeta_M(D) a 2-power root of unity; no class number divided out | own + Cornut-Jetchev | 17 | (O.4), (O.2) | Cornut-Jetchev reduction map (Gross-type; not a GZ height formula) | (3.8) L2522-2530 |
| 9118-9240 | (proof: optimal embeddings, CJ specialization) | Q_B(x) = mD iff optimal embedding O_F -> R_z; 2^{omega(N)+1} local orientation tuples; each tuple an actual Pic(O_F)-torsor; genus character well defined (biquadratic discriminant (D h_*)^2); CJ §§3.1-3.3 with F_CJ = Q, K_CJ = F, B_CJ = M_2(Q), S = {l_0}: H.1, H.2 (integer 2), H.3 inert case; fine conductors 1; kappa = 1 (CJ Lemma 2.1(ii)); sign fiber at l_0 (§3.6); Cor 3.2 | cites Voight Prop 14.6.7 (v)=>(iii); Cornut-Jetchev §§3.1-3.3, 3.6, Thm 3.1, Cor 3.2, Lemma 2.1(ii) | 123 | - | none beyond CJ | (O.7) |
| 9241-9330 | (proof: reduction identity, orbit count) | CJ §§4.9-4.10 identify the adelic map with geometric reduction; sum_a chi_F(a) P_M(z_a) = lambda_M(L P_D bar); stabilizer +-1 gives c_0/2 per orientation tuple; phase zeta_M(D) | cites CJ §§4.9-4.10; own count | 90 | CJ specialization | none | (O.7) |
| 9331-9405 | (proof: other orientations, precision) | Atkin-Lehner normalizer and l_0 uniformizer change weight and norm character by the same sign, so all 2^{omega(N)+1} tuples contribute equally: total c_0 2^{omega(N)}; no loss of precision (c_0/2 integral); c_theta = 9 + omega(N); v2 a_M(D_w) = c_theta + c_w for M > c_theta + c_w | own | 75 | (O.3), (O.2) | none | visibility at D_w; delta minimum (L2531-2551) |
| 9407-9445 | ex:app-visibility, (O.8) | for simple-zero D: v2 a_M(D) >= min{M, j_gen(D) - C_det}; for every admissible D: v2 a_M(D) < M implies ord L(E^D,s) = 1 and j_gen(D) <= v2 a_M(D) + C_det; an odd-sign D that is not a simple zero has a_M(D) == 0 mod 2^M | own + "the height formula" (CST 1.1, not named here) | 39 | (O.7), L kills torsion | **G3: cites a print (CST 1.1, conductor one; Rankin L-function L(E^D,s) L(E^{h_*},s) with L(E^{h_*},1) != 0)** | branch 1 (L2593-2599), odd symbol, (3.9), ex:app-odd-minimum |
| 9446-9470 | ex:app-coefficient-rules (statement) | integer divisions (O.9)-(O.11) valid at every Fourier index (truncated for the odd source); fresh coefficient-one reading (t(Fr_q) theta H_U)[1] bar = A(Uq); actual symbols depend only on the typed graph and obey contraction, whole-prime omission, primary isolation; no claim at empty outputs or untested weights | own | 25 | ex:app-even-phase, ex:app-theta-form, ex:app-odd-minimum | none | ex:sec7-coefficient-rules (L2072-2119), seed/address lemmas |
| 9471-9548 | (proof: operators, levels) | coefficient support S; n_U, e_U, B_U = 2^{-n_U} prod (U_p - eta(p) V_p) g; V_p raises level by p with character psi (p/.); U_{p^2} preserves level 4Ap; U_{p^2} V_p = U_p; unary J-series levels | own (classical theta-multiplier calculations) | 78 | - | none | (O.9)-(O.12) |
| 9549-9640 | (proof: (O.9)-(O.11)) | shell recurrence b_s; p in U\J gives odd b_s - b_{s-1}, p in J gives even b_{s+1} - b_s; (O.9) v2 B_U[J r m^2] >= w(r) + ... - e_U; (O.10) (b_{s+1}-b_s)/2 == c_p(D) mod 2 via d_s == p d_{s-1} mod 4 and a_p == p+1 mod 4; unary series Theta_J; (O.11) H_U = (B_U - sum_J B_U[J] Theta_J)/2 integral; odd-source precision M - n_U - 1 | own | 92 | (E.12), (O.6), depth minimum | none | coefficient-one reading |
| 9641-9762 | (proof: integral trace module, reading) | theta H_U weight-2; finite closed integral module stable under Hecke, diamond, Chebotarev limits t(g), d(g); B_U[q] = 2^{-n_U} a(uq), H_U[q] = 2^{-n_U-1} a(uq); reading A(uq) in F_2; stage M_theta >= max(0, delta+W) + R; d(u)t(v) = t(v), t(u)t(v) = t(uv) + t(uv^{-1}), t(1) = 0; two fresh primes give zero, so factorization through elementary quadratic quotient | own | 122 | (O.9)-(O.11) | none | symbol well defined |
| 9763-9883 | (proof: (O.12) local identity at p in U) | conductor-one ramified blocks are Ind(mu_1, mu_2) (Casselman Thm 1 pp.302-306, Cor p.306, Thm 4 p.313); Carayol §§0.3-0.7, Thm A pp.409-411 normalization; U_p^(2) = sqrt(p) mu_1(p) on the new line (Whittaker computation); (O.12) U_p^(2){t(g tau phi) - t(g phi)} = d(phi){t(g tau) - t(g)} in characteristic 0, extended to the integral module | cites Carayol Thm A; Casselman Thm 1, Thm 4; own Whittaker computation | 121 | integral trace module | none | omission rule |
| 9884-9976 | (proof: omission, isolation, graph dependence) | H_U[pr] == eta(p) C_p(vr) 2^{-n_V-1} a(vr); opposite Legendre signs give A_U(U q_tau) + A_U(U q) = A_V(V r_0); product-label rule incl. external incidences; trivial-label vertex reads t(1) = 0 (primary isolation); bridge-copy argument gives dependence on typed graph only | own (CRT, Dirichlet, reciprocity) | 93 | (O.10), (O.12) | none | ex:sec7-coefficient-rules |

### Appendix G (app:endpoints), tex L9981-10935

| tex | label | claim | kind | size | depends on | GZ/TYZ | used in |
|---|---|---|---|---|---|---|---|
| 9981-9994 | (intro: choice order) | even-source case first (rough companion, genus lower bound), then odd minimum, then odd coefficient rules and two-symbol address; rough companion does not use the odd minimum | own (outline) | 14 | - | none | order of sec 7 (L1818-1823) |
| 9995-10000 | (HL statement) | Hoffstein-Luo [hl, p.436]: fundamental discriminants with nonzero central value, at most four prime factors, arbitrary finite splitting set | cites HL p.436 | 6 | - | none | ex:app-five-prime |
| 10001-10037 | ex:app-five-prime | in each nonempty signed unit filter of even root number: odd squarefree u prime to S and B with L(A^u,1) != 0 and omega(u) <= 5 (q_0 by CRT/Dirichlet, then HL applied to A^{q_0}; d > 0 forced by the functional equation; d == 1 mod 8) | own reduction to HL | 37 | HL | none | ex:sec7-nonvanishing (L1968-2004), rough companion |
| 10038-10053 | (sign for rough companion) | k_0 = a q_0 negative, 1 mod 8, square at 2Nh: w(E^{h k_0}) = w(E^h) chi_{k_0}(-N_{E^h}) = +1; HL on E^{h k_0} gives k' = k_0 d with at most five new primes | own | 16 | HL | none | ex:app-rough-companion |
| 10055-10079 | ex:app-rough-companion (statement) | constants A, C_E fixed before h: for h in the odd-sign filter there is negative odd fundamental k' with h k' partitionable, L_*(hk') != 0, omega(k') <= A, (F.3) v2 L_*(hk') <= 2 omega(h) + 2 omega(k') + s(hk') + C_E | own | 25 | ex:app-five-prime, one-symbol address, (E.8), (E.11) | none | ex:sec7-rough-companion (L2320-2401), (3.3) |
| 10080-10150 | (proof) | (F.1) unit symbol gives v2 L_*(sigma D) = 2 omega(D) + C_{e,unit}; partitionability of negative types (index 7 mod 8, least seed); (F.2) for partitionable corank-0 d: one-symbol address cube + Boolean comparison of sec 9 + (E.5), (E.8) give v2 L_*(d) - 2 omega(d) - s(d) <= C_{e,unit} + 2 C_loc; dummy anchors; (F.3) | own; uses lem:forward-rank and the sec 9 Boolean-degree lemma | 71 | (E.5), (E.8), (E.9), (E.11), ex:app-simultaneous-address, L5690-5714 | via lem:forward-rank (rank 0: Kato/Kolyvagin print) | (F.3), (F.4) |
| 10151-10170 | ex:app-odd-minimum (statement) | (3.5), (3.4) and the rough companion give (F.4)-(F.5) before the odd minimum; attained minimum delta_o on one ultrafilter; (F.6) for each weight cutoff on an ultrafilter-large set; valid stage for every finite operator budget; unit symbol exhaustive and implies (F.7) with C_o = delta_o + C_det | own | 20 | (3.4), (3.5), (F.3), (O.8) | uses (3.4) (CST 1.1, G1) and (O.8) (CST 1.1, G3) | L2531-2551 (delta minimum), (3.9) |
| 10171-10256 | (proof) | (F.4) 2 j_gen(h) >= 2 omega(h) + s(h) - C_gen (s(hk') cancels); (F.5) v2 a_M(D) >= min{M, omega(D) - C_coarse}; ultrafilter minimum delta_o (witness D_w makes the set nonempty); (F.6); stage choice T, M for an operator budget; (F.7) ord L(E^D,s) = 1 and j_gen(D) <= omega(D) + C_o for units | own (ultrafilter bookkeeping) | 86 | (F.3), (3.4), (3.5), (O.8), (O.2), (O.7) | via (3.4), (O.8) | ex:app-coefficient-rules (odd case), ex:app-final-family |
| 10258-10273 | ex:app-nonempty-seeds (statement) | fix K = Q(sqrt k); E/K has 2^inf-Selmer corank one; transported even source for E^k has v2 a_new(D) >= omega(D) and a nonempty K-split unit seed; if the odd limit symbol is a unit at the empty configuration, E already has a simple zero; otherwise both seeds are nonempty and readable through a common alphabet | own | 16 | ex:app-even-phase, ex:app-coefficient-rules, lem:forward-rank | via lem:forward-rank | L2604-2675 (final companion, ex:sec7-ksplit-seed) |
| 10274-10318 | (proof: transport) | s_2(E/K) = 1 (isogeny Res E -> E x E^k); new source for E^k normalized at 1; Waldspurger comparison gives v2 a_new(D) = v2 a_old(d_k D) - v2 a_old(d_k) >= omega(D) | own; Waldspurger (via ex:app-even-phase) | 45 | (E.10), (E.11) | none | ex:sec7-ksplit-seed |
| 10319-10443 | (proof: no-seed gives H[p^3] even) | under no K-split seed: b_1 even (G.4a), B[n_j] even (G.4b), (G.4c) (d(phi) f)[p] even with delta_B = delta_p, (G.4d) f == H mod 2; trace identity U_p^2 t(phi) = U_p^3 + d(phi) U_p and a fresh prime p' with H[p^2 p'] = eta(p)(a_p - 1) a(pp')/4 even give H[p^3] even | own | 125 | (O.11), (O.12)-type trace identity, (E.12) | none | mod-8 contradiction |
| 10444-10500 | (proof: mod-8 contradiction) | a(p^2) = eta(p)(a_p - 1), a(p^4) = eta(p)^2 {a_p(a_p - 1) - p}; B[p] = eta(a_p - 2)/2, B[p^3] = eta^2((a_p - 1)^2 - p)/2; H[p^3] = eta^2 (a_p - 1)(a_p - p - 1)/4, so no seed forces a_p == p+1 mod 8; but for p == 1 mod 4, (l/p) = -1, (k/p) = 1 the 2-primary part of E_l(F_p) has order exactly 4, so v2(p+1-a_p) = 2: contradiction. Hence a nonempty even seed | own (explicit computation, specific to E_l) | 57 | (E.12) | none | ex:sec7-ksplit-seed (L2649-2675) |
| 10508-10552 | ex:app-odd-stabilization | bounded elementary label groups; for each cutoff W one symbol table on an ultrafilter-large set; tables agree on restrictions; union defines the intrinsic odd limit symbol on all compatible finite typed graphs; stationary tests of k in a common alphabet | own (finite pigeonhole on an ultrafilter) | 45 | ex:app-odd-minimum, ex:app-coefficient-rules | none | ex:sec7-symbol odd case, two-symbol address, branch 1 |
| 10554-10590 | ex:app-simultaneous-address (statement) | one or two symbols with nonzero terminal polynomials at every x != 0: adjoin primary auxiliaries with nonzero linear activations, changing only their incidences, so that all symbols equal 1 at every x != 0 | own | 37 | coefficient rules, realization lemma | none | ex:sec7-one-symbol-address, ex:sec7-two-symbol-address (L2179-2271), rough companion |
| 10591-10626 | (proof: zero-total packets) | total projected labels zero; packets with even copies of every label, one copy per nonzero activation, give terminal inputs with nonzero terminal polynomial for each symbol, using only separate projection surjectivity | own | 36 | seed lemmas | none | packet realization (L2677-2693) |
| 10627-10730 | (proof: network operators) | network operator det(Q) + sum c_a^t adj(Q) c_b d_ab + (degree >= 2); singular network T = I+P with adj(Q) = r r^t isolates d_e at x_* and has constant 1 elsewhere; varying network T = I+L, B_eps = eps E_bb; sum over eps isolates d_e at x_* | own (F_2 linear algebra; Cauchy-Binet / matrix-tree) | 104 | contraction, primary isolation | none | (G.1a) |
| 10731-10790 | (proof: one choice for both symbols, (G.1a)) | top monomial M_x of H_{1,x} H_{2,x} with exponents <= 2; degree count: only minimum-cost terms survive, sum (G.1a) = prod_x [M_x](H_{1,x} H_{2,x}) = 1, so some eps works at every x != 0; one-symbol and stationary specializations | own (combinatorial-nullstellensatz-type count) | 60 | network operators | none | (3.9) |
| 10792-10812 | ex:app-final-family (statement) | in the nonempty-seed case, for large b, one actual theta stage and primes Q split in K realize h_x = prod (q^*)^{lambda_q(x)} with (3.9): ord L(E^{h_x},s) = 1, L_*(h_x k) != 0, j_gen(h_x) <= omega(h_x) + C_o, v2 L_*(h_x k) <= 2 omega(h_x) + C_e; constants before b | own | 21 | ex:app-simultaneous-address, (F.7), (O.8), even transport | uses (O.8) (CST 1.1, G3) | ex:sec7-final-family (L2695-2715), (3.9) |
| 10813-10861 | (proof) | finite budget W_b; stage in the finite intersection of ultrafilter sets; units give v2 a_M(h_x) = delta_o + omega(h_x) < M, (O.8) gives the simple zero and j_gen bound; even unit gives the L_* bound | own | 49 | (F.6), (F.7), (O.8) | via (O.8) | (3.9) |
| 10862-10935 | (final contradiction, (F.8)) | (3.4), (F.7) give 2 j_rc(h_x,k) <= 4 omega(h_x) + C_J; integral correction eta; (F.8) calibration; upper bound B at x != 0; fixed-field clearing f_x u~_x = d_x with c <= c_det, L_T(M) = 16(d_K+5)M; choose M > B + 2 c_det, b > (L_T(M)+2)(2^M - 1); x != 0 with v2(u~_x(0) - u~_0(0)) >= M - 2c > B contradicts base zero; Rankin factorization and L(E^k,1) != 0 give the simple zero of E | own (restates sec 9 L5666-5735) | 74 | (3.4), (4.6), (4.7), (5.9), (5.11), ex:arith-base-zero | via (3.4) (G1) and base-zero (G4) | end of proof of Theorem 5.3 |

## K3: exactly what (3.4) needs from CST Theorem 1.1

**Where.** ex:sec7-genus-lower, L2403-2458. The objects are defined at L2403-2415, the citation and
(3.4) are at L2427-2439, and the uses of (3.4) are (3.6) at L2440-2452, (F.4) at L10173-10178,
L2695-2705 (ex:sec7-final-family) and L10870-10874. This item records what the text needs. It does not
reconstruct CST. The bibliography entry is L11181-11183: Cai, Shu, Tian, *Explicit Gross-Zagier and
Waldspurger formulae*, ANT 8 (2014).

**The two applications.** h is positive, odd, squarefree, h == 1 mod 8, with w(E^h) = -1. h_* is a
negative odd fundamental discriminant with L(E^{h_*},1) != 0 and abs(h_*) > 4. k' is a negative odd
fundamental discriminant prime to 2Nh, square at every prime of 2Nh, with L(E^{hk'},1) != 0.

| | field K, disc K | conductor c | character chi | Rankin product L(E/K, chi, s) | point (L2411-2414) |
|---|---|---|---|---|---|
| genus | Q(sqrt(h h_*)), disc = h h_* (odd) | 1 | genus character for (h, h_*) | L(E^{(h)},s) L(E^{(h_*)},s) | P_h^gen = sum_{[a] in Pic(O_K)} chi(a) pi(x^[a]), as (O.1) |
| ring class | Q(sqrt k'), disc = k' (odd) | abs(h) (odd, prime to N and to k') | chi_h o N_{K/Q}, a ring-class character of conductor abs(h) | L(E^{(h)},s) L(E^{(hk')},s) | P_{h,k'}^rc = sum over Pic(O_c), weighted by chi_h |

In both cases the derivative at s=1 is L'(E^{(h)},1) times the nonzero central value of the other
factor. That is why "the two Rankin products have the common factor L(E^{(h)},s)" (L2432).

**The form of CST 1.1 that (3.4) needs, factor by factor.** Write the theorem as
ĥ(P_chi) = Phi(E, f) * F(K, c) * L'(E/K, chi, 1). The text's claims about each factor are:

| factor | what (3.4) needs | text that asserts it |
|---|---|---|
| (a) the point P_chi | the **unaveraged** sum over all of Pic(O_c), with no 1/#Pic(O_c), no 1/#genus classes and no 1/u | "its sum is unaveraged" (L2431); "unaveraged" (L2411, L2413) |
| (b) the parametrization | the same f = pi = phi o AJ with pi(inf) = 0 in both applications, so Phi(E, f) (Petersson norm, deg f, 8 pi^2, and so on) cancels exactly in the ratio | "the parametrization is the same" (L2430); pi set up at L1787-1789 |
| (c) the conductor/discriminant factor | F(K, c) = (fixed constant) x c x sqrt(abs(disc K)) x u^2 x 2^{mu(N, disc K)}, and **no other dependence on c or K**. Here u = [O_c^x : Z^x] = 1 (extra-unit fields excluded) and 2^{mu} = 1 because every prime of N splits | "Its conductor factor is c sqrt(abs(disc K))" (L2430-2431); "All level primes split, conductors are prime to N, extra-unit fields are excluded" (L2428-2430) |
| (d) the height normalization | ĥ is the absolute Néron-Tate height (or a fixed multiple of it, such as [K:Q] = 2), not a height normalized over the ring class field H_c. A normalization over H_c would bring in [H_c : K] = #Pic(O_c), whose 2-adic valuation grows with omega(c) | implicit; the text compares heights of points of the same rank-one group E^{(h)}(Q) |
| (e) hypotheses | Heegner hypothesis (every prime of N splits in K), (c, N) = 1, chi a ring-class character of exact conductor c, u = 1 | L2428-2430 |

**Why this gives (3.4).** Take the ratio of the two outputs, using (b) and (c):

ĥ(P^rc)/ĥ(P^gen) = [abs(h) sqrt(abs(k')) L(E^{(hk')},1)] / [sqrt(abs(h h_*)) L(E^{(h_*)},1)]
= L_*(hk') / L_*(h_*).

This uses L_*(d) = sqrt(abs(d)) L(E^d,1)/abs(Omega^-) (L7176), and both hk' and h_* are negative, so
the same period Omega^- appears. Both points are multiples of a generator of E^{(h)}(Q)/tors, and
each rational line has index 1 or 2 in its native lattice (L2433-2435). Taking v2 therefore gives
2 j_rc - 2 j_gen = v2 L_*(hk') - v2 L_*(h_*) + epsilon, where epsilon = 2(v2 n_rc - v2 n_gen) is in
{-2, 0, 2}, so abs(epsilon) <= 2.

**What would break it, and what would not.** Every quantity here is odd except the factors under
test: c = abs(h) is odd, and so are disc K = k' and h h_*. So **odd factors are harmless**. A power
c^a or abs(disc K)^b with a different exponent would leave the 2-adic statement unchanged. What would
break the 4 omega(h) balance in (3.5)-(3.6) and (3.9) is any factor whose 2-adic valuation grows with
omega(c) = omega(h):

- 2^{omega(c)};
- prod_{p | c}(p + 1), prod_{p | c}(p - 1), or phi(c)/c;
- #Pic(O_c)/#Pic(O_K) = (c/[O_K^x : O_c^x]) prod_{p | c}(1 - (d_K/p)/p);
- an average over Pic(O_c) (item (a));
- a height over H_c (item (d)).

Each of these changes (3.4) by a term of size about omega(h), and (3.4) is used in **both directions**:
as a lower bound in (3.6)/(F.4), and as an upper bound for j_rc at L10870-10874.

**For the reader holding CST.** My recollection (UNVERIFIED) is that CST Theorem 1.1 states
L'(1, E, chi) = 2^{-mu(N,D)} * 8 pi^2 (phi, phi)_{Gamma_0(N)} / (u^2 sqrt(abs(D c^2))) * ĥ_K(P_chi(f)) / deg f,
with P_chi(f) = sum over t in Gal(H_c/K) of chi(t) f(t). That would satisfy (a)-(e). Settling K3
needs four checks against the print:

1. the denominator u^2 sqrt(abs(D c^2)) and the factor 2^{-mu(N,D)}, with nothing else depending on
   c or D;
2. that P_chi(f) is the plain sum over Gal(H_c/K), unaveraged;
3. the normalization of ĥ_K (relative to K, not H_c);
4. that the hypotheses allow c > 1 with (c, N) = 1 and every prime of N split.

G2, G3 and G4 use only "height zero if and only if the derivative vanishes" and need none of this.

## Leftover editorial tex comments (sections 7-9 and Appendices E-G)

All are `%` comments. None is typeset. They record how the file was assembled from an earlier
"baseline" text. The ones that read as notes on the state of a proof are marked **(flag)**. The
`% Begin/End <file>.tex` markers are assembly markers only.

| tex line | comment | note |
|---|---|---|
| 2832 | `% Source reconstruction of the finite arithmetic input I08/I09.` | **(flag)** precedes ex:arith-finite-heegner |
| 2833 | `% This is a proof fragment, not an assertion about completion of RC.` | **(flag)** reads as a disclaimer on ex:arith-finite-heegner (L2834-3393); worth showing to Elliot |
| 3923 | `% Insert after baseline line 1583, before the ordinary compact Kummer complex.` | **(flag)** baseline-line note inside ex:arith-central-specialization |
| 4975 | `% Replace baseline lines 4112--4138.` | **(flag)** baseline-line note inside ex:limits-uniform-lower-bound |
| 7428 | `% Replace baseline lines 3310--3335; retains equation tag (E.3).` | **(flag)** baseline-line note in ex:app-even-scalar |
| 7789 | `% Replaces baseline manuscript.tex lines 3416--3510 inclusive.` | **(flag)** baseline-line note before ex:app-even-phase |
| 7790 | `% Baseline SHA256 525c8c05...b5197.` | **(flag)** baseline hash |
| 8222 | `% Replace immutable baseline lines 3532--3591 inclusive.` | **(flag)** baseline-line note before ex:app-detector |
| 8223 | `% Keeps (O.2). This expands the existing non-CM argument.` | **(flag)** edit note |
| 8407 | `% Completion audit replacement for baseline lines 3593--3748.` | **(flag)** before ex:app-theta-form |
| 2714, 2717, 4378, 4381, 5741, 5744, 6824, 8202, 8205, 9977, 9980, 10933 | `% Begin/End 03-...tex` to `09-...tex` | file-assembly markers |

No typeset text in L1760-10935 contains "baseline", "fragment", "audit" or "reconstruct". The only
typeset "audit" hits are file names in the source table at L6624-6643, which is outside this scope.

## Known issues

- **K1 (locators, UNVERIFIED).** None of the appendix locators in the prints table could be checked
  offline. As far as I recall, the content used in each case is available in the literature. The ones
  that carry the most weight are:
  - Waldspurger Cor 2 (pp.483-484), in particular that its proof removes (H2) for a pair in one
    2-adic squareclass;
  - Cornut-Jetchev Thm 3.1 with S = {l_0} and the sign fiber of §3.6. This is a 2010 preprint, cited
    by URL;
  - Kato 13.4(2) under rational hypotheses at p = 2 (the text says part (3) is not used);
  - Carayol Thm A, and Casselman Thm 1 / Thm 4;
  - Weil Acta 111 II.25-II.30.
- **K2 (read once, not certified).** About 4,100 lines of appendices were read once, in order. The map
  shows that each appendix statement used in sections 7-9 is proved from earlier statements and
  prints. It does not certify the large own constructions line by line. The highest-value next reads
  are:
  - the transformation law and orientation count of App F (L8623-9405), where (O.7) has no
    class-number loss;
  - the Kato-system normalization (K14), where there is no phi(D) or 2^{omega} factor, the even
    analogue of K3;
  - the network degree count (G.1a).
- **K3 (GZ contact G1).** See the section above. It is open until checked against the CST print; only
  (a)-(e) matter. The even-side analogue (K14) is Elliot's own normalization of Kato's Thm 6.6, and
  the text addresses it explicitly (L7155-7169).
- **K4 (presentation).** ex:app-coefficient-rules (L9446-9470) is stated "on all tested nonempty
  configurations". The odd symbol only exists as an ultrafilter limit of finite-stage tables
  (ex:app-odd-stabilization). The order of choices (budget, then stage, then primes) is stated
  carefully at L10813-10861 and is consistent. A reader should not read the coefficient rules as
  holding at one fixed stage for all weights; the text explicitly disclaims that.
- **K5 (presentation).** In ex:app-theta-comparison, P_1 (the case D = 1) is the trace of the
  conductor-one Heegner point to Q(sqrt h_*). Its use in branch 1 (L2593-2599) needs (O.8) at D = 1,
  where the Rankin product is L(E,s) L(E^{(h_*)},s). The text covers D = 1 explicitly (L8263-8266,
  L9189-9190), so this is fine.
- **K6 (text artefacts).** These are the flagged comments above. They are editorial, but L2833 ("proof
  fragment") is worth showing to Elliot.
- **K7 (inherited).** K4 and K5 of mcheck-rc-map (the outline omits branch 1; the harmless
  "sum t_p <= 2A") still stand. The appendices resolve its K2 only to the extent of the map.
