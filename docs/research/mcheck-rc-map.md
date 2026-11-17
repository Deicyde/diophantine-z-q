# mcheck-rc-map: map of the proof of Theorem 5.3 (hyp:RC) in sections 7-9, and a check of its opening reduction

Scope: tex L1760-5744 of `diophantine_zq.tex` (sections 7, 8, 9), read in full, in order. Appendices E
(app:even-source, L6825-8205), F (app:odd-source, L8206-9980) and G (app:endpoints, L9981-10935) were
**not** read in full. Only the statements the main text cites from them were looked up, plus
ex:app-visibility (O.8) at L9407-9445 and the start of ex:app-nonempty-seeds at L10259-10380.
No network was available. Every print locator below is quoted as the manuscript gives it. Wherever I say
whether a locator is right, that is from memory and marked UNVERIFIED.

Computations are in `scratch/mcheck-rc-map/checks.py`, with output in `checks.out` (43/43 PASS).

## Conclusion

**As far as the map shows, Theorem 5.3 follows from the cited prints plus Elliot's own steps. The logical
skeleton is coherent, and I found no step that is wrong.** No "error" verdict was reached, so no
`.fleet/mcheck-rc-map-verdict.md` was written. That is a statement about the skeleton and the checkable
algebra. Elliot's large own constructions in sections 8-9 (about 2,000 lines of 2-adic Heegner/Kolyvagin
and Iwasawa-type limit arguments) were read once for structure. They were not verified line by line.
Appendices E-G (about 4,100 lines) were not read.

### The skeleton (how RC is actually deduced)

Fix l. Assume corank Sel_{2^inf}(E_l/Q) = 1. The proof then runs as follows.

1. Root number w(E)=-1 by 2-parity, cited as [dd, Thm 1.8] (L1793-1797). So ord_{s=1} L(E,s) is odd, and
   RC amounts to excluding ord >= 3.
2. The odd theta forms of App F carry coefficients a_M(D) with (3.8): a_M(D) = c_0 2^{omega(N)} zeta
   lambda(L P_D^gen) mod 2^M (Cornut-Jetchev Thm 3.1). Visibility (O.8) follows: if v2 a_M(D) < M, then
   P_D^gen is nontorsion, so by CST Thm 1.1, ord L(E^D,s) = 1. At D=1 this is RC itself.
3. **Branch 1** (L2593-2599): the odd limit symbol is a unit at the empty configuration. Then
   v2 a_M(1) = delta_o < M, and (O.8) gives RC directly.
4. **Branch 2**: Elliot fixes a companion k with L(E^(k),1) != 0 and K = Q(sqrt k). Then
   s_2(E/K) = 1 + 0 = 1 (L2627-2647). He builds a binary family h_x (x in F_2^b) with (3.9) at every
   x != 0 (simple zero, L_*(h_x k) != 0, bounded genus index, bounded L-valuation). Through (3.4) (CST)
   and the calibration (4.6), these give a uniform upper bound B on v2 u~_x(0) at x != 0.
5. Fixed-field determinant clearing (5.9) gives f u~ = d in O[G], with uniform pole and valuation control.
   The Boolean-degree "missing-address" argument (5.10)-(5.11) then gives an address x != 0 with
   v2(u~_x(0) - u~_0(0)) > B.
6. Lemma ex:arith-base-zero: if L'(E/K,1)=0, the conductor-one Heegner point is torsion (CST/GZ print), so
   u~_0(0)=0. This contradicts step 5, so L'(E/K,1) != 0. Since L(E^(k),1) != 0 and
   L(E/K,s) = L(E,s)L(E^(k),s), we get ord L(E,s) = 1.

The checkable algebra in steps 4-6 was verified. That covers the inequality chains (3.3)-(3.6) and
(3.9)+(3.4), the Boolean-degree lemma, cube parity, the choice (5.10), the convolution estimate (5.11) and
the pole bound (5.8). See the Part 2 supplement and `checks.out`.

### Cited prints the proof rests on (statements as the manuscript uses them)

| print (manuscript locator) | statement used | where |
|---|---|---|
| BCDT, Thm A and Introduction conds (1)-(6) | E_l is modular | L1779, lem:forward-rank |
| Milne, *Modular functions and modular forms* v1.31, Thm 11.19, Rem 11.18 | rational newform f of level N; elliptic quotient q_f: J_0(N) -> A_f in the isogeny class of E | L1781-1786 |
| Dokchitser-Dokchitser, Crelle 658, Thm 1.8 | 2^inf-Selmer parity over Q, so corank 1 gives w = -1 | L1793-1797 |
| Kato, Asterisque 295, Thm 13.4(2), 13.5(2); Prop 8.12; Cor 14.3 | Euler-system divisibility at height-one primes not containing 2; nonzero class; rank-0 finiteness | L1886-1893, App E, lem:forward-rank |
| Hoffstein-Luo, MRL 4 (p. 436) | nonvanishing central twists with fundamental d having at most four prime factors and arbitrary finite splitting conditions | L1985-1991, App G L9996 |
| Bump-Friedberg-Hoffstein, Invent. 102 | in an odd filter, a twist with a simple zero ("simple-zero clause") | L1987-1992 |
| Desjardins, JTNB 32, Prop 3.3 | root-number factor (-1/p) at a newly ramified good odd prime | L1997 |
| **Cai-Shu-Tian, ANT 8, Thm 1.1** | explicit unaveraged GZ formula: Heegner/ring-class point height = L'(E,chi) up to (phi,phi), the conductor factor c sqrt|disc K| and fixed constants | (3.4) L2427-2439; D_w nontorsion L2463-2464, L8268-8271; (O.8) L9439; base-zero L4337-4339 |
| **Kolyvagin, MPIM 90-69, Thm 1 (with Thms 3-5)** | analytic rank r <= 1 gives rank r and finite Sha ("forward theorem") | lem:forward-rank (L1086-1108), used at L2376, L2630, L4020, L5250 |
| Cornut-Jetchev, 2010 preprint, Thm 3.1 (and §§3.1-3.6, 4.9-4.10) | oriented embedding count giving theta coefficient = Kummer image of the genus point mod 2^M | (3.8) L2522-2530, App F L9197-9266 |
| Waldspurger, JMPA 60, Prop 18, Cor 2 | comparison of squarefree Fourier coefficients of half-integral-weight forms (same dyadic squareclass) | L2554-2557, App G |
| Serre (open image) | non-CM 2-adic open image | L2882, L3600 |
| Cai-Chen-Liu, TAMS 370, Thm 2.15 | Heegner norm relations (4.1) | L2918 |
| Elkik, Asterisque 183 (Manin-Drinfeld) | finite cuspidal subgroup | L2940 |
| Nekovar, *Selmer complexes* (Sections 4.1.4.1, 5.1-5.4, 6.2-6.4, 7.8.8(ii), 8.1, 8.6) | Selmer complexes, duality, support change, Shapiro/transfer | throughout sec 8-9 |
| Milne, ADT I.2.3, I.2.8, I.3.2-3.5, I.4.10, I.5.1, I.7.3 (7.3.1) | local/global duality and Euler characteristics; isogeny invariance of the BSD quotient | L3442, L4027, L4526, L4547 |
| Edixhoven, Thm 5.3, Rem 5.4.1 | component group of a tame ramified twist is the fixed points of [-1] | L4119 |
| Lang 1956; Silverman IV.2.3, IV.3.2 | H^1 of a connected group over a finite field; formal groups | L3044-3051, L3180 |
| Howard 2012, sec 1.7 (13) | cross-reference only for the CM congruence (H4) | L2965 |

### Elliot's largest own steps (by size and difficulty)

1. **ex:arith-finite-heegner** (L2834-3393, about 560 lines). A finite Heegner/Kolyvagin descent at p=2
   with one uniform multiplier L, the one-prime derivative identities (4.2) at exact precision, and
   Selmer-cone witnesses. Hard. The identities spot-checked (H1, H5, H6, H12, H14, H17, H18) are correct.
2. **Section 9 limits** (L4382-5744, about 1,360 lines). Finite free models and an ultrafilter inner
   limit; the residual rank bound (5.1); the outer DVR (5.3); rank-two detection; derivative switches; the
   **uniform ring lower bound (5.5)** (the "varying-companion estimate", giving (3.5)); the fixed-field
   budget (5.7); determinant clearing (5.9); and the final missing-address contradiction (5.11). Very
   hard. The arithmetic (5.1), (5.7), (5.8), (5.9), (5.10) and (5.11) checks.
3. **ex:sec7-even-scalar** (L1832-1966, 135 lines, expanded in App E). A uniform Kato-scalar family u^ev
   with (3.2). Hard. Its key inputs are Kato's divisibility and the integrality at two, and both are
   sketched.
4. **Coefficient symbols and the address lemmas** (L2006-2271, plus App G simultaneous-address and App F
   odd stabilization). Finite combinatorics on typed residue graphs. Medium difficulty, but the proofs
   are delegated to the appendices.
5. **ex:arith-moving-character** (L3498-3702, about 205 lines). Moving anticyclotomic characters with a
   uniform trace bound c_E = 16d+21. Medium. The SL_2(Z_2) group theory and the trace lemma (4.4d)
   were checked numerically.
6. **ex:arith-central-calibration** (4.6) (L3989-4140) and **ex:arith-common-coordinate** (4.7)
   (L4142-4317). Medium. The Euler-factor identities, regulator ratio and component-group bookkeeping
   check.
7. **Odd theta forms and the ultrafilter minimum delta** (L2460-2551, App F about 1,800 lines). Hard,
   and not read.

### Every GZ/TYZ contact point

No TYZ argument and no TYZ citation occurs anywhere in L1760-5744 or Appendices E-G (grep for tyz/Tian).
GZ enters only through the CST print and the Kolyvagin print:

| # | tex | contact | kind |
|---|---|---|---|
| G1 | L2427-2439 (3.4) | CST Thm 1.1 applied twice (genus point over Q(sqrt(h h_*)); ring-class point of conductor abs(h) over Q(sqrt k')). The ratio has the common factor L(E^(h),s), plus index-at-most-two glue | cites a print, plus about 10 lines of Elliot's own comparison. Conductor factor c sqrt abs(disc K) as the text states it; UNVERIFIED against the print (Known issue K3) |
| G2 | L2463-2464, L8268-8271 | CST Thm 1.1 at conductor one: L'(E^(D_w),1) L(E^(h_*),1) != 0, so P_{D_w}^gen is nontorsion | cites a print |
| G3 | L9439 (O.8), used at L2588 and throughout | CST Thm 1.1: an odd-sign D that is not a simple zero has a torsion genus point. Conversely, a visible coefficient forces a simple zero | cites a print |
| G4 | L4337-4339 (ex:arith-base-zero) | "conductor-one height formula": L'(E/K,1)=0 makes the Heegner point torsion | cites a print (CST 1.1, implicit) |
| G5 | lem:forward-rank (L1086-1108) | Kolyvagin Thm 1 (r <= 1 gives rank r and finite Sha). Used for the companions, the calibration and s_2(E/K)=1 | cites a print (Kato Cor 14.3 also cited for r=0) |
| G6 | L2834-3393, L4747-5205 | Heegner points with Kolyvagin derivative classes, and Kolyvagin-style rank reduction by derivative switches | **Elliot's own argument**, not a citation of Kolyvagin and not a GZ formula. Under Jack's ruling this is Elliot's own work to be checked, not a place where we would need our own GZ/TYZ argument |

No step was found that needs a GZ or TYZ argument beyond a print.

### Steps that looked wrong

None. One sub-step failed in my first script run, and that was my own range bug: v2((1+2^m)^2-1) = m+1
needs m >= 2, and the text has m = 2d+2 >= 6. Minor imprecisions are listed under Known issues.

## Map

Columns: tex lines | label | claim | kind | size (lines) | depends on | GZ/TYZ contact. "Own" means
Elliot's own argument. Print locators are as the manuscript gives them.

### Section 7 (sec:rc), tex L1760-2715

| tex | label | claim | kind | size | depends on | GZ/TYZ |
|---|---|---|---|---|---|---|
| 1760-1798 | sec:rc intro | E_l invariants, non-CM; modularity; modular parametrization phi=alpha q_f; root number -1 from Selmer corank 1 | cites BCDT (Thm A, conds (1)-(6)); Milne MF (Thm 11.19, Rem 11.18); DD (Thm 1.8, Selmer parity) | 39 | none | none |
| 1799-1816 | ex:sec7-rc-scope | why l = 11 mod 12; only fixed-l constants | own (remark) | 18 | Lemma lem:corank (sec 5) | none |
| 1818-1823 | (dependency order) | plan: even bound -> genus lower bound (via sec 9 limits) -> odd normalization -> common family -> determinant argument | own (outline) | 6 | - | none |
| 1825-1966 | ex:sec7-even-scalar | one Iwasawa scalar u^ev in Lambda[1/2][G] with uniform clearing 2^{C_ev}, and (3.2): v2 u_h(0) = v2 L_*(h) - 2 omega(h) - s(h) + O(1) at corank-0 constituents with L != 0 | own construction around Kato's Euler system; cites Kato Thm 13.4(2), 13.5(2); details in App E (ex:app-kato-system, ex:app-even-scalar, ex:app-central-calibration) | 142 | App E; sec 9 nilpotent-perturbation finite free models | none (Kato, not GZ) |
| 1968-2004 | ex:sec7-nonvanishing | in any signed unit filter + avoidance set: even root number -> squarefree twist with <=5 primes and L(1)!=0; odd -> simple zero | cites Hoffstein-Luo [hl] (even, "at most four prime factors of d"), BFH [bfh] (odd, simple-zero clause), Desjardins Prop 3.3 (root numbers); Dirichlet | 37 | ex:app-five-prime (App) | none |
| 2006-2070 | ex:sec7-typed-graph, ex:sec7-symbol | definitions: typed residue graphs; F2-valued coefficient symbol A(D) = [v2 a(D) = delta + omega(D)] | own (definitions) | 65 | (3.2), (3.8), ex:app-even-phase, ex:app-odd-minimum, ex:app-odd-stabilization | none |
| 2072-2119 | ex:sec7-coefficient-rules | symbols obey whole-prime omission, contraction Delta_vw A(G)=A(G/(v,w)), primary isolation | own; proof delegated to ex:app-coefficient-rules (shell recurrence, trace/inertia identities) | 48 | App (coefficient rules) | none |
| 2121-2142 | ex:sec7-realization | any compatible type/bit prescription realized by fresh primes | own (CRT + Dirichlet + reciprocity) | 22 | coefficient rules | none |
| 2144-2177 | ex:sec7-seed-partition, ex:sec7-seed-certificate | minimum seeds independent of internal bits; contraction certificate -> nonzero terminal polynomial; partitionability criterion | own (finite combinatorics) | 34 | coefficient rules | none |
| 2179-2271 | ex:sec7-address, ex:sec7-one-symbol-address, ex:sec7-two-symbol-address | addresses x in F2^b; adjoin primary vertices so symbol(s) = 1 at all x != 0 | own; proof delegated to ex:app-simultaneous-address (forest/network, product of top forms) and ex:app-odd-stabilization | 93 | App (simultaneous address) | none |
| 2273-2318 | ex:sec7-even-upper | partitionable, Selmer corank 0 -> (3.3b): L_*(d)!=0, v2 L_*(d) - 2omega(d) - s(d) <= C_1 | own ("cyclotomic missing-address argument on the Kato scalar"); uses Boolean bounded bit degree from sec 9 | 46 | (3.2), seed lemmas, one-symbol address, sec 9 bit-degree bound | none |
| 2320-2401 | ex:sec7-rough-companion | for h in prepared filter: negative odd fund. disc k', omega(k') <= A, L_*(hk')!=0 and (3.3) | own; uses ex:sec7-nonvanishing (HL), "forward rank-zero theorem" (Kato/Kolyvagin-type, not named here), (3.3b); App ex:app-rough-companion | 82 | 3.3b, nonvanishing | none (forward theorem: print-level, unnamed at this point) |
| 2403-2458 | ex:sec7-genus-lower | (3.4) GZ comparison of genus point and ring-class point; (3.5) arithmetic lower bound from sec 9; hence (3.6) 2j_gen(h) >= 2omega(h)+s(h)-C | (3.4): cites CST Thm 1.1 twice + own index-<=2 lattice glue and ratio of the two formulas; (3.5): forward ref to ex:limits-uniform-lower-bound + ex:arith-central-calibration (sec 8-9) | 56 | (3.3), sec 8-9 | CITES A PRINT (CST 1.1) + own comparison of two outputs (factor L(E^(h),s) common, period convention, epsilon<=2); see Known issues K3 |
| 2460-2551 | (fixed witness, odd forms) | D_w with L'(E^(D_w),1)!=0 gives nontorsion Q; Chebotarev stage (3.7); ternary theta forms; (3.8) a_M(D) = c_0 2^omega(N) zeta lambda(L P_D^gen) mod 2^M via Cornut-Jetchev Thm 3.1; ultrafilter minimum delta | own (theta construction, App F ex:app-odd-*), cites Cornut-Jetchev Thm 3.1 and CST 1.1 (nontorsion of P_{D_w}) | 92 | sec:nonvan (BFH), (3.6), App F | CITES A PRINT (CST 1.1 for nontorsion); Cornut-Jetchev counting is Gross-type (special-value via Heegner/CM points) but cited |
| 2553-2575 | (common family, Waldspurger) | even source as eigenvector; Waldspurger Cor. 2 compares squarefree Fourier coefficients; coefficient ratios rational x root of unity | cites Waldspurger (Prop 18, Cor 2) + own Galois-conjugation argument | 23 | - | none (Waldspurger, not GZ) |
| 2576-2591 | (operators) | omission/contraction for both systems via V_p, traces, U_p eigenvalue | own sketch | 16 | App | none |
| 2593-2602 | (empty-unit branch) | if odd symbol unit at empty config: v2 a(1) = delta_o < M, visibility (O.8) gives ord L(E,s)=1 = (RC) | own; (O.8) in App F | 10 | (3.8), App F (O.8) | (O.8) presumably via GZ+Kolyvagin (visible Heegner point) — to check in map of App F use |
| 2604-2647 | (final companion) | fix k (even unit, L(E^(k),1)!=0), K=Q(sqrt k) with fresh ramification; s2(E/K)=s2(E/Q)+s2(E^(k)/Q)=1 | own; "forward theorem at nonzero central value" (Kato) | 44 | even symbol, nonvanishing | none |
| 2649-2675 | ex:sec7-ksplit-seed | nonempty K-split unit seed for E^(k); proof via 2-primary of E_l(F_p) of order 4 | own, specific to E_l; App ex:app-nonempty-seeds | 27 | App E/G | none |
| 2677-2693 | (packet realization) | grounded Laplacian minors, product of top forms -> one choice works for both | own (sketch) | 17 | App simultaneous address | none |
| 2695-2715 | ex:sec7-final-family | binary family h_x, x in F2^b, with (3.9): simple zero, L_*(h_x k)!=0, j_gen <= omega+C_o, v2 L_* <= 2omega + C_e; hence 2j_rc <= 4omega + C_J | own; App ex:app-simultaneous-address, ex:app-final-family | 21 | two-symbol address, (3.4), (3.8) | uses (3.4) (CST) |

### Section 8 (sec:arithmetic), tex L2718-4380

| tex | label | claim | kind | size | depends on | GZ/TYZ |
|---|---|---|---|---|---|---|
| 2718-2741 | (setup) | coefficient rings A_i=(Z/2^i)[t]/t^i, M_i=(T_2E (x) A_i)(chi_h Psi_i); one moving character Psi_i for whole family | own | 24 | ex:arith-moving-character | none |
| 2743-2760 | ex:arith-data | conventions: Lambda, O, binary family, local conditions | own (definition) | 18 | sec 7 | none |
| 2761-2830 | ex:arith-conjugate-duality | tau^*M_i = M_i^*(1) via Weil pairing; finite Selmer duality C_U(M) = RHom(C_{U^perp}(M^*(1)),R)[-3] | own + cites Nekovar Selmer complexes (by section, below) | 70 | - | none |
| 2834-3393 | ex:arith-finite-heegner | finite Heegner/Kolyvagin descent at p=2 with ONE multiplier L: norm relations (4.1) (cites Cai-Chen-Liu Thm 2.15; Elkik/Manin-Drinfeld), CM congruence (H4) (own; Howard 2012 sec 1.7 (13) as cross-ref), (H5)-(H7) derivative classes, descent (H8)-(H9) (Nekovar 4.1.4.1), local descent (H10) (Lang 1956 Thm 1; Silverman IV.3.2(a)), exact one-prime precision (H12)-(H19), coefficient push/Shapiro (H20)-(H21) (Nekovar 8.1.1-8.1.6), local tame diagrams, Selmer-cone witnesses (H22) | own (a full Kolyvagin-system construction at 2; uses Serre open image) | 560 | Serre open image, CCL, Nekovar | Heegner points + Kolyvagin derivatives, own argument; no GZ formula used; NOT a citation of Kolyvagin Thm 1 |
| 3395-3468 | ex:arith-local-kummer | derived Kummer condition is its exact annihilator with integral isotropy homotopy | own + cites Milne ADT I.2.3, I.3.2-3.5; Nekovar 5.1, 5.2.4, 5.4.3, 6.3.4 | 74 | - | none |
| 3470-3496 | (4.4), support change | tame split local model; Nekovar Prop 7.8.8(ii) support change, five uses | cites Nekovar 7.8.8(ii) | 27 | - | none |
| 3498-3702 | ex:arith-moving-character | split primes r = 1 mod 2^B and characters xi of Gal(H_r/K) with xi=1 at active orientations, trivial at 2N, and v2(2 +- a_r) <= c_E = 16d+21 | own (Kummer + Chebotarev + explicit SL2(Z2) group theory) | 205 | Serre open image | none |
| 3704-3880 | ex:arith-paired-functional | closed degree-2 functional lambda_z = PD(-, j^{-1}c(z)), integral over O[G]; height-one regularity for primitive constituents | own + Nekovar 6.2.5-6.2.8, 6.3.4 | 177 | inner limit (sec 9), local Kummer | none |
| 3882-3892 | ex:arith-coordinate | coordinate u of [z](x)[lambda] in det line | own (definition) | 11 | - | none |
| 3894-3988 | ex:arith-central-specialization | central specialization: z_0 = i(LmP), lambda_0 = Kummer dual of c_K(LmP); free coefficients have valuation j_rc + v2(Lm) | own | 95 | (4.5) from finite Heegner | none (point identity only) |
| 3989-4140 | ex:arith-central-calibration | (4.6): v2 u_prim(0) = 2j_rc - 4omega(h) - s(h) - s(hk) - sum_{p|k} t_p + O(1) at known simple zeros | own (Kummer complex torsion + Cassels isogeny invariance via Milne ADT I.7.3 (7.3.1) + Edixhoven Thm 5.3/Rem 5.4.1 for component groups); uses lem:forward-rank | 152 | lem:forward-rank (Kolyvagin Thm 1 print; Kato Cor 14.3), finite Heegner | via lem:forward-rank: CITES Kolyvagin Thm 1 as print |
| 4142-4317 | ex:arith-common-coordinate | primitive vs relaxed: l_q u_rel = e_q^2 eps_q u_prim (4.7); universal integral correction eta in O[G] | own (exact algebra; Nekovar 6.4.1-6.4.3) | 176 | moving character | none |
| 4319-4373 | ex:arith-base-zero | if L'(E/K,1)=0 then u_prim,0(0) = u~_0(0) = 0 | own DVR/Smith argument + "conductor-one height formula" makes Heegner point torsion | 55 | paired functional, (4.5), common coordinate | CITES A PRINT (GZ in CST 1.1 form, conductor one) |

### Section 9 (sec:limits), tex L4382-5744

| tex | label | claim | kind | size | depends on | GZ/TYZ |
|---|---|---|---|---|---|---|
| 4382-4388 | (intro) | all maps, homotopies, duality data retained | own | 7 | sec 8 | none |
| 4391-4456 | ex:limits-inner-limit | flat complexes over Artin rings have finite free models (perturbation formulas); ultrafilter limit over Lambda keeps matrix identities | own (homological perturbation + ultrafilter) | 66 | - | none |
| 4458-4648 | ex:limits-residual-bound | generic residual rank N(E,A,j) <= 56omega(2N)+8A+56j+70, independent of the active primes | own; cites Milne ADT I.4.10, I.5.1, I.2.3, I.2.8; Nekovar 7.8.8(ii) | 191 | inner limit | none |
| 4650-4745 | ex:limits-outer-evaluation | evaluation identities (5.2); outer ultraproduct O_inf (5.3) is a DVR with uniformizer 2 | own | 96 | (5.1) | none |
| 4747-4831 | ex:limits-kernel-detection | rank-two localization at one kernel element (char 0); exact Chebotarev realization (5.4) | own (Kolyvagin-type detection) | 85 | (H1)-(H2) matrix span | own Kolyvagin-style; no GZ |
| 4833-4907 | ex:limits-derivative-switch | derivative local conditions; switch preserves the determinant-coordinate valuation | own; Nekovar 6.3.3-6.3.4 | 75 | (4.2) | none |
| 4909-5205 | ex:limits-uniform-lower-bound | (5.5) v2 u_prim >= -C(E,A) uniformly at known simple zeros; u_prim in Lambda[1/2] (height-one regularity, including the quadratic specializations (t),(t+2)); hence (3.5) | own (rank reduction by switches in the outer DVR; sign-decomposition argument in the quadratic case) | 297 | (5.1)-(5.4), switch lemma, (4.6), finite Heegner | own Kolyvagin-style; no GZ |
| 5207-5484 | ex:limits-fixed-field-budget | fixed K: (5.6) support triangle; (5.7) rank <= 2d_K+12, m <= d_K+5, h_1 <= h_K+2c_E+2t_K; (5.8) Schur inverse pole <= 4M at every sign | own; Nekovar 5.1.1-5.1.6, 6.3.4 | 278 | moving character, common coordinate | none (uses s_2(E/K)=1, via lem:forward-rank) |
| 5486-5664 | ex:limits-fixed-field-clearing | common Delta, Q in O[G]: f u~ = d with f = 2^a Delta^4, v2 f_0(0) <= c_det, pole L_T(M) = 16(d_K+5)M | own (block Schur/Smith determinant calculus) | 179 | (5.7), paired functional, eta | none |
| 5666-5735 | ex:limits-coefficient-transfer | Boolean bit-degree lemma + cube parity give an address x != 0 with v2(u~_x(0)-u~_0(0)) >= M-2c > B; base-zero lemma gives a contradiction; so L'(E/K,1) != 0 and ord L(E,s)=1 | own | 70 | (3.9), (3.4), (4.6), (4.7), (5.9), base-zero | via (3.4) (CST) and base-zero (CST) |

### What the main text takes from Appendices E-G (not read in full)

- **App E (app:even-source, L6825-8205)**: ex:app-kato-system (L6847), ex:app-even-scalar (L7367) and
  ex:app-central-calibration (L7614) give the full construction of u^ev and (3.2). ex:app-even-phase
  (L7792) gives the coefficient-square formula making the even symbol well defined, which yields (3.3a).
- **App F (app:odd-source, L8206-9980)**: ex:app-theta-form (L8409) gives the weighted ternary theta forms
  and their transformation laws. ex:app-theta-comparison (L9104) gives (3.8) via Cornut-Jetchev.
  ex:app-visibility (L9407) gives (O.8), which was read (CST contact G3). ex:app-coefficient-rules
  (L9447) proves the omission/contraction/primary-isolation rules.
- **App G (app:endpoints, L9981-10935)**: ex:app-five-prime (L10001) is the HL five-prime bound.
  ex:app-rough-companion (L10056) gives the companion k'. ex:app-odd-minimum (L10152) and
  ex:app-odd-stabilization (L10508) give the odd minimum and the finite-stage tables.
  ex:app-nonempty-seeds (L10259) gives the congruence a_p == p+1 mod 8 under the no-seed assumption; I
  read the start, and it holds for every fresh good K-split p, so it applies to the p chosen at L2662.
  ex:app-simultaneous-address (L10554) proves the address lemmas, and ex:app-final-family (L10792) gives
  (3.9).

## Part 2: Manuscript check of the opening reduction of section 7

**Where the reduction ends.** Section 7 opens with the setup (L1760-1797) and the scope remark
(L1799-1816). The paragraph "Here is the dependency order of the proof" (L1818-1823) then reduces RC to
five statements proved later: (a) the even coefficient bound, (b) the varying-companion estimate from the
two limits, (c) the genus lower bound, (d) the odd normalization and the common binary family, and (e) the
fixed-field determinant argument. Subsection 7.1 starts at L1825 with the first of these, so **I stop at
L1823**. Under the heading "Supplement" I also checked the two places where that outline turns into an
actual deduction of RC: the branch split (L2593-2602) and the final contradiction (L5666-5735).

| tex | step | verdict | reason |
|---|---|---|---|
| L1761-1764 | definition of E_l: y^2 = x(x-l)(x+3l) for positive squarefree l == 11 mod 12 | OK | matches the hypothesis domain of hyp:RC (L1005-1010) |
| L1765-1766 | c4 = 208 l^2, Delta = 2304 l^6, j = 35152/9 | OK | computed from the Weierstrass coefficients for 9 values of l (checks.py) |
| L1766-1767 | full rational 2-torsion; non-CM because rational CM j-invariants are integers | OK | roots 0, l, -3l are rational; j is not integral (checks.py); integrality of rational CM j is standard |
| L1768-1769 | E_l differs from the CM generator curve | OK | non-CM vs CM |
| L1771-1776 | restatement (RC) | OK | identical to the display at L1007-1009 |
| L1777-1778 | RC is proved in sec 7-9 with Appendices E-G | OK (pointer) | consistent with the map |
| L1779-1780 | E is modular [bcdt, Thm A] | OK | Thm A of BCDT is the modularity of all E/Q. The locator "Introduction, conditions (1)-(6)" is UNVERIFIED |
| L1781-1786 | rational newform f of level N; quotient q_f: J_0(N) -> A_f in the isogeny class of E [milnemf, Thm 11.19, Rem 11.18] | OK; locator UNVERIFIED | Eichler-Shimura plus modularity. Isogeny of A_f with E follows from equality of L-functions (Faltings), or directly from the modular parametrization. The precise Milne numbering was not checked |
| L1787-1789 | phi = alpha q_f, pi(x) = phi([x]-[inf]); pi(inf)=0; phi T_q = [a_q] phi for q not dividing N | OK | Hecke acts on A_f through a_q, and alpha is a Q-isogeny, so it commutes |
| L1790-1793 | fix the Tate lattice and local squareclasses at 2N; constants are fixed before conductors, companions and binary dimension vary | OK (organizational) | this order is respected later: see the order of choices at L2706-2711 and L5650-5662 |
| L1793-1797 | a rational 2-torsion point gives a rational 2-isogeny; Selmer parity [dd, Thm 1.8] gives w(E) = -1 when corank Sel_{2^inf} = 1 | OK; locator UNVERIFIED | 2^inf-Selmer parity over Q is a theorem (Monsky for p=2; Dokchitser-Dokchitser in general). Corank 1 is odd, so w = -1. As the text says, it does not need rank or finite Sha. Whether it is exactly Thm 1.8 of the Crelle paper is UNVERIFIED |
| L1799-1806 | remark: the two RC applications in the proof of PC have dim Sel_2 = 3, so corank 1 by lem:corank | OK | lem:corank (L1072-1084) is correct: r + dim Sha[2] = 1; Cassels-Tate is alternating for elliptic curves (Poonen-Stoll), so dim F[2] is even, F = 0 and r + t = 1 |
| L1808-1810 | l is odd, prime to 3, greater than 1, hence not a square | OK | l == 3 mod 4 (checks.py) |
| L1810-1816 | constants may depend on the fixed curve; no uniformity in l | OK | RC is a statement for each l separately; nothing later needs uniformity in l |
| L1818-1823 | dependency order: (a) even bound, then (b)+(c) genus lower bound, then (d) odd normalization and common family, then (e) determinant argument at the base; the even estimate does not use (e) | OK, with a gap filled | The order matches the text: (a) = (3.2), (3.3b), (3.3) at L1832-2401; (b)+(c) = (3.5)+(3.6) at L2403-2458 with (5.5) at L4909; (d) = L2460-2715; (e) = L5207-5735. There is no circularity: the even upper bound uses from sec 9 only the Boolean bit-degree lemma (L5690-5700), which is self-contained. **Gap filled (presentation):** the outline omits the empty-unit branch (L2593-2599), where RC follows from (O.8) at D=1 without (e). It also does not say where the Selmer hypothesis is used: only in w = -1 (L1793) and in s_2(E/K) = 1 (L2627-2647), which feeds ex:arith-base-zero and the budget (5.7). Sketch: the hypothesis enters exactly at these two points; every other step is unconditional or uses only analytic hypotheses at known parameters |

### Supplement: the two places where the outline becomes a deduction of RC

| tex | step | verdict | reason |
|---|---|---|---|
| L2593-2599 | branch 1: odd limit symbol a unit at the empty configuration, so v2 a_M(1) = delta_o < M, so (O.8) gives ord = 1 | OK (relative to (O.8)) | D=1 is admissible ((1/l_0) = 1). Read (O.8) at L9407-9445: a visible coefficient gives a nontorsion genus point by (3.8), hence a simple zero by CST 1.1 (here L(E^(h_*),1) != 0) |
| L2627-2647 | s_2(E/K) = s_2(E/Q) + s_2(E^(k)/Q) = 1 + 0 | OK | the sum/difference isogeny Res_{K/Q}E -> E x E^(k) has kernel and cokernel killed by 2. s_2(E^(k)) = 0 by lem:forward-rank (Kolyvagin/Kato print) |
| L2649-2675 | K-split nonempty seed for E^(k), via #E_l(F_p)[2^inf] = 4 when p == 1 mod 4 and (l/p) = -1 | OK (relative to App G) | the halving criterion gives the differences -l, l, -4l. Brute force over 984 pairs (l,p) confirms that the 2-primary part has order exactly 4. The congruence a_p == p+1 mod 8 comes from App G (L10320ff) for every fresh K-split p. The conditions p == 1 mod 4, (l/p) = -1, (k/p) = 1 are compatible because K has a fresh ramified prime |
| L2695-2705 | (3.9) + (3.4) give 2 j_rc(h_x,k) <= 4 omega(h_x) + C_J | OK | checks.py; C_J = 2C_o + C_e - v2 L_*(h_*) + 2 |
| L2440-2452 | (3.3) + (3.4) + (3.5) give (3.6) | OK | checks.py; C = C_R + C_E + 2A + 2 - v2 L_*(h_*). (The bound sum t_p <= 2A at L5197 is not needed for this direction; t_p >= 0 suffices) |
| L5197-5200 | (5.5) + (4.6) give (3.5) | OK | v2 u(0) is at least the Gauss valuation of u in Lambda[1/2]. Substitute into (4.6) |
| L5690-5700 | bit j of a sign-value function has Boolean degree at most 2^{j-1} | OK | Lucas/(1+Y)^A argument checked; brute force (b <= 6, 300 random elements) |
| L5702-5714 | cube parity and the choice (5.10) | OK | a Boolean function of degree < b has even support (brute force). Here q = L_T(M)+2 equations, each of degree at most 2^{M-1}-1 |
| L5716-5735 | convolution estimate (5.11), then contradiction with v2 u~_x(0) <= B | OK | checked by hand: E_x has valuation >= M-c, F_x has valuation c, and M > B + 2c_det. B is fixed before b (constants C_o, C_e, C_J, the (4.6) error) |
| L5736-5741 | L'(E/K,1) != 0 and L(E^(k),1) != 0 give ord L(E,s) = 1 | OK | L(E/K,s) = L(E,s)L(E^(k),s), and w(E) = -1 gives ord >= 1 |

## Known issues

- **K1 (locators, UNVERIFIED).** I could not check the following offline: DD Thm 1.8; BCDT "conditions
  (1)-(6)"; Milne MF Thm 11.19/Rem 11.18; Kato Thm 13.4(2), 13.5(2), Prop 8.12, Cor 14.3; the HL
  statement "at most four prime factors, arbitrary finite splitting set" (p. 436); the BFH simple-zero
  clause; CST Thm 1.1 and its hypotheses; Cornut-Jetchev Thm 3.1 with changed set {l_0}; CCL Thm 2.15;
  Waldspurger Cor 2. In each case the mathematical content used is, as far as I recall, available in
  the literature. The exact numbering is unverified.
- **K2 (unread volume).** The weight of the proof is Elliot's own: finite Heegner descent at 2,
  ultrafilter limits, the uniform lower bound (5.5), the odd theta forms and the address combinatorics.
  About 2,000 lines of sections 8-9 were read for structure. About 4,100 lines of Appendices E-G were not
  read. The map shows that the reduction is complete. It does not certify those constructions. The
  highest-value next checks are ex:limits-uniform-lower-bound (L4909-5205, the "varying-companion
  estimate") and ex:arith-finite-heegner (L2834-3393).
- **K3 (GZ contact G1, UNVERIFIED against the print).** (3.4) needs CST Thm 1.1 for ring-class characters
  of conductor c = abs(h) to have no conductor-dependent factor other than c sqrt abs(disc K) (and
  u = [O_c^x : Z^x] = 1). My recollection of CST 1.1 agrees: the denominator is u^2 sqrt abs(D c^2), and
  2^{-mu(N,D)} is trivial here. Any extra factor like 2^{omega(c)} would shift (3.4) by a multiple of
  omega(h) and break the 4 omega(h) balance in (3.5)-(3.6) and (3.9). Under Jack's ruling this is marked,
  not reconstructed.
- **K4 (presentation).** The outline at L1818-1823 omits the empty-unit branch and does not say where the
  Selmer hypothesis enters. This is filled in above.
- **K5 (presentation).** At L5197 "sum_{p|k} t_p <= 2A" is invoked, but the inequality needed for (3.5)
  only uses t_p >= 0. This is harmless.
- **K6 (text artefacts).** Source-reconstruction comments remain in the tex: L2832-2833 ("This is a
  proof fragment, not an assertion about completion of RC"), L3923 ("Insert after baseline line 1583")
  and L4975 ("Replace baseline lines 4112--4138"). These are editorial and not mathematical. The first
  is worth showing to Elliot, since it reads as a disclaimer on ex:arith-finite-heegner.
