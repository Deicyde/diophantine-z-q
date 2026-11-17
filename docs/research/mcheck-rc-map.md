# mcheck-rc-map: map of the proof of Theorem 5.3 (hyp:RC) in sections 7-9

Status: IN PROGRESS (map of sec 7 written; sec 8-9 pending). Conclusion is written last.

## Map

Columns: tex lines | label | claim | kind | size | depends on | GZ/TYZ contact.
"Own" = Elliot's own argument. Print locators are as the manuscript gives them.

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
