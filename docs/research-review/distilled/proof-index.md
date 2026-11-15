# Proof index

Standalone proof notes found in the review records (81 after removing byte-identical copies), each compared against `manuscripts/quartic_v17.tex` by text search. See README.md for the summary and limits.


## Batch 1


Method: each proof file was read in full; the manuscript (45,035 lines) was searched with grep for distinctive terms and the hits were read in context. Line numbers are lines of `manuscripts/quartic_v17.tex`. "main NNNN" line references inside the proof files point to older manuscripts (V14-era) and do not match V17 line numbers. V17 Part I (to about line 5300) is the 214-variable argument; Part II (from about line 5300) is the retained Version 16 body. "PARTIAL" means the statement is used in V17 but the note's argument is not reproduced there. "NOT FOUND" means my searches failed, not that the material is certainly absent.

### docs/research-review/proof-sources/ceggps-connections-v1/o3/PROOF.md
- path: docs/research-review/proof-sources/ceggps-connections-v1/o3/PROOF.md
- claim: (a) For G=GL2(Q5), every nonordinary absolutely irreducible admissible unitary Banach representation Pi with nonzero irreducible locally algebraic vectors satisfies the Breuil-Mezard "RED" condition (dim R(Pi) <= 1). (b) RED plus End_G(Pi)=E and multiplicity one of a K-type V gives dim Hom_K(V,X) <= 2 for first-order extensions 0->Pi->X->Pi^m->0 with dim Hom_G(Pi,X)=1; the note then states how these enter the Breuil-Mezard / Hu-Tan cycle arguments.
- author / date: /root/astra_v14_baseline_compiler, 2026-11-08
- status: new author proposal; Sections 3-4 await independent review; "No independent acceptance or current manuscript incorporation is claimed"
- published theorems relied on: Dospinescu (Compositio 151, 2015) Thm 1.3, Props 1.4-1.5 (author-text version only, final text not compared); Breuil-Mezard / Paskunas BM arXiv 1209.5205v3 (2.42, 4.14-4.21, 6.5/6.6); Hu-Tan 4.2, 4.9, 4.10, 5.11; Colmez VI.6.50; Henniart
- in_v17: NOT FOUND. Searched "Dospinescu", "Breuil--M / Mezard / Paskunas / Colmez / Banach", "locally algebraic", "ceggps": no relevant hits. The only related text is lines 5794-5801, where the prime-five modularity input is taken from Calegari ICM 2022 p.624 / Pan 2022 and the manuscript says Pan's "local Hu--Tan ring calculations" are not reproved.
- note: This is a proposed alternative route for re-deriving the p=5 modularity input from Breuil-Mezard/Hu-Tan. V17 does not use it; it imports the published statement instead. The note itself flags two unresolved source-version qualifications (final Duke and Compositio texts not obtained).

### research/quartic214/PROOF.md
- path: research/quartic214/PROOF.md
- claim: Assembly of the 214-variable quartic family: with A_N=149^(2N+1) and P_N the sum of squares of 188 primitive quadratic rows in 214 coordinates, there is an (ineffective) N0 such that for all N>=N0 and all rational x, P_N has a rational zero over x iff x is an integer; degree 4, content 1, coefficient height A_N^2+1 for N>=53.
- author / date: not stated ("author assembly for fresh public review")
- status: proposed; all applications "require review of this exact public serialization"; no reviewer approval
- published theorems relied on: Faltings, Poincare reducibility, Kato (full index / limiting class), Green-Tao-Ziegler GI and Gaussian primes, published p=5 modularity, Carayol, Lucas lower bound, RC theorem (all via linked sub-proofs)
- in_v17: YES. The text is incorporated almost verbatim in Part I: theorem at lines 84-103 (label q214:theorem), assembly at lines 2052-2100 (family and domains 2052-2056, source objects 2060, application table 2062-2075, soundness 2081-2089, completeness following), with P01-P20 at about 2228-2312 and C01-C13 at about 3309-3346.
- note: The H3 step uses height-averaging.md; the "historical quotient route" in height-supplier.md H3 is declared superseded. Completeness is only claimed on the q != 0 stratum (no bijection with the discarded q=0 witnesses). N0 is ineffective; the N>=53 statement is only about coefficient height.

### research/version14/evidence/atkin-cusp-input-001/PROOF.md
- path: research/version14/evidence/atkin-cusp-input-001/PROOF.md
- claim: The Atkin-Lehner matrix M=[[ea,b],[Nc,ed]] (N=er, gcd(e,r)=1, det e) normalizes Gamma0(N) and M^2/e lies in Gamma0(N), so W permutes the cusps; hence pi(W infinity) lies in phi(C_N) and is killed by the annihilator C_pi.
- author / date: not stated
- status: not stated (scoped "proves only cusp permutation and the resulting cuspidal constant")
- published theorems relied on: none for the computation; Manin-Drinfeld finiteness is a separate input
- in_v17: PARTIAL. Lines 8970-8979 state the formula pi(Wx)=[w]pi(x)+pi(W infinity) with the constant in phi(C_N), citing Manin-Drinfeld via Elkik; lines 20022 and 20235-20237 reuse it. The explicit conjugation computation showing W normalizes Gamma0(N) and permutes cusps is not reproduced (searched "normalizes", "Atkin", "cusp").
- note: The eigen-action of W on the differential is an explicit hypothesis, not proved here.

### research/version14/evidence/beta-local-norm-published-current/PROOF.md
- path: research/version14/evidence/beta-local-norm-published-current/PROOF.md
- claim: For a finite extension E/K of characteristic-zero local fields (E/K not necessarily normal), rec_K(N_{E/K}u)=i_ab(rec_E(u)); applied with K=Q2, E=F=L_v this gives beta^4=1 on O_F^*.
- author / date: not stated
- status: not stated; described as a replacement for an online-course-note input (ACTIVE-BETA-LOCAL-NORM)
- published theorems relied on: Milne, Arithmetic Duality Theorems 2nd ed., I(1.1b), Example 1.6(b), Remark 1.5(a)
- in_v17: PARTIAL. Lines 6635-6637 say "local reciprocity and the norm map give beta^4=1 on the units of F" with no citation or proof at that point; the corestriction/cup-product derivation is absent (searched "class formation", "norm of units / N_{F/Q_2}", "projection formula"). Milne ADT is cited at line 6515 for a different fact.
- note: Handles nonnormal E/K and avoids cancelling d in Q/Z. The manuscript sentence has no source attached, which is exactly the gap this note was written to fill.

### research/version14/evidence/beta-quantitative-join-001/PROOF.md
- path: research/version14/evidence/beta-quantitative-join-001/PROOF.md
- claim: For the first (discriminant-six) beta family, with G0=116064000000, E0=10(D G0)^2, U0=4(D G0)^2, Q=R^(R E0), R>=max(D,max S,10^12): the kernel field satisfies [L':Q] <= Q M and the primitive level satisfies N <= Q M^2.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "new connecting-proof proposal, not an independent acceptance"
- published theorems relied on: Serre, Local Class Field Theory (Cassels-Frohlich VI 4.1-4.3); Silverberg-Zarhin 1995 Thm 3.5; Carayol; Milne CFT v4.03 V Prop 3.3 (norm functoriality); formal logarithm
- in_v17: YES. Constants at lines 5575-5580; argument at lines 6604-6667 (Eisenstein derivative/Herbrand at 6610-6617, Silverberg-Zarhin at 6626, U0 at 6631, beta^4=1 and (U_F^{e+1})^4=U_F^{3e+1} at 6635-6641, level bound R^{RE0}M^2=QM^2 at 6667). A restatement is also in Part I around 2590-2596.
- note: Identical to beta-quantitative-join-002 except for the Milne locator; 002 says the "V Proposition 3.3" locator used here points to the global ideal diagram, not the local one. Treat 002 as the corrected copy.

### research/version14/evidence/beta-quantitative-join-002/PROOF.md
- path: research/version14/evidence/beta-quantitative-join-002/PROOF.md
- claim: Same as beta-quantitative-join-001: [L':Q] <= Q M and N <= Q M^2 for the first beta family with the manuscript constants.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "new connecting-proof proposal, not an independent acceptance"
- published theorems relied on: as 001, but local norm functoriality is Milne CFT v4.03 III Lemma 3.2 (p.107)
- in_v17: YES. Lines 5575-5580 and 6604-6667 (see 001).
- note: Corrects the citation in 001. In V17 the norm step (6635-6637) carries no citation at all, so neither locator reached the manuscript.

### research/version14/evidence/cj-global-atkin-identification-current/PROOF.md
- path: research/version14/evidence/cj-global-atkin-identification-current/PROOF.md
- claim: For n=p^e exactly dividing N, the operation (E,C_N) -> (E/C_n, phi(E[n])+phi(C_m)) equals the published Atkin-Lehner W_n on noncuspidal moduli points; in the split conductor-one CM setting it exchanges the two O-eigensummands (local normalizer coset [[0,1],[-p^e,0]]), and it reduces compatibly at q=ell_0 not dividing N as a finite etale degree-n quotient preserving the q-orientation.
- author / date: /root/v14_h6_coverage (calculation suggested by /root/v14_sign_conductor); date not stated
- status: "author proposal, not an independent approval"
- published theorems relied on: Atkin-Lehner 1970 (exact-divisor matrix); dual-isogeny identities; modular interpretation and good finite diagram as incoming data
- in_v17: PARTIAL. The local normalizer is used at lines 21028-21040 ("use the local Atkin--Lehner normalizer. It reverses the selected root ... reduced norm has valuation e") and the two orientations at 20893-20905, but the global identification (lattice computation s z = n d z' - b, quotient equals W_n) is not found (searched "exact-divisor", "E_z / Z z+Z", "dual isogeny", "eigensummand"). The finite-etale quotient argument at lines 35252-35262 is stated only for isogenies of degree prime to qN.
- note: The note says explicitly that the old "degree prime to qN" profile must not be applied wholesale, because here n divides N; V17's simultaneous-good-model subsection still has only the prime-to-qN case. This is a candidate missing justification.

### research/version14/evidence/cj-level-normalizer-001/PROOF.md
- path: research/version14/evidence/cj-level-normalizer-001/PROOF.md
- claim: In the split local Eichler order R=[[Z_p,Z_p],[p^e Z_p,Z_p]], w=[[0,1],[-p^e,0]] normalizes R, has reduced-norm valuation e, and conjugation by w swaps the selected eigen-projector so the selected root r becomes -r (including p=2 via e_x=(1+x)/2); hence the root-weight ratio is alpha_p(-1)=w_{p^e} chi_hstar(p)^e.
- author / date: not stated
- status: not stated ("establishes the local matrix, selected-root and norm assertions only")
- published theorems relied on: none
- in_v17: PARTIAL. Projectors (x+r)/(2r), dyadic e_x=(1+x)/2, and (O.3) alpha_p(-1)=w_{p^e}chi_{h_*}(p)^e are at lines 20248-20282; the consequence is asserted at 21030-21038. The explicit matrix w and the conjugation w y w^{-1} are not written out (the only "w" matrix found is [[0,1],[-1,0]] at 20490; line 21524 has a similar remark for K_0(p)).
- note: The global identification of this local normalizer with the geometric Atkin-Lehner correspondence is explicitly not proved here (see the cj-global-atkin entries).

### research/version14/evidence/current-h6-original-datum-001/PROOF.md
- path: research/version14/evidence/current-h6-original-datum-001/PROOF.md
- claim: For the six-contact problem (C={0,-15,-20,-24,-30,-60}, S containing primes <=324), composing the discriminant-six principal datum (B=(2,-3), mu=2j+ij), the full-three cover of degree <=324, and the tame pullback J(u)=-57600F^2/G^6 yields a principally polarized O-surface A/K with K/Q normal of degree <=324!, unramified outside S union supp(M_S(u)), with good reduction outside S.
- author / date: /root/v14_sign_conductor, run 01a1bed7-...; date not stated
- status: "new bounded composition and schema normalization"; earlier decisions retain their own provenance
- published theorems relied on: Baba-Granath; Lin-Yang (Example 30); PEL moduli/descent theorems (Milne 2005, Buzzard 1997 via suppliers)
- in_v17: YES. Lines 5564 (contact set), 5575 (F0=324!), 5810-5870 (datum, 6E vs E remark at 5823, coordinate 0, infinity, -16/27 at 5843), 6058-6076, 6266-6296 (pullback, G^6-97200F^2=H^2 at 6276, [K:Q]<=324! at 6288).
- note: The printed Baba-Granath form is 6E and is not principal; the manuscript uses E. I did not check every sub-step (e.g. the normalizer index bound 4*3^4=324 was not found by a literal search).

### research/version14/evidence/current-reviewed-003/suppliers/all-prime-compatibility-sol-001/PROOF.md
- path: research/version14/evidence/current-reviewed-003/suppliers/all-prime-compatibility-sol-001/PROOF.md
- claim: For each of the two original families (eta=beta or b) and every rational prime ell, the original factor r_ell is isomorphic to the ell-adic realization U_{f,ell} of the same primitive weight-two form f identified at ell=5.
- author / date: not stated
- status: not stated (builds on "accepted" prime-five conclusion; previous r3-only proof left unchanged)
- published theorems relied on: Milne, Abelian Varieties Prop 12.9 (degree polynomial); Chebotarev; characteristic-zero trace criterion; classical good-prime trace formula
- in_v17: YES. Beta family: lines 6585-6600 (trace transport, Chebotarev, irreducibility of U_{f,ell}). b family: lines 13400-13462 (e_p, relative p-Frobenius, Milne 12.9 at 13450, trace formula). Part I restatement near 2560-2574.
- note: Requires the separate all-prime irreducibility argument. Gives no conductor or level bound.

### research/version14/evidence/current-reviewed-003/suppliers/all-prime-irreducibility-matrix-units-002/PROOF.md
- path: research/version14/evidence/current-reviewed-003/suppliers/all-prime-irreducibility-matrix-units-002/PROOF.md
- claim: If End^0(A_Qbar)=B with all endomorphisms defined over L', then for every rational prime ell (including 2) the original matrix-unit factor r_ell of the normalized family is absolutely irreducible on G_Q.
- author / date: not stated
- status: not stated
- published theorems relied on: Faltings (semisimplicity and endomorphism theorem)
- in_v17: YES (condensed). Lines 13408-13416 for general ell; lines 5628-5636 for r_5.
- note: The manuscript gives the argument in a few sentences; the note spells out coefficient-extension of the commutant and descent of invariant subspaces from the algebraic closure. Full endomorphism algebra and common field of definition are hypotheses.

### research/version14/evidence/current-reviewed-003/suppliers/v14-resume-arithmetic-author-proxy-002/PROOF.md
- path: research/version14/evidence/current-reviewed-003/suppliers/v14-resume-arithmetic-author-proxy-002/PROOF.md
- claim: For the first beta family: rho_ell = R_ell + R_ell via matrix units fixed over one number field C, R_ell is absolutely irreducible for every ell, and r_ell is isomorphic to U_{f,ell} for every ell; hence the Artin conductor at p can be computed with any auxiliary ell != p.
- author / date: not stated ("Author proposal")
- status: "Author proposal, not an independent acceptance"; target was PROPOSED.tex lines 1163-1408
- published theorems relied on: Faltings; Milne Abelian Varieties Prop 12.9; Chebotarev; trace criterion
- in_v17: YES. Lines 6552 (matrix units), 6585-6604 (all-prime comparison and "for each residue prime p choose ell != p", Carayol at 6604).
- note: Removes the need for a named quadratic coefficient field E in the beta family; warns that a fixed r_3 cannot be used for the conductor at p=3.

### research/version14/evidence/current-reviewed-003/v14-sign-conductor-002/PROOF.md
- path: research/version14/evidence/current-reviewed-003/v14-sign-conductor-002/PROOF.md
- claim: For quasi-isogenies mu_sigma on an abelian surface with rational discrepancy c(sigma,tau), the normalized degree D(u)=deg([m]u)/m^4 is well defined and multiplicative with D(cu)=c^4 D(u), so normalizing by d_sigma=D(mu_sigma)^(1/4)>0 gives a cocycle with values in {+1,-1}; also, isomorphic ell-adic representations (ell != p) have equal Artin conductor at p.
- author / date: not stated ("Author proposal")
- status: "Independent review is pending"; makes no claim that Item 2.9 or Version 14 is accepted
- published theorems relied on: Milne, Abelian Varieties (1986) Thm 8.2 (deg [n]=n^(2g), multiplicativity)
- in_v17: YES. Line 2506 (D(mu)=deg([n]mu)/n^4, positive fourth root), lines 5590-5600 (lemma hypotheses with c in Q^x), line 12861 (Milne Thm 8.2 cited), conductor restriction at 6600-6604.
- note: The note stresses what is not proved: that the sign cocycle splits, or that a splitting cochain has finite image. The manuscript handles that separately (obstruction check near 2516 / 6504-6515).

### research/version14/evidence/cyclotomic-zero-local-001/PROOF.md
- path: research/version14/evidence/cyclotomic-zero-local-001/PROOF.md
- claim: A nonzero f in Z_2[[t]][1/2] has f(zeta-1)=0 for only finitely many 2-power roots of unity zeta; hence a torsion class over this ring has nonzero specialization at only finitely many finite-order cyclotomic characters, so the retained Euler-system class is non-torsion in each sign component.
- author / date: not stated
- status: not stated
- published theorems relied on: none for the lemma; Kato 13.5(2) and reciprocity are separate inputs
- in_v17: PARTIAL. Lines 18832-18843 use it in one sentence ("a nonzero annihilating power series has only finitely many cyclotomic zeros"); the valuation argument (dominant term a_d z^d for small v_2(z), v_2(zeta-1)=1/2^(n-1)) is not reproduced.
- note: Standard Weierstrass-preparation-type fact; the note proves it directly for bounded-denominator series.

### research/version14/evidence/dual-exponential-trace-001/PROOF.md
- path: research/version14/evidence/dual-exponential-trace-001/PROOF.md
- claim: For a de Rham representation V of G_K and finite L/K, exp*_K(cor z)=Tr_{L/K}(exp*_L z); applied to W=V tensor chi this gives the unnormalized chi-weighted sum of exp*(z_D) with no division by the degree.
- author / date: not stated
- status: not stated
- published theorems relied on: Kato, Asterisque 295 (2004), sections 9.2-9.3
- in_v17: PARTIAL. Lines 18740-18746: "Dual exponential commutes with corestriction, whose de Rham map is field trace", giving (K12). The explicit cocycle proof of cor(res(alpha) cup m)=alpha cup cor(m) and the check that the twist W (not V) is used at the descended endpoint are not reproduced.
- note: The W-versus-V point (the trace identity must be applied to the twisted representation) is the kind of detail that is easy to lose; V17 states only the conclusion.

### research/version14/evidence/elementary-inputs-current/PROOF.md
- path: research/version14/evidence/elementary-inputs-current/PROOF.md
- claim: Supplies four elementary connections: (A055) positivity, absolute value and nonnegative-index predicates via Lagrange four squares; (A056) division-polynomial recurrences and the cleared scalar equations 2y([n]P)psi_n^4=psi_{2n}, x([n]P)psi_n^2=phi_n; (A057) termination of the fixed prime catalogue modulo W=4*prod_{p<=324}p; (A058) for K0=Q(sqrt2), E:y^2=x^3-d^2x with d=75-53s: class number one, unit squareclasses, explicit two-isogeny kernel identification, [E(K0):2E(K0)]=8, and odd free index of R.
- author / date: not stated
- status: "does not itself claim whole-proof acceptance"; historical closure batches retained as author derivations
- published theorems relied on: Lagrange four squares (via Matiyasevich 1971 p.2); Silverman AEC 2nd ed. Exercise III.3.7 with official errata; Bennett-Martin-O'Bryant-Rechnitzer (primes in progressions); Silverman X Example 4.8
- in_v17: PARTIAL. A055: lines 5366-5375, 5548, 12609-12613. A056: formulas at 5395-5412, but the manuscript cites Sutherland's MIT lecture notes (line 5399), not Silverman Exercise III.3.7. A057: lines 5414-5416 say only "Dirichlet's theorem ensures termination" (BMOR is cited elsewhere, line 12380). A058: condensed at 5452-5476 (norm-Euclidean, units, descent images, odd index at 5475-5476); the explicit kernel computation ker(alpha_b)=phi-hat(E_{-4b}(K)) with the maps phi, phi-hat is not reproduced.
- note: This note says the Sutherland lecture-note source and the Minkowski-bound argument were replaced by published sources and a direct proof. V17 dropped Minkowski but still cites Sutherland for division polynomials, so the source replacement for A056 did not reach the manuscript. The Silverman Prop X.4.9 misprint (a^2-b for a^2-4b) is flagged and avoided.

### research/version14/evidence/finite-field-halving-inputs-001/PROOF.md
- path: research/version14/evidence/finite-field-halving-inputs-001/PROOF.md
- claim: (1) Over F_ell (ell odd), x^2+y^2=s has ell-chi(ell) solutions for s != 0 and ell+(ell-1)chi(ell) for s=0. (2) On y^2=(x-e1)(x-e2)(x-e3) over a field of characteristic != 2, if 2Q=(e_i,0) then every e_i-e_j is a nonzero square; for roots 0, ell, -3ell over F_p (p=1 mod 4, ell a nonsquare) the two-primary subgroup therefore has order four.
- author / date: not stated
- status: not stated
- published theorems relied on: none (chord-and-tangent group law is an incoming premise)
- in_v17: PARTIAL. Halving condition used at lines 22192-22198 (stated, not proved); fibre count ell-chi(ell) used at line 25375 (not proved). Searched "halv / half of", "ell-chi(ell)", "norm fibre", "2 ell-1".
- note: Only necessity of the square condition is proved, and only necessity is used.

### research/version14/evidence/finite-kummer-current/PROOF.md
- path: research/version14/evidence/finite-kummer-current/PROOF.md
- claim: For a field F containing mu_n (char prime to n) and a finite subgroup B of F*/F*^n, the extension L=F(B^(1/n)) is Galois and Gal(L/F) x B -> mu_n is a perfect pairing, so every homomorphism B -> mu_n is realized by an automorphism; F may be an infinite extension such as K(mu_{2^infinity}).
- author / date: not stated
- status: "new local proof" replacing an online-note supplier
- published theorems relied on: none (elementary Galois theory, structure of finite abelian groups)
- in_v17: PARTIAL. Lines 9584-9593: after checking the prescriptions respect every Kummer relation, the manuscript says "Kummer theory therefore gives the specified automorphism"; the pairing proof is not reproduced and no source is cited at that point.
- note: The lemma gives no independence of radicands, descent to finite layers, or Chebotarev statement; the manuscript's use is consistent with that.

### research/version14/evidence/gaussian-current-inverse-inputs-001/PROOF.md
- path: research/version14/evidence/gaussian-current-inverse-inputs-001/PROOF.md
- claim: Source/application note: Green-Tao Proposition 10.1 (relative inverse theorem under GI(k) with a pseudorandom majorant) applies with r=max(s,4), k=r-1, C_*>=20, and Appendix B (B.12)-(B.15), Lemma B.5 convert the U^s[L] lower bound alpha*delta/2 into a U^r[L] lower bound alpha*delta/(4C_*).
- author / date: not stated ("author source/application proposals")
- status: proposal
- published theorems relied on: Green-Tao, Linear equations in primes (Annals 171, 2010), Prop 10.1, Appendix B (B.12)-(B.15), Lemma B.5
- in_v17: YES. Lines 24574-24595 (Prop 10.1, pseudorandomness, Appendix B (B.13)-(B.15)), 24597-24604 (majorant lemma with C_*>=20), 24795-24808 (bound alpha*delta/(4C_*), application with k=r-1).
- note: The manuscript cites (B.13)-(B.15) rather than (B.12)-(B.15)/Lemma B.5; minor locator difference. GI(k), the majorant lemma and the nilsequence estimate are separate.

### research/version14/evidence/generic-kummer-current/PROOF.md
- path: research/version14/evidence/generic-kummer-current/PROOF.md
- claim: For an elliptic curve E over a characteristic-zero field F and n=2^a, the Kummer sequence 0 -> E(F)/nE(F) -> H^1(F,E[n]) -> H^1(F,E)[n] -> 0 is exact and natural (restriction, field automorphisms); consequently an n-multiple has trivial Kummer class, and a class that becomes Kummer over an unramified F'/F is Kummer over F after multiplying by c_E.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "New bounded connecting proof; source-set adoption and independent review remain separate"
- published theorems relied on: Silverman AEC III.4 (isogenies surjective), Example 4.1, Prop 4.2(a)
- in_v17: PARTIAL. The local step is used at lines 9091-9094 ("If a class v in H^1(F,B[2^a]) becomes Kummer over F' ... Thus c_B v is Kummer"), with (H10) at 9069-9074 and the derivative class at 9002-9065; the cocycle-level proof of exactness is not reproduced.
- note: Standard; covers residue characteristic 2 and needs no good reduction.

### research/version14/evidence/global-atkin-root-sign-001/PROOF.md
- path: research/version14/evidence/global-atkin-root-sign-001/PROOF.md
- claim: For the weight-two newform f of E on Gamma0(N), f|W_N = lambda f with lambda = product of w_{p^e}, and the Mellin transform gives functional-equation sign -lambda; comparing bad Euler factors shows L(E,s) and L(f,s) have the same order at s=1, so w(E) = -product_{p^e || N} w_{p^e}.
- author / date: not stated
- status: not stated
- published theorems relied on: Atkin-Lehner 1970 Lemma 9, Theorem 3; Silverman C.16 (bad factors, functional equation)
- in_v17: PARTIAL. Line 20335 states "w(E)=-prod w_{p^e}" as "more explicitly" with no proof or citation; searched "Mellin", "it/sqrt", "Lemma 9 / Theorem 3(iii)".
- note: Careful about normalization (determinant-normalized slash action = Atkin-Lehner's k=1). Avoids assuming equality of full L-series by comparing bad factors. Supersedes the shorter release-completion-017 version.

### research/version14/evidence/heegner-finite-field-current/PROOF.md
- path: research/version14/evidence/heegner-finite-field-current/PROOF.md
- claim: For finite fields k'/k with cyclic Galois group G, H^1(G,k')=0 by a direct trace argument (no division by the degree); moreover k' is a free k[G]-module (normal basis) and all positive cohomology vanishes. Applied to successive formal-group quotients in the Heegner local cocycle correction.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "New local proof; pending independent review and explicit source extension"
- published theorems relied on: none (formal-filtration identification is a separate input, Silverman IV.3.2(a))
- in_v17: PARTIAL. Lines 9081-9089: "each successive formal quotient is an additive copy of the residue field of F' [Silverman IV.3.2(a)]. A normal basis makes this an induced module, so its positive-degree cohomology vanishes." The elementary proofs are not reproduced.
- note: Extended version of the release-completion-013 note; it adds the normal-basis and higher-cohomology proof matching the manuscript's wording. Works when the residue characteristic divides the degree.

### research/version14/evidence/heegner-kernel-specialization-current/PROOF.md
- path: research/version14/evidence/heegner-kernel-specialization-current/PROOF.md
- claim: For a degree-ell raising isogeny f between CM elliptic curves with common good models at an inert prime ell, the extended f is finite locally free of degree ell, its special fibre is purely inseparable with kernel the relative Frobenius kernel, and the prime-to-ell cyclic N-level subgroup extends as finite etale and is transported by the same Frobenius.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "New bounded connecting proof; independent review and source-scope adoption pending"
- published theorems relied on: BLR Neron Models 1.2/1, 1.2/8; Silverman II.2.12, III.4.10, III.6.1-6.4, V.3.1, VII.5.5, VII.7.2; Stacks 02LS, 039E, 0BFG, 0BFH, 02GM; Fowler (CM integrality)
- in_v17: PARTIAL. Lines 8989-8996 assert that each cyclic raising isogeny "specializes to the quotient by ... the relative Frobenius kernel" and that the N-subgroup specializes by the same Frobenius map, without the flatness/degree argument. The good-model subsection at 35252-35262 treats only isogenies of degree prime to q. Searched "raising", "Frobenius kernel", "02LS/039E", "separable degree".
- note: This is a degree-ell isogeny in residue characteristic ell, so the etale argument in the manuscript does not cover it; the note supplies the missing flat (non-etale) argument.

### research/version14/evidence/local-generator-and-index-inputs-001/PROOF.md
- path: research/version14/evidence/local-generator-and-index-inputs-001/PROOF.md
- claim: For E:y^2=x^3-d^2x over Q(sqrt2), d=75-53s, and the fixed point P_0: formal-logarithm valuations give that n=N_s^4 m_0 (m_0 the product of actual reduction orders, m_0<=N_s^6) satisfies the divisibility guard, so the least successful index M_0 exists with M_0<=N_s^10; and the duplication forms on C:y^2=x^3-delta^2x give 4h_x(P)-log 392 <= h_x(2P) <= 4h_x(P)+log 676.
- author / date: /root; date not stated
- status: "Proposed for independent review"
- published theorems relied on: Silverman AEC IV.1.1, IV.5.5, IV.6.2-6.4, VII.2.1-2.2, V.1.1 (Hasse)
- in_v17: YES. Lines 12396-12430 (reduction at 7, Hasse, m_0<=N_s^6, valuations 2+8v_p(N_s) and 6+16v_2(N_s), M_0<=N_s^10); lines 5478-5491 (duplication forms, bounds 676, log 392).
- note: No nontorsion premise is used for totality of the search; the dyadic equation is not assumed minimal. Cites "Proposition 5.5, p.129" where the overlay copy cites "Corollary 5.5, p.128".

### research/version14/evidence/local-twist-factors-002/PROOF.md
- path: research/version14/evidence/local-twist-factors-002/PROOF.md
- claim: For quadratic twists E^h (h odd squarefree) the comparison between the fixed differential and a minimal invariant differential at 2 has bounded valuation (finitely many 2-adic squareclasses); local Euler factors at primes dividing 2N form a finite nonzero list; at a good prime q | h the twist has additive reduction with local factor 1; at an unused good prime the factor is #E^h(F_q)/q.
- author / date: not stated
- status: not stated
- published theorems relied on: Silverman AEC Table 3.1, VII.1.3, VII.5.1, VII.7.1, Appendix C.16
- in_v17: PARTIAL. Lines 18818-18826 give a five-sentence summary of exactly these conclusions ("This proves (K3)"); the supporting arguments (Hensel lifting of squareclasses, the additive-reduction argument via integral j and VII.5.1, the point-count identity) are not reproduced. Searched "additive reduction" (0 hits), "VII.5.1 / VII.7.1 / C.16", "minimal invariant differential".
- note: The claim "at a good active prime the local L-factor is one" in V17 rests on the additive-reduction argument that exists only in this note.

### research/version14/evidence/polarization-pairing-input-001/PROOF.md
- path: research/version14/evidence/polarization-pairing-input-001/PROOF.md
- claim: For an abelian variety A over a number field F with an F-polarization lambda, V_5(A) carries a G_F-equivariant nondegenerate alternating pairing with values in Q_5(1) (multiplier epsilon_5), with no assumption that lambda is principal, of degree prime to 5, or that A has good reduction at 5.
- author / date: not stated ("Author proposal")
- status: author proposal; source-level input to an already reviewed determinant calculation
- published theorems relied on: Milne, Abelian Varieties (1986) section 16: Lemma 16.1, Lemma 16.2(e), Prop 16.6
- in_v17: PARTIAL. Lines 5743-5744: "put alpha=det(r_5)/epsilon_5. The polarization pairing on V_5(A) gives ..."; I found no citation of Milne section 16 (searched "16.2 / 16.6 / Lemma 16", "Weil pairing / Tate pairing"). I did not read the lines following 5744 in full.
- note: The point of the note is the exceptional case 5 | deg(lambda), handled by inverting V_5(lambda) rationally.

### research/version14/evidence/qroot2-class-units-current/PROOF.md
- path: research/version14/evidence/qroot2-class-units-current/PROOF.md
- claim: For K=Q(sqrt2): O_K=Z[sqrt2] (discriminant 8), it is norm-Euclidean hence a PID, every unit is uniquely +/-(1+sqrt2)^k, there are four unit squareclasses, and every totally positive unit is a square.
- author / date: not stated
- status: "new local proof" replacing general Minkowski and unit-rank inputs
- published theorems relied on: none
- in_v17: PARTIAL. Lines 5452-5454 state the three conclusions in three sentences ("norm-Euclidean, hence has class number one"; units; sign vectors); the proofs (integrality via trace/norm parity, Euclidean rounding, unit reduction into [1,epsilon)) are not reproduced.
- note: Elementary and standard; the manuscript no longer mentions Minkowski (0 hits), consistent with this replacement.

### research/version14/evidence/quadratic-gauss-local-001/PROOF.md
- path: research/version14/evidence/quadratic-gauss-local-001/PROOF.md
- claim: For a primitive quadratic character chi of conductor D, S(a)=chi(a)tau for units a and S(a)=0 for nonunits, |tau|^2=D, tau^2=chi(-1)D; hence for odd squarefree signed h, tau(chi_h)^2=Delta_h and tau(chi_h)/sqrt(h) lies in {1,-1,2,-2}.
- author / date: not stated
- status: not stated
- published theorems relied on: none
- in_v17: PARTIAL. Lines 18809-18815 state tau(chi)^2=Delta_h and that the basis-change ratio "is one or two up to sign"; line 18737 notes imprimitive Gauss sums can vanish. The proof is not reproduced.
- note: No exact sign of the Gauss sum is claimed or needed.

### research/version14/evidence/release-completion-005/v14-quartic-theorem-author-001/PROOF.md
- path: research/version14/evidence/release-completion-005/v14-quartic-theorem-author-001/PROOF.md
- claim: For every rational X, the specified quartic P299 (298 witnesses, 6630 monomials, max coefficient 186624*3^(2^26)) has a rational zero above X iff X is an integer, and the same holds for P314 (313 witnesses, 6672 monomials, coefficients below 2^6496); the note records how the soundness and completeness arguments compose.
- author / date: /root/v14_h6_coverage, run 01a1bedc-...; date not stated
- status: author record; "awaits independent composition review and final graph reconciliation"
- published theorems relied on: none directly (composition of retained contracts)
- in_v17: YES, as Part II material. Theorem at lines 27924-27938; coefficient facts at 28807 and 28859; summary at 5184.
- note: V17's headline theorem is the 214-variable family; line 115 says the 222- and 314-variable theorems "retain their own scope; they are not the polynomial" of the main theorem. I did not verify that the composition narrative in this note matches the Part II proof step by step.

### research/version14/evidence/release-completion-006/v14-elementary-input-connections-author-001/overlay/research/version14/evidence/elementary-inputs-current/PROOF.md
- path: research/version14/evidence/release-completion-006/v14-elementary-input-connections-author-001/overlay/research/version14/evidence/elementary-inputs-current/PROOF.md
- claim: Earlier draft of elementary-inputs-current (A055-A058), with the same mathematics but different suppliers: division polynomials from Sutherland's MIT 18.783 lecture notes, primes in progressions from Milne's CFT course notes (Thm V.2.2), class number and units of Q(sqrt2) from Milne's ANT notes (Minkowski bound, unit theorem).
- author / date: not stated ("new bounded author proposal")
- status: author proposal; "No canonical file is changed"
- published theorems relied on: Lagrange (via Matiyasevich 1971); Sutherland lecture notes; Milne CFT v4.03 and ANT v3.08 course notes; Silverman X Example 4.8
- in_v17: SUPERSEDED. The non-overlay elementary-inputs-current says the Sutherland supplier is "retained only as historical provenance" and the Minkowski expression is "a superseded method". Manuscript status is as for that entry (PARTIAL: lines 5366-5375, 5395-5416, 5452-5476).
- note: V17 line 5399 still cites Sutherland's lecture notes for the division-polynomial normalizations, i.e. the manuscript matches this older sourcing for A056. This draft also says it "does not claim epsilon is a chosen fundamental unit", whereas the later note proves it.

### research/version14/evidence/release-completion-006/v14-local-bounds-connections-root-001/overlay/research/version14/evidence/local-generator-and-index-inputs-001/PROOF.md
- path: research/version14/evidence/release-completion-006/v14-local-bounds-connections-root-001/overlay/research/version14/evidence/local-generator-and-index-inputs-001/PROOF.md
- claim: Same as local-generator-and-index-inputs-001: M_0<=N_s^10 via formal-logarithm valuations and reduction orders, and the duplication height bounds with constants log 392 and log 676.
- author / date: /root; date not stated
- status: "Proposed for independent review"
- published theorems relied on: Silverman AEC IV.1.1, IV Corollary 5.5 (p.128), IV.6.2-6.4, VII.2.1-2.2, V.1.1
- in_v17: YES. Lines 12396-12430 and 5478-5491.
- note: Textually identical to the non-overlay copy except for the Silverman locator (Corollary 5.5 p.128 here, Proposition 5.5 p.129 there) and one variable name in D4. One of the two locators is wrong; not resolved here.

### research/version14/evidence/release-completion-013/v14-heegner-finite-field-input-author-001/overlay/research/version14/evidence/heegner-finite-field-current/PROOF.md
- path: research/version14/evidence/release-completion-013/v14-heegner-finite-field-input-author-001/overlay/research/version14/evidence/heegner-finite-field-current/PROOF.md
- claim: For finite fields k'/k, H^1(Gal(k'/k),k')=0 by the trace argument, applied to the successive formal quotients; offered as a direct replacement for invoking normal-basis inducedness at the H^1 step.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "New local proof; pending independent review and explicit source extension"
- published theorems relied on: none
- in_v17: PARTIAL. Lines 9081-9089 use the fact but justify it by "A normal basis makes this an induced module", i.e. by the argument this note proposed to replace.
- note: Shorter earlier version of heegner-finite-field-current, which adds the normal-basis proof instead. Says explicitly that it "neither claims a normal-basis theorem nor supplies ... higher cohomology", while the manuscript sentence claims positive-degree vanishing.

### research/version14/evidence/release-completion-015/v14-heegner-kernel-specialization-author-001/overlay/research/version14/evidence/heegner-kernel-specialization-current/PROOF.md
- path: research/version14/evidence/release-completion-015/v14-heegner-kernel-specialization-author-001/overlay/research/version14/evidence/heegner-kernel-specialization-current/PROOF.md
- claim: Same core statement as heegner-kernel-specialization-current: the degree-ell raising isogeny extends finite locally free of degree ell and its special fibre has kernel the Frobenius kernel; the common good model and the level-subgroup extension are taken as retained inputs.
- author / date: /root/v14_arithmetic_author; date not stated
- status: "New bounded connecting proof; independent review and source-scope adoption pending"
- published theorems relied on: BLR 1.2/1, 1.2/8; Silverman II.2.12, III.4.10, III.6.1-6.4, V.3.1; Stacks 02LS, 039E
- in_v17: PARTIAL. Lines 8989-8996 assert the conclusion only (see the non-overlay entry).
- note: Earlier, shorter version; the non-overlay copy additionally constructs the common good model (Fowler, Silverman VII.5.5, VII.7.2) and proves the level-subgroup extension (Stacks 0BFG, 0BFH, 02GM).

### research/version14/evidence/release-completion-017/h5-geometric-isogeny-author-001/PROOF.md
- path: research/version14/evidence/release-completion-017/h5-geometric-isogeny-author-001/PROOF.md
- claim: In the discriminant-210 fibre, each non-CM fibre surface A and conjugate A_sigma admit an isogeny h over L intertwining the specified embeddings of the chosen quadratic field (via Skolem-Noether in B), so each is of GL2-type over L; no cocycle-compatible system, degree bound or descent to Q is claimed.
- author / date: /root/astra_v14_source_review; date not stated
- status: author proposal; "claims no independent acceptance"
- published theorems relied on: Voight, Quaternion Algebras (2021) Corollary 7.1.5 with first-edition erratum; Hodge-centralizer / PEL identification (prior packets)
- in_v17: YES. Lines 13150-13166 (j(x)=f^{-1}i_sigma(x)f, Voight Cor 7.1.5, g=f b^{-1}, h=ng, everything over the same L); bibliography note on the erratum at 44747.
- note: The manuscript calls the quadratic field F where the note calls it E. The pairwise compatibility is all that is proved.

### research/version14/evidence/release-completion-017/v14-cj-global-atkin-identification-001/PROOF.md
- path: research/version14/evidence/release-completion-017/v14-cj-global-atkin-identification-001/PROOF.md
- claim: Same as cj-global-atkin-identification-current: the quotient (E,C_N) -> (E/C_n, phi(E[n])+phi(C_m)) is the Atkin-Lehner W_n, exchanges the O-eigensummands in the split case, and reduces compatibly at q.
- author / date: /root/v14_h6_coverage (suggested by /root/v14_sign_conductor); date not stated
- status: "author proposal, not an independent approval"
- published theorems relied on: Atkin-Lehner 1970; dual-isogeny identities
- in_v17: PARTIAL. As for the -current copy: local normalizer used at 21028-21040 and 20893-20905; global identification not found.
- note: Earlier version. Its Section 4 simply retains "quotient and mapping-property inputs"; the -current copy replaces that with a fresh finite-etale argument valid for n prime to q, noting the old prime-to-qN profile does not apply.

### research/version14/evidence/release-completion-017/v14-global-atkin-root-sign-001/PROOF.md
- path: research/version14/evidence/release-completion-017/v14-global-atkin-root-sign-001/PROOF.md
- claim: f|W_N = lambda f with lambda = product of w_{p^e}; the Mellin transform gives completed functional-equation sign -lambda; assuming the separately established equality L(E,s)=L(f,s), w(E) = -product w_{p^e}.
- author / date: not stated
- status: not stated
- published theorems relied on: Atkin-Lehner 1970 Lemma 9, Theorem 3(iii)
- in_v17: PARTIAL. Line 20335 states the formula without proof (see global-atkin-root-sign-001).
- note: Earlier, shorter version. It relies on equality of the two L-functions; the later global-atkin-root-sign-001 removes that dependence by comparing bad Euler factors and central orders.

### research/version14/evidence/release-completion-017/v14-qroot2-class-unit-proof-001/overlay/research/version14/evidence/qroot2-class-units-current/PROOF.md
- path: research/version14/evidence/release-completion-017/v14-qroot2-class-unit-proof-001/overlay/research/version14/evidence/qroot2-class-units-current/PROOF.md
- claim: Same as qroot2-class-units-current: O_K=Z[sqrt2], norm-Euclidean, units +/-(1+sqrt2)^k, four unit squareclasses, totally positive units are squares.
- author / date: not stated
- status: "new local proof"
- published theorems relied on: none
- in_v17: PARTIAL. Lines 5452-5454 state the conclusions only.
- note: Identical to the non-overlay copy except one sentence in the last section ("epsilon generates the positive units" here; the other copy says positive at the first embedding, with epsilon^2 generating the totally positive units, which is the correct wording).


## Batch 2


Method: each file was read in full; the manuscript was searched with grep for distinctive terms and the hit passages were read. Line numbers refer to quartic_v17.tex (45,035 lines). "NOT FOUND" means the listed searches failed, not that the material is provably absent. Lines roughly 2000-4700 of the TeX are embedded review/record material (older-version audit text), not the operative proof; hits there are flagged as such.

### research/version14/evidence/research-additions-005/o2_proposal/PROOF.md
- path: research/version14/evidence/research-additions-005/o2_proposal/PROOF.md
- claim: For p=5 and an absolutely irreducible potentially semistable 2-dimensional r of G_Q5 with distinct weights u<v and absolutely irreducible Weil-Deligne representation, the locally algebraic vectors of the Colmez Banach representation satisfy B_C(r)^lalg = pi_p(r) tensor Sym^(v-u-1) det^(1-v) (Tate-normalised classical local Langlands). Proved by transfer from an auxiliary classical eigenpoint (residual representation induced from Q(sqrt(-2)), tame ramification at 2 and 193), conditional on listed source theorems and earlier packets.
- author / date: `/root/astra_v14_baseline_compiler`, 2026-11-08
- status: "immutable author proposal for independent review"; does not approve itself; new connections in Sections 3-6 need independent review
- published theorems relied on: Emerton 2006 (Invent.) Thms 2.3.1, 2.5.1, 7.4.2; Hu-Tan 2015 p.1384 type criterion; CEGGPS Thm 7.4; Colmez VI.6.42, VI.6.9 and shape/nonvanishing theorems; (transitively Saito 1997, Henniart). Also the unpublished-in-manuscript packets ceggps-route-001 and ceggps-consolidated-003.
- in_v17: NOT FOUND. Searches: "CEGGPS|Caraiani|arithmetic action", "Emerton", "Colmez", "Paskunas", "locally algebraic", "sqrt{-2}", "Banach" (only an unrelated bibliography title). "Hu--Tan" occurs once (line 5799), only to say Pan's local Hu-Tan ring calculations are distinct from the global Hu-Tan support argument.
- note: This is part of an alternative (Hu-Tan / CEGGPS) route to p=5 modularity. V17 instead cites the published Calegari ICM 2022 statement of Pan's theorem (lines 5791-5804) with no residual restriction, so this argument is not needed by the manuscript as written. The file itself says it does not establish the full Hu-Tan theorem or manuscript adoption. If anyone later claims modularity is independent of Pan, this packet (and its unreviewed status) is where that would rest.

### research/version14/evidence/research-additions-005/retained_local_proof/PROOF.md
- path: research/version14/evidence/research-additions-005/retained_local_proof/PROOF.md
- claim: For the auxiliary absolutely irreducible residual representation of G_Q5, Ptilde = Ptilde^psi completed-tensor 1_univ carries the R_p action, is the projective envelope of pi^vee without fixed central character, and satisfies the four CEGGPS arithmetic-action axioms (d=0); each characteristic-zero dual fibre is the actual Colmez Banach representation B_C(r_x) (topologically and equivariantly). Avoids Emerton 2011's supercuspidal locally-algebraic identity, Image Thm 12.7, Dospinescu, and the Schneider-Stuhler resolution (replaced by a direct Ext^1 computation for principal series).
- author / date: `/root/astra_v14_source_review`; date not stated
- status: "Author proposal ... submitted for independent assembly review"; component reviews do not approve the composition
- published theorems relied on: CEGGPS 6.10-6.19, 4.30/4.32, 7.4; Paskunas "Image" (5.53, 5.56, 6.2, 6.3, 6.8, 4.36) and BM paper (5.2, 6.1, 6.4, 2.29-2.33, 4.18-4.21); Kisin Asterisque 330 (2.7-2.11); Colmez (IV.3-4, VI.5-6, VII.5.2); Breuil-Paskunas Section 9; Berger-Breuil (4.3.1, 5.2.7, 5.3.x); CEG+16 Thm 4.1; Kisin 2008 3.3.8; de Jong 7.3.6
- in_v17: NOT FOUND. Searches: "CEGGPS|arithmetic action", "Pa.k.nas", "Colmez", "Cohen--Macaulay|Breuil--M" (only unrelated surface-geometry hits), "Banach".
- note: Same alternative route as the o2_proposal above; not used by V17, which rests on Calegari/Pan. Final editions of several sources were not compared (stated in the file). Contains self-contained lemmas of independent interest (idempotent lifting for integral projective covers; Ext^1 of an irreducible principal series with distinct characters is one-dimensional; finiteness of exceptional crystalline points in the unframed space) that exist nowhere in the manuscript.

### research/version14/evidence/rooted-forest-network-input-001/PROOF.md
- path: research/version14/evidence/rooted-forest-network-input-001/PROOF.md
- claim: Over F_2 (or as a polynomial identity in edge weights), for an auxiliary network with grounded Laplacian Q and attachment columns c_a, the degree-zero and degree-one part of the network difference operator is det(Q)*1 + sum_{a<b} c_a^t adj(Q) c_b partial_ab, valid also for singular Q; operators of disjoint networks multiply. Conditional on the incoming symbol rules (edge contraction, cycle vanishing, primary isolation).
- author / date: not stated
- status: not stated (evidence note; explicitly says it does not establish the symbol rules or later constructions)
- published theorems relied on: none (Cauchy-Binet and an elementary incidence-minor lemma, both proved or standard)
- in_v17: PARTIAL. Lines 22337-22357: the displayed formula and the sentence "The displayed coefficients are the rooted-forest minors, by Cauchy--Binet on the incidence matrix. They are polynomial identities, so apply to singular Q as well", plus the multiplicativity remark. Missing: the incidence-minor lemma (determinant is 0 or +-1 according to the one-root-per-component forest condition), the all-minors forest expansion with R=T\{a}, C=T\{b}, and the block-determinant identity det[[Q,-c_b],[-c_a^t,0]] = -c_a^t adj(Q) c_b.
- note: The manuscript asserts in two sentences what the note proves in full. The note is not cited from the manuscript (no bibliography entry found for it). The contraction/isolation rules remain separate inputs in both.

### research/version14/evidence/theta-transport-current/PROOF.md
- path: research/version14/evidence/theta-transport-current/PROOF.md
- claim: For a weight-3/2 algebraic-coefficient cusp form g of level L (4|L) and character psi in Ramsey's convention, coefficientwise Galois conjugation gives a cusp form with character tau(psi), and the twist by a primitive character nu of conductor m is a cusp form of level Lm^2 with character psi nu^2 whose good T(p^2)-eigenvalues are multiplied by nu(p)^2; hence, given the separately proved full-eigenspace proportionality, tau(a(D)) = nu(D/D0) a(D).
- author / date: `/root/v14_gi_selection_review`; date not stated
- status: "proposed connecting proof, pending independent acceptance"
- published theorems relied on: Ramsey Definition 3.1, Theorem 6.2, p.600 theta multiplier; primitive Gauss sum identity
- in_v17: YES. Section "Coefficient conjugation and finite theta twists", label v15:theta-transport, lines 28910-28925 (essentially the whole note, including the gamma_t matrix identity and the Kronecker-symbol conductor argument); referenced from line 19839.
- note: Final proportionality step is not proved here; it is "already proved in the theta section" per the manuscript. The note's alternative remark (only the primitive twist is needed at D, D0 prime to S_0) is not in the manuscript text but is not needed.

### research/version14/proofs/a001-moduli-current-v1/PROOF.md
- path: research/version14/proofs/a001-moduli-current-v1/PROOF.md
- claim: For B=(2,-3), O=Z[i,(1+j)/2], mu=2j+ij, the form Trd(mu^{-1} x ybar) is an integral unimodular positive principal polarization with the prescribed Rosati involution, so Baba-Granath Theorem 2.1 applies and the coarse polarized forgetful quotient is V/W = P^1_Q with branch indices 4, 6, 2 at rational points, normalised by j = 0, infinity, -16/27 at CM discriminants -4, -3, -24.
- author / date: not stated (author-frozen connecting proof); references records dated November 2026
- status: "proposed current application, not an independent decision"
- published theorems relied on: Baba-Granath (CJM 2008) Theorem 2.1, Lemma 3.1, Section 3; Lin-Yang (Math. Z. 2020) Section 2 Lemma 3, Example 30; Buzzard 1997 p.592; (Rotger as antecedent)
- in_v17: YES. Lines 5812-5847 (matrix of the form, determinant one, factor-six correction of the Baba-Granath printed form, uniqueness via Buzzard p.592, W generated by w2,w3, cyclic-stabiliser argument giving 4,6,2, the three-value coordinate); cites a001-moduli-project at 5847 and bibliography 44373-44378.
- note: Corrects a source error: Baba-Granath's printed form Trd(xbar mu y) is 6 times a principal form (determinant 6^4), not principal. Items only in the note: the positivity sign check (lower-left entry of mu), distinctness of the three marked points, the identification of the third point with discriminant -24 via Z[sqrt(-6)], and a correction of an index slip (z3 should read z2) in Baba-Granath Lemma 3.1 p.740. The note also records an unresolved concern about Baba-Granath Propositions 3.7-3.9; V17 line 5881-5883 says those are not used.

### research/version14/proofs/cj-cm-inputs-v1/PROOF.md
- path: research/version14/proofs/cj-cm-inputs-v1/PROOF.md
- claim: For an imaginary quadratic field F with maximal order O, fixed CM type, and N prime to q*disc(F) with all primes split, labelled triples (A, A[n], iota) form a Pic(O)-torsor under ideal isogenies of degree Norm(a); j(A) is integral; (A,A[n],iota)^{Art(a)} = [a]*(A,A[n],iota) in a fixed convention; and for q inert the reductions are supersingular (forward direction only, q=3 included).
- author / date: not stated
- status: "authored source-to-application supplement" (no acceptance stated)
- published theorems relied on: Silverman Advanced Topics/AEC (VI.4.1, VI.5.x, C.11.1-C.11.4, III.1.4); Fowler Section 2.1 (class polynomial integrality); Cai-Shu-Tian pp.2524-2531; Gross-Zagier "On singular moduli" pp.198-199 (citing Deuring); Milne CFT notes for the Frobenius convention
- in_v17: YES. Section "Labelled CM points and their common-place reduction", label v15:cm-reduction, lines 35236-35248 (ideal action, CRT choice of representative, integrality, C.11.4 iteration avoiding bad primes, lifting j-equality to O-linear isomorphism, Cai-Shu-Tian inversion, Gross-Zagier forward criterion).
- note: Manuscript version is condensed: the local-principal argument for kernel = A[a] and degree = Norm(a), the cyclicity of the level subgroup, and the explicit remark that C.11.4 needs a good-reduction hypothesis are stated rather than derived. The note is explicit that no converse (lifting/surjectivity) is used and that the arithmetic/inverse Artin convention is only fixed up to one global inversion, harmless because the genus character is quadratic.

### research/version14/proofs/cj-good-reduction-v1/PROOF.md
- path: research/version14/proofs/cj-good-reduction-v1/PROOF.md
- claim: Given integral j-invariants, a finite diagram of labelled CM elliptic curves and ideal isogenies of degree d prime to qN acquires common good models over one finite extension; actions and isogenies extend, reduction is injective on O, the special isogeny has degree d with kernel exactly the specialised a-kernel and is the ideal quotient, and it preserves the N-level subgroup, the q-divisible group (isomorphism) and the residue orientation O/q -> k.
- author / date: `/root/astra_v14_assertions_arithmetic`; date not stated
- status: "new author successor awaiting independent review"
- published theorems relied on: Silverman VII.5.5, III.6.1-6.2 (with errata); BLR 1.2/1, 1.2/8, 1.4/2; EGA IV4 17.11.2(c'), 18.2.3, 18.2.7, 18.5.14-15; EGA III1 4.4.11
- in_v17: YES. Subsection "A simultaneous good model", lines 35250-35263 (same sequence of steps and the same citations, including the explicit torsor-quotient map and the u d + v N = 1 inverse).
- note: Manuscript omits the Legendre-form explanation of why Silverman VII.5.5 works at odd residue characteristic including q=3, the homomorphism check via uniqueness on A x A, and the connectedness argument for constant rank; these are routine. Does not prove supersingularity, reciprocity or class-set bijection (stated in both).

### research/version14/proofs/cubic-unirationality-v1/PROOF.md
- path: research/version14/proofs/cubic-unirationality-v1/PROOF.md
- claim: The manuscript's quotient cubic (after removing all vertex directions W) is geometrically integral, not a cone, of dimension >= 2 over Q with a rational point, so Colliot-Thelene-Salberger Proposition 1.3 gives Q-unirationality, and the input function then cannot take only integer values. This replaces the earlier Kollar citation.
- author / date: not stated ("Author proposal")
- status: "independent review is pending"
- published theorems relied on: Colliot-Thelene-Salberger, PLMS 58 (1989), Prop. 1.3 (and 1.2); Colliot-Thelene-Sansuc-Swinnerton-Dyer, Crelle 373 (1987), Remark 2.3.1; transitively Coray-Tsfasman
- in_v17: YES. Lines 17951-17962 (theorem statement and source split), about 18040-18078 (vertex space W, descent of X0, X1, section argument, application of Prop. 1.3 and contradiction); bibliography 44264-44274 cites this note for "exact hypotheses and quotient application".
- note: Supersedes the Kollar perfect-field citation (no "Koll" hit remains in V17). Narrow scope: characteristic zero only, dimension >= 2 only, cones over plane cubics excluded; dimension-one case handled separately in the manuscript. The note's justification that "no vertex direction over the algebraic closure" equals the noncone hypothesis (cone implies D_v H = 0 identically, by degree) should be checked against the manuscript wording near 18040-18060, which I did not read line by line.

### research/version14/proofs/direct-p5-modularity-v1/PROOF.md
- path: research/version14/proofs/direct-p5-modularity-v1/PROOF.md
- claim: In Lemma qm-modularity-descent (QM abelian surface with rational scalar cocycle, descent cochain t), the descended 2-dimensional r5 is absolutely irreducible, finitely ramified, de Rham with weights {0,-1} and odd, hence by the published Pan/Calegari theorem is a finite-character twist of a weight-two newform; the twist is finite and can be absorbed, so r5 is the Tate realisation of a primitive weight-two newform.
- author / date: not stated
- status: not stated in the file (the manuscript's embedded record at line 2634 calls acceptance "pending a nonauthor reviewer")
- published theorems relied on: Calegari ICM 2022 pp.611-612, 624 (Pan's theorem); Faltings; Scholze 2013 Cor. 1.8, Thms 9.1/9.3 + corrigendum; Fontaine Asterisque 223 Thm 3.8; Milne 1986 Thm 15.1, Milne 2005 6.8/6.9; Washington Thm 14.1; Shimura 1973 Section 4; Li 1975 p.294, Thm 5
- in_v17: YES. Lemma label lem:qm-modularity-descent at line 5589; proof lines about 5613-5790 (irreducibility 5625-5638, de Rham and weights 5640-5655, oddness 5657 ff., weight two and finite twist 5737-5753, twist absorption 5755-5789); scope paragraph 5791-5804 cites direct-p5-modularity-project; second citation at 15512.
- note: V17 corrects the note in one place: Li's Theorem 5 gives uniqueness, not existence, of a primitive constituent, so V17 (lines 5769-5785) supplies existence by a Deligne-Serre extraction instead and keeps the Li wording only as "historical". V17 also adds an explicit exclusion of weight k=1 (Deligne-Serre finite image) and uses Kato's filtration for HT weights, neither of which is in the note. The whole lemma depends on Pan's theorem as reported by Calegari; no comparison of Pan's final JAMS text is claimed.

### research/version14/proofs/general-field-tw-v1/PROOF.md
- path: research/version14/proofs/general-field-tw-v1/PROOF.md
- claim: For any totally real F (possibly ramified at 2) and r: G_F -> GL_2(k), char k = 2, with nonsolvable image, for every n there is a finite set Q of auxiliary primes satisfying all three conclusions of Kisin Proposition 3.2.2 (N(v) = 1 mod 2^n with distinct Frobenius eigenvalues; |Q| = h^1(G_{F,S},A) - 2 with 2|Q|+1 relative generators; Theta_Q/2^n free of rank 2-|S|+|Q|). Shows the even-p branch of Khare-Wintenberger II Lemma 5.2 never uses "F unramified at 2".
- author / date: not stated
- status: "At author freeze it has no independent acceptance"
- published theorems relied on: Khare-Wintenberger II Lemma 4.3, Section 4.1.6, Lemma 5.7, Prop. 5.6, Lemmas 5.8-5.9; Dickinson Lemma 42; DDT Theorem 2.19 (Selmer-size/Wiles formula); Kisin 3.2.1 representability; Chebotarev, class field theory, local Tate duality
- in_v17: NOT FOUND. Searches (case-insensitive): "kisin", "khare|KW|Wintenberger", "Proposition 3.2.2|Lemma 5.2|unramified at 2", "Taylor--Wiles|auxiliary prime" (only unrelated hits), "totally real".
- note: This repairs a real source-level gap (a cited lemma stated with a field hypothesis the application does not satisfy) inside the proof ancestry of 2-adic modularity lifting. V17 does not mention Kisin or Khare-Wintenberger at all, so either the dependency is hidden behind a cited published theorem or it belongs to a route no longer used; a human should decide which. Unreviewed.

### research/version14/proofs/h5-full-three-v1/PROOF.md
- path: research/version14/proofs/h5-full-three-v1/PROOF.md
- claim: For the discriminant-210 maximal order, the functor of triples (A, i, eta) with eta an O-linear isomorphism (O/3O) -> A[3] is a degree-72 finite etale cover of Yuan's maximal stack over Z[1/210], has trivial inertia, and is a smooth proper projective scheme Y with universal abelian scheme; Y_Q is the entire canonical Shimura curve of principal level U(3) with its normaliser action (coarse degree 36, group order 576).
- author / date: `/root/astra_v14_baseline_compiler`; errata read 2026-11-08
- status: "Author proposal ... Independent acceptance remains pending"
- published theorems relied on: Yuan (2024) Section 2.1 maximal stack; Milne 1986 Thm 8.2, Rem 8.4, Lemma 12.2; Milne 2005 (Clay) Example 8.6, Prop 8.7, Thm 7.4, 13.6, 14.8, pp.354-355; Buzzard 1997 p.592; Stacks Project tags 03YR/94.13.2, 0ADD, 0A18, 0E83, 0D3A, 0D32, 0B45; Gonzalez-Rotger (genus 5)
- in_v17: YES. Section label sec:h5-full-three-construction, lines 12852 to about 13045 (lattice principality at ramified 3, 72 units, torsion-freeness of 1+3M_4(Z_3), Riemann-Hurwitz and ampleness route to projectivity, type-C PEL datum with both half-planes, integral-lattice/quadruple equivalence, canonical Q-model, degrees 72 and 36); used at 13329; bibliography 44395-44400. A tabulated restatement also appears in the embedded record material at 2336 and 2425-2454.
- note: Handles the exceptional case that 3 is ramified in B, so standard prime-to-discriminant level-structure theorems do not apply. Deliberately avoids Milne's erroneous original 8.14/8.17 by checking the Hodge condition directly. Explicitly retains all similitude multipliers mod 3 (all geometric components). No smooth model at primes dividing 210 is claimed.

### research/version14/proofs/igusa-theta-v1/PROOF.md
- path: research/version14/proofs/igusa-theta-v1/PROOF.md
- claim: With Igusa's half-characteristic theta constants z_m at the genus-two period point, 4 psi_4 = sum over even m of z_m^8 and -2^14 chi_10 = product over even m of z_m^2; with psi_4 = 144 j and chi_10 = -j^3/4 this gives j = 3779136 (prod z_m)^4 / (sum z_m^8)^5 and h(j) <= 40 h([z_m]) + log 3779136 <= 40 h + 22, in Pazuki's r=2 theta coordinates.
- author / date: not stated
- status: "pending independent review"
- published theorems relied on: Igusa, Amer. J. Math. 89 (1967) pp.833-834, 848; Lin-Yang p.793 eq.(13); Pazuki, Theta height and Faltings height, p.25 and Section 2.3.4 pp.30-31
- in_v17: YES. Lines 6738-6767 (definitions, both identities, weight-20 cancellation, the constant 3779136, norms 3779136 and 10^5, bound +22, odd coordinates zero); cites igusa-theta-project at 6746 and bibliography 44480-44482.
- note: Replaces a citation to an unpublished LNY proof (no "LNY" hit remains in V17). Details only in the note: the reindexing between Igusa's and LNY's characteristic conventions, the caveat that Pazuki's coordinates are theta_(m1,m2)(tau,0) and not the alternative theta_(m,0)(4 tau,0) system, and that Igusa's Lemma 10 (genus >= 3) is not applied. Nonvanishing of the denominator comes from psi_4 = 144 j with j finite nonzero, not from nonvanishing of theta constants.

### research/version14/proofs/ly-d6-normalization-v1/PROOF.md
- path: research/version14/proofs/ly-d6-normalization-v1/PROOF.md
- claim: On the discriminant-six quaternionic locus with Hauptmodul j normalised by j = 0, infinity, -16/27 at CM discriminants -4, -3, -24, the constants in Lin-Yang's identities s3^2/s2^3 = c1 j, s5/(s2 s3) = c2, s6/s2^3 = c3 j + c4 are all 1, hence [J2,J4,J6,J10] = [12(j+1), 6(j^2+j+1), 4(j^3-2j^2+1), j^3] and j = (12^5 J10)^2/(J2^2-24 J4)^5.
- author / date: "Gaussian", 8 November 2026
- status: "new connecting proof awaiting independent review"
- published theorems relied on: Lin-Yang, Math. Z. 295 (2020), eqs (13)-(14) p.793, Examples 29-30 pp.795-797 (divisors, Y1 and Y'_5 parameterisations, eta-coordinate values at discriminant -24); Baba-Granath Thm 2.1, Lemma 3.1 only for the Q-structure
- in_v17: YES. Lines 5849-5884 (same two evaluation points, the values s2=-36x, s3=6912, s5=-248832x, s6=-32845824, ratios -16/27, 1, 11/27, rescaling by -12), equation label eq:qm-normalized-igusa at 5874; cited at 5880, 6302, 6732; bibliography 44380-44382.
- note: Deliberately avoids Lin-Yang's j(P_-19) = 81/64 evaluation and Baba-Granath Propositions 3.7-3.8 / Theorem 3.10 (the note says the displayed Baba-Granath map is a degree-four isogeny, so that product-isomorphism proof is doubtful). The manuscript typo-level difference: V17 writes c4 = 2^12 3^6 / 1728^2, the note 2^12 3^6 1728^4/1728^6; both equal 1. The explicit Q-rationality formula for j in terms of Igusa invariants (note Section 4) appears in V17 only via the theta-height passage (line 6754).

### research/version14/proofs/pan-local-rings-v1/PROOF.md
- path: research/version14/proofs/pan-local-rings-v1/PROOF.md
- claim: At p=5, for the local framed fixed-determinant lifting rings in Pan 4.2.10 at v with q = 1 mod p: (i) unrestricted and fixed-determinant rings differ by one formal variable (unique square root of det(Phi)/d), transferring connectedness, dimension, generic regularity and Taylor's component statement; (ii) for nontrivial xi the fixed-determinant ring is O-flat, by an explicit basis for the determinantal ring of 2x2 minors; (iii) for trivial xi only the nilreduced component statement holds, and generic reducedness of the unreduced special fibre must not be asserted.
- author / date: not stated
- status: "authored supplement, not an independent verdict" (the V17 bibliography entry describes a "bounded independent review")
- published theorems relied on: Pan (Fontaine-Mazur in the residually reducible case) 4.1.1, 4.2.4, 4.2.10; Thorne 3.15(2)/3.16; Taylor Lemma 3.2(1), 2.7; Allen-Newton-Thorne correction
- in_v17: NOT FOUND in the body. Searches: "Thorne|Allen--Newton|generic(ally) reduced", "Sigma^q|lifting ring|4.2.10", "pan-local-rings" (only the bibliography item at 44788-44793, with no \cite to it found).
- note: This supplies a flatness statement that the note says is absent from the cited Thorne result and corrects an over-strong generic-reducedness claim in Pan's local analysis (with the counterexample O[e]/(e^2)). V17 uses Pan only through Calegari's published statement and says (5797-5800) that not every input to Pan's proof is reproved; so this is proof-ancestry repair kept outside the manuscript. The bibliography entry exists but appears uncited, which a human may want to fix or justify.


## Batch 3


Line numbers are lines of `quartic_v17.tex` (45,035 lines). Manuscript layout used for orientation: lines 83-5135 "proposed 214-variable construction" (review-style bridges); 5136-28930 "complete current Version 16 mathematical foundation"; 28931-35286 polynomial inverse theorem; 35287-end "222-variable family and its predecessors". "YES (condensed)" means the argument is present but shorter than the note. in_v17 judgments come from targeted Grep plus reading the matched regions, not from a full read of the manuscript.

### research/version14/proofs/prime-cyclic-base-change-v1/historical/PROOF.md
- path: research/version14/proofs/prime-cyclic-base-change-v1/historical/PROOF.md
- claim: For F totally real, r: G_F -> GL_2(E) l-adic (l = 2 allowed) with nonsolvable residual image, and M/F finite solvable Galois totally real: if r|G_M is attached to a parallel-weight-two cuspidal Hilbert automorphic representation then so is r (and conversely restriction to intermediate fields). This is "the automorphic part of H-D4" (solvable descent/ascent with exact twist bookkeeping).
- author / date: /root/astra_v14_baseline_theta; date not stated
- status: "new connecting proof submitted for independent review"; conditional on named inputs; file sits in a `historical/` directory
- published theorems relied on: Langlands, Base Change for GL(2) (Ch. 2(A,B,F), Lemma 3.1, Lemma 11.3(b), Prop. 11.4, Lemma 11.6(b)); Taylor/Carayol Galois representations for Hilbert forms; global class field theory; Chebotarev + Brauer-Nesbitt
- in_v17: SUPERSEDED. No hits for "Base Change for", "Lemma 11.6", "solvable", "Kisin", "totally real", "strong multiplicity one". The modularity lemma `lem:qm-modularity-descent` (line 5588) is now proved directly from the prime-five statement in Calegari ICM 2022 (lines 5614-5680; also M_2-M_7 at 2530-2634); bibliography item at 44243 calls the old material a "historical route map".
- note: The whole Khare-Wintenberger/Kisin "H" route this served is absent from V17. The note itself flags that it used an IAS retypeset of Langlands, not the 1980 edition, and that the ramified local interface (Section 6) was conditional on H-D5.

### research/version14/proofs/qm-centralizer-v1/PROOF.md
- path: research/version14/proofs/qm-centralizer-v1/PROOF.md
- claim: If A = M_s(Delta) with Delta a central division algebra over a characteristic-zero field E, and C/E is a field of degree m embedded in A with centralizer C, then dim Delta = d^2 and m = sd; if moreover a left A-module is one-dimensional over C then d = 1 and A = M_s(E).
- author / date: not stated
- status: not stated (supplies one step of the V14 "scalar-descent lemma"; explicitly does not construct idempotent images or the cohomology comparison)
- published theorems relied on: none (self-contained algebra)
- in_v17: NOT FOUND (probably superseded together with the route it served). Searched "centralizer" (17 hits, none this calculation), "M_s(E)", "End^0", "primitive factor", "Weil restriction".
- note: Its application (End_Q^0(Y), Lie(Y/Q), cutting out Y0 from a Weil restriction) does not occur in V17; the lemma at 5588 no longer passes through a primitive factor Y0.

### research/version14/proofs/qm-cohomology-v1/PROOF.md
- path: research/version14/proofs/qm-cohomology-v1/PROOF.md
- claim: H^1 of a Q-isogeny factor Y0 of the Jacobian of the compact modular curve embeds G_Q-equivariantly (ell = 5) into the parabolic cohomology of the open curve at finite level and then into the classical tower, with injective transition maps; no Hecke-stability of the factor is assumed.
- author / date: not stated
- status: not stated; modular tower and classical constituent decomposition are "retained inputs"
- published theorems relied on: Stacks Project 03RQ, 095L, 09ZB, 0BD2, 0BCY; Milne, Jacobian Varieties Thm 6.6; Milne, Abelian Varieties Thm 15.1(a), Rem. 15.5, Sect. 16
- in_v17: NOT FOUND (probably superseded). Searched "parabolic", "H^1_c", "j_!", "autodual", Stacks tags 03RQ/095L/09ZB, "classical tower". Only 0BD2/0BCY appear (35231) in an unrelated Picard-norm construction.
- note: V17 obtains the newform directly (Calegari) and then gets the abelian variety by Faltings isogeny (3090-3104, 2604-2628), so no embedding into a classical cohomology tower is needed.

### research/version14/proofs/qm-idempotent-image-v1/PROOF.md
- path: research/version14/proofs/qm-idempotent-image-v1/PROOF.md
- claim: Over a characteristic-zero field, the image of a rational idempotent of an abelian variety is an abelian subvariety over the ground field; orthogonal idempotents give an isogeny decomposition, matrix units give isogenous factors with End^0 equal to the corner algebra, and differentiation of rational endomorphisms is faithful on Lie.
- author / date: not stated
- status: not stated
- published theorems relied on: Cartier's theorem (Stacks 047N, Lemma 39.8.2)
- in_v17: PARTIAL. The statements are used without this argument: 13745-13752 ("image of an integral multiple of such an idempotent is an elliptic subvariety over L", factors' endomorphisms via inclusions/projections), 13755-13758 (faithful differentiation, elliptic case only), 6389 (multiples of matrix units), 3253-3259 (factor idempotents; Poincare reducibility cited to Milne Prop. 12.1). Missing: the closed-image/schematic-dominance/Cartier proof, the denominator-clearing isogeny p q = [m], and the general faithfulness proof. The three listed uses (Weil restriction W, M_2(C) on X, End^0(Y) = M_s(E)) were not found.
- note: A reader of V17 sees the idempotent-image fact asserted in the CM branch; this note is the only place the full proof was written.

### research/version14/proofs/real-cyclotomic-residual-v1/PROOF.md
- path: research/version14/proofs/real-cyclotomic-residual-v1/PROOF.md
- claim: For K_n = Q(zeta_{2^{n+2}})^+ and S_n = dyadic prime plus a fixed odd set: the two-class group of K_n is trivial, unit signatures are surjective (via u = 1 + zeta + zeta^{-1} of norm -1), and the positive cone C^+ of G_{K_n,S_n}-cohomology with F_2 coefficients has dim H^1 = r_n + s_n - 1, dim H^2 = s_n - 1 and no other cohomology.
- author / date: not stated
- status: not stated; "supplies only the finite-level argument at main14018-14067"
- published theorems relied on: Cox, Primes of the form x^2+ny^2 (Thm 5.9, Props 5.10-5.11, Thms 5.18/5.23); Milne ADT I Cor. 4.15, Thm 4.10(c), Thm 5.1; ADT II Props 2.1, 2.9
- in_v17: YES (condensed). Paragraph "The residual positive complex", lines 19166-19219 (summary also at 7914-7923), leading to (E.3) at 19241.
- note: The manuscript omits the elementary ramification facts (Eisenstein irreducibility, unramifiedness at odd primes, cyclicity of the Galois group), the parity count for the negative conjugates, and the Cox/ADT page citations; it says "Frattini quotient" where the note proves the cyclic-abelianization lemma. The note stresses ordinary (not narrow) Hilbert class field and that C^+ is not ADT's compact-support complex; the manuscript states "with the real places split" and "ordinary real cochains".

### research/version14/proofs/real-kummer-lattice-v1/PROOF.md
- path: research/version14/proofs/real-kummer-lattice-v1/PROOF.md
- claim: For the twist E = E_l^h (full rational 2-torsion) the period lattice splits integrally as Lambda^+ + Lambda^- (rectangular), so T_2(E) = T^+ + T^- with J = diag(1,-1); E(R)/2^n = Z/2 and its Kummer image in H^1(R, E[2^n]) is exactly the minus line, which is its own annihilator; the truncated complex U_R = [T^+ + T^- -> T^-] has the right H^0 and H^1 mod 2^n.
- author / date: not stated
- status: not stated; supplies input "used at main14247-14265"
- published theorems relied on: Silverman VI.5.1.1, VI.5.2 (complex uniformization); finite real Tate duality (accepted input)
- in_v17: PARTIAL. Lines 19402-19418 state the conclusions (J = 1 mod 2, projectors (1 +/- J)/2, U_R, H^0 = T^+/2^n + (T^-/2^n)[2], Kummer line T^-/2, self-annihilating) with a one-sentence sketch ("can also be checked using a rectangular period lattice"). Missing: equivariance of the period map, the explicit Kummer cocycle computation (0,-1), the two-circle description of E(R), and the isotropy/order-4 argument.
- note: The integrality of the splitting (not just rational) is the point; the manuscript gets it from J = 1 mod 2 in one line, which is correct but terse. The warning that E(R)^wedge_2[-1] would lose T^+/2^n is reproduced (19416-19418).

### research/version14/proofs/real-selmer-limit-cancellation-v1/PROOF.md
- path: research/version14/proofs/real-selmer-limit-cancellation-v1/PROOF.md
- claim: For the fixed curve and support, compact/discrete limits of finite Poitou-Tate restricted to Kummer conditions give the exact sequence 0 -> L_2/J_2 -> Sel^vee -> H^2_glob -> local H^2 + H^2(R,T) -> H^0(Q,D)^vee -> 0; at corank zero this yields the length identity (E.6) and, through the positive cone and Smith-normal-form determinant, the valuation formula (E.7) with all torsion/saturation terms cancelling.
- author / date: not stated
- status: not stated; several items are "separate caller inputs" (explicit reciprocity for z, forward-rank theorem)
- published theorems relied on: finite local Tate duality, finite Poitou-Tate with real Tate terms, Weil pairing, Mordell-Weil
- in_v17: YES (condensed). Lines 19364-19492: (E.6) at 19379, (E.7) at 19395, exact sequence at 19435-19441, cone sequence 19463-19467, positive-cone lengths 19469-19491. Manuscript cites Nekovar 5.7.1.4-5.7.1.7 for the orthogonal-Kummer Poitou-Tate step.
- note: The manuscript abbreviates the limit justifications (transition maps, Mittag-Leffler for images with non-surjective transitions, derived reduction of B_v[-1], closedness of J_2) to one or two sentences. The note explicitly does not assert (E.7) at z = 0 and does not claim cd_2(G_Q) = 2.

### research/version14/proofs/yuan-final-source-v1/PROOF.md
- path: research/version14/proofs/yuan-final-source-v1/PROOF.md
- claim: Source-use reconciliation: the maximal-stack height argument needs only Yuan (Acta Math. Sinica Chin. Ser. 67 (2024)) Section 2.1 and Theorem 1.1 and proves integrality of J^2 q_i directly on the stack, so it avoids Yuan's coarse Lemma 2.1 and Theorem 2.2; the published Chinese proof of Lemma 2.1 has a separability inference that does not follow from the stated hypotheses (test case Z_p[t] -> Z_p[x], t = x^p).
- author / date: root, drawing on /root/astra_quartic_opt05_anchor; date not stated
- status: "This proposal awaits independent acceptance"
- published theorems relied on: Yuan 2024, Section 2.1 (pp. 230-231) and Theorem 1.1 (p. 229)
- in_v17: PARTIAL. The usage is implemented: 12842 (Section 2.1 cite), 13195-13202 ("uses no integral coarse-model pullback from Yuan's Lemma 2.1 or ... Theorem 2.2"), 13220-13230 (Petersson norm, isometry), 2425 (source table), 4693 (internal source "Yuan-finalbridge"). Missing: the separability gap finding itself and its counterexample (no hits for "purely inseparable", "SEPARABILITY"), and the open check that Yuan's proof of Theorem 1.1 does not depend on Lemma 2.1.
- note: A reader of V17 sees that Lemma 2.1 is avoided but not why; the reason (a doubted step in a published proof) lives only in this note and the SOURCE-YUAN-LEMMA21-SEPARABILITY finding. The note says the Chinese and English proofs are not claimed to agree.

### research/version15/quartics/quartic-222/provenance/detector-q-nonzero-107/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/detector-q-nonzero-107/PROOF.md
- claim: In the raw 224/198 system, ten retained rows alone force R > 0, T = R^2 != 0 and the detector coordinate q (= x102) != 0 for every rational solution, via the 5-adic argument on (1+q) P5(r) = r^5 with P5 = (r-1)^2 (r-4)^3 mod 5; hence a guard q h = 1 is redundant.
- author / date: not stated in file (attributed to "H6" in joint-root-factor-110); date not stated
- status: not stated in file; packet 110 says it was independently reviewed at work/quartic224-detector-q-review-001
- published theorems relied on: none
- in_v17: YES. Section `v222:roots`, lines 42473-42480 (R > 0 from 42245-42247).
- note: Does not imply q > 0 or q + 1 != 0 (q = -1 is retained), as both note and manuscript say. The manuscript omits the explicit positivity-of-P(x55) step for R, relying on the four-contact positivity instead.

### research/version15/quartics/quartic-222/provenance/joint-root-factor-110/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/joint-root-factor-110/PROOF.md
- claim: The 224/198 system is equivalent (two-sided rational maps on the admitted-family solution set) to a 223-variable, 197-residual system obtained by deleting six FU coordinates, rescaling root/label coordinates by q/R, q, 1/R, pairing detector factors via H, J, K, and rewriting the trace as Q1 G - R^2 Z.
- author / date: arithmetic_author (with H6 normalization 109 and GI trace organization 005); date not stated
- status: "Author proposal ... not an independent acceptance"; "No manuscript adoption"
- published theorems relied on: none
- in_v17: YES. Section `v222:roots`, lines 42467-42531.
- note: Coefficient threshold N >= 53 is about coefficient height only; the defining threshold stays ineffective (stated in both).

### research/version15/quartics/quartic-222/provenance/normalizer-shared-root-109/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/normalizer-shared-root-109/PROOF.md
- claim: The M-free root/label normalization (separate i/k and root scalings by q, R) turns the affected root, circle, comparison and Lucas equations into quadrics, kills the six FU definitions, and gives q^2 * (old trace) = q^2 G - R^2 Z.
- author / date: not stated in file ("H6" per packet 110); date not stated
- status: "composable author contribution, not acceptance of a full 223-variable system"
- published theorems relied on: none
- in_v17: YES (condensed). Lines 42482-42504 (scaling table, "differing first-root i,k normalization is included") and 42522-42529 (trace).
- note: The manuscript says "literal substitution ... gives quadrics" and does not list the 18 consumers of the 12 repurposed coordinates or the individual rewritten equations (e.g. new AC = d q (new i - new k)); those are only in this note and its checker.

### research/version15/quartics/quartic-222/provenance/quartic223-positive-weights-integration-001/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/quartic223-positive-weights-integration-001/PROOF.md
- claim: Replacing the 197 unit-weight squares of the sparse 223 system by strictly positive rational weights (identity maps on coordinates) keeps the rational/real zero set, yields 2283 monomials, and keeps coefficient height A_N^2 + 1 for N >= 53.
- author / date: not stated
- status: "author proposal requiring independent review, not a new variable saving"
- published theorems relied on: none
- in_v17: YES. Lines 42675 ("positive weights preserve the common zero set") and 44222-44234 (for the final 196-row, 2277-monomial polynomial).
- note: The manuscript's numbers are for the 222 system (196 rows, 2277 monomials), one step past this note's 223 system.

### research/version15/quartics/quartic-222/provenance/scalar-contact-quartic-001/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/scalar-contact-quartic-001/PROOF.md
- claim: Replacing the five-factor scalar contact product by r4 = beta(beta-1)(beta-2401)(32 beta+343) (dropping 2 beta - 1), with R = A_N r4/(1+149^2 r4), gives a 232-variable, 206-residual system with the same defining property (soundness and integer completeness, ineffective N0); this is a new arithmetic construction, not a witness bijection.
- author / date: not stated
- status: "Author proposal, not independently accepted"
- published theorems relied on: none new (inherits five-contact height input, parity-237 lemma)
- in_v17: YES. Section `v222:contacts`, lines 42222-42291, equation (C232) at 42238.
- note: Changes a small-prime preparation value: v_3(R) is now 0 rather than 1; both note and manuscript check that the actual requirement (1 + 9792/R a square in Q_2, Q_3, Q_17) still holds. The manuscript compresses the v_2 case analysis to "a direct parity calculation".

### research/version15/quartics/quartic-222/provenance/shared-T-elimination224-004/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/shared-T-elimination224-004/PROOF.md
- claim: In the 226 system the reference coordinate g can be eliminated by the polynomial g = ((beta S + alpha) T - alpha S - gamma)/delta (delta a nonzero constant), replacing eight reference rows by six K-quadrics Q0..Q5 in f, S, B, w, W, T; the 224-variable, 200-residual system is equivalent in both directions, with polynomial certificates.
- author / date: not stated; direct-ratio idea credited to Jose Brox public commit 34454098...
- status: "Author-frozen full 224 candidate, pending independent review"
- published theorems relied on: none
- in_v17: YES. Section `v222:reference`, lines 42342-42465: formula (G) 42355, Q0..Q5 42362-42420, certificates for F and E 42422-42437, f = 0 check 42439-42441.
- note: The manuscript prints certificates for F and E only; the third certificate (for A^2 w - (8 - a f - 2 e g)^2) is replaced by the Q2-linear-in-w argument of the next entry, and the manuscript goes straight to 198 quadrics.

### research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/shared-T-redundancy224-006/PROOF.md
- claim: In the 224 system the two rational components of Q5 are redundant: Q0, Q1, Q3 recover F, E and f != 0; the forced-149 valuations make the coefficient M of w in Q2 nonzero, so Q2 forces w = g^4/f^2, Q4 gives W = w^2, and Q5 follows; result 224 variables, 198 residuals.
- author / date: not stated
- status: "author-frozen successor"; "No manuscript adoption or independent acceptance is claimed"
- published theorems relied on: none
- in_v17: YES. Lines 42439-42459 (M displayed 42446-42453; "Retain only Q0..Q4").
- note: Valid only for the admitted family A_N = 149^(2N+1) (uses the 149-adic valuations), not for symbolic A; both texts say so.

### research/version15/quartics/quartic-222/provenance/shared-alternate-226-001/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/shared-alternate-226-001/PROOF.md
- claim: The eight alternate-ratio components z_i of the 232 system can be replaced by one field coordinate T with D T = N and E_i T = K_i L_i'; N, D, T are nonzero (149-adic valuation argument), giving an equivalent 226-variable, 200-residual system including all zero-numerator branches.
- author / date: not stated; idea credited to Jose Brox, fixed_difference_charts_20261110_v18.tex
- status: "Author-frozen candidate, pending independent review"
- published theorems relied on: none
- in_v17: YES. Section `v222:ratio`, lines 42293-42340 (identity at 42333-42336; Brox credit 42294-42298).
- note: None beyond the inherited ineffective threshold.

### research/version15/quartics/quartic-222/provenance/trace-quotient222-116/PROOF.md
- path: research/version15/quartics/quartic-222/provenance/trace-quotient222-116/PROOF.md
- claim: In the 223 system the two trace helpers G, Z (with Q G = R2 Z) can be replaced by one coordinate T with Z = Q T, G = R2 T, giving 222 variables and 196 quadratic residuals with inverse polynomial maps; uses only q != 0.
- author / date: arithmetic_author; date not stated
- status: "Independent acceptance of this packet is pending"
- published theorems relied on: none
- in_v17: YES. Section `v222:quotient`, lines 42533-42549 (coordinate called U_*).
- note: This is the last step to the headline 222 count; the manuscript does not record that the note's acceptance was pending.

### research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/resume-depth-20261107/anchor313/PROOF.md
- path: (as in heading)
- claim: The common scale gamma of the shared-314 circuit can be taken as 1/u for the anchor coordinate u on u^2 + 6v^2 - 2z^2 = 3T^2 - 2C^2 (C = 3^(2^25)), using eight power coordinates; completeness holds because a rational anchor point with prescribed valuations of u at 2, 3, 17 and the contact primes and a prescribed real interval exists, proved by explicit local points and an elementary weak-approximation argument through a fixed rational point.
- author / date: /root/astra_quartic_opt03_depth, November 7, 2026 (anchor reuse proposal and local targets due to agent05)
- status: "contributed proof, not independent acceptance"; count/transport left to compiler review
- published theorems relied on: none new (inherited quaternion criterion; Version 13 scalar preparation)
- in_v17: YES. Subsection `subsec:v14-anchor`, lines 28599-28703.
- note: Belongs to the 314-variable predecessor inside the "Version 16 foundation" part, not to the 222 family. Requires the extra preparation condition F_s in 8 Z_2 (manuscript 28625).

### research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/resume-depth-20261107/shared314/PROOF.md
- path: (as in heading)
- claim: A common-scale detector with groups G0, G1, G2 (terms weighted by gamma^-160, gamma^-80, gamma^-40 and an eighth-power guard gamma^16 E^8) is sound: valuation classes mod 16 give a unique minimum, the guard forces v(gamma) > 15 alpha/32, the bounds give v(H_i) >= 40, v(M_i) >= 10 and primary depths 40/20/22, and H depth >= 10 is recovered by a bootstrap from the Lucas test (F(0,0,0) = -1) without the old high H0 test; completeness holds with v(gamma) = 1 at contact primes.
- author / date: /root/astra_quartic_opt03_depth, November 7, 2026 (Agent01 compiler audit separate)
- status: "new, unaccepted arithmetic proposal"; H-bootstrap flagged as needing independent review
- published theorems relied on: none new
- in_v17: YES. `subsec:v14-groups` 28196-28307, `subsec:v14-logarithms` 28439-28528 (bootstrap 28478-28491), `subsec:v14-completeness` 28530-28597.
- note: The note calls the H-depth bootstrap "the new application requiring independent review" and says an earlier review explicitly excluded it; the manuscript presents it without that flag. The original "156" proposal remains rejected per the note.

### research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/root-ordinate299/PROOF.md
- path: (as in heading)
- claim: In the reciprocal chart the alternate ordinate k can be removed (k = s(f-F) - h) with a reduced slope row b = 0 and regular ratio (1 - DB) z = k; exact identities recover the old divided-difference row, the alternate curve and (once 1 - DB != 0) the raw ratio; for the scalar root S the orientation row a bS = D h - s(D f + c) must be added.
- author / date: "the root agent" (extension of agent01's elimination); date not stated
- status: "a proof component, not acceptance of a complete 299-variable artifact"
- published theorems relied on: none
- in_v17: YES. `subsec:v14-reciprocal`, lines 28309-28437: reduced rows 28320-28324, restoration identities 28333-28337, orientation (eq:v14-S-orientation) 28390-28399, raw ratio (eq:v14-raw-ratio) 28411-28421.
- note: Nonvanishing of 1 - DB is an arithmetic dependency discharged only after the low tests; both texts insist on the order. The root-curve equation alone would allow the wrong sign of the S ordinate, hence the orientation row.

### research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/root-reciprocal307/PROOF.md
- path: (as in heading)
- claim: On y^2 = x^3 - Dx with reciprocal coordinates f = 1/x, h = -y/x^2, three quadratic slope equations in (f,h,F,k,s,c) force (c, y_R), y_R = D h - s(D f + c), to be the point U - V in every case (secant, tangent, U = O, V = O), with the integer polynomial identity y_R^2 - c^3 + Dc = D^2 r4 - D(Df+c)(r2 - s r1) + r3 (c+Df)(c+DF).
- author / date: "the root agent" (reciprocal construction by the horizontal-repair agent; exceptional cases by Agent10); date not stated
- status: "not a certificate for a complete new polynomial"; independent review assigned to agent01
- published theorems relied on: none
- in_v17: YES. Lines 28309-28381: case analysis 28354-28366, identity (eq:v14-root-identity) 28368-28376, c_i != 0 via the product-height chain 28378-28388.
- note: The sign convention h = -y/x^2 is load-bearing (reversing it flips the orientation). Recovering b = y_R/a needs c != 0, proved from the height-product chain.

### research/version15/snapshots/v15-018/review/sf34-root-typing-025/PROOF.md
- path: research/version15/snapshots/v15-018/review/sf34-root-typing-025/PROOF.md
- claim: For one root block, the five stored values V, Q', I, K', W (V = ar, Q' = ag, I = aJ, K' = ak, W = rg) are equivalent to the old chart via three exact polynomial identities modulo c = a^2, D = c^2 - b^2, with Y_U = r^4, Y_V = g^4 and no zero stratum discarded; also records that the H chart (chi f = 1, S_H^2 = chi - D f) can contain 2-torsion locally and that S_H != 0 comes from the forced-149 argument, not from "D nonsquare" (D is a square in K).
- author / date: not stated
- status: review note on "the chart replacement already printed in the frozen manuscript"; does not identify the 259- and 248-variable systems by a bijection
- published theorems relied on: none
- in_v17: YES. "Scaled biquadratic comparison charts", lines 27289-27340 (identities 27318-27322); component typing with the factor-2 conventions at `v15:component-typing` 38372-38424; H chart at 37671.
- note: The corrective remark (do not justify S_H != 0 by "D nonsquare") is a warning to authors; I found no such wrong claim in V17 (grep "S_H=0", "nonsquare in K"), but did not read every H-chart passage.

### research/version15/snapshots/v15-018/work/quartic238-optimization-20261110/scalar/parity-core-237-001/PROOF.md
- path: (as in heading)
- claim: Replacing the scalar pole by W = Z0^4/R^10 + Z1^2/R^5 + F^2/R^4, b = R(R+9792) W^2 (three terms in distinct valuation classes 2+4Z, odd, 4Z) gives a 237-variable, 211-residual system with v_p(Z0) > 19 nu/8, v_p(Z1) > 9 nu/4, v_p(F) > 7 nu/4 at contact primes, hence the same defining property with threshold exponent L'_N = floor(9(2N-1)/4) + 1.
- author / date: not stated
- status: "author proposal, independent review pending"
- published theorems relied on: none new (base cubic-log height theorem inherited)
- in_v17: YES. `v15x:parity`, lines 40170-40296 (Lemma `v15x:scalar-local` 40197-40231).
- note: A new scalar criterion, not a bijection of old and new scalar witnesses (stated in both).

### research/version15/snapshots/v15-018/work/quartic248-optimization-20261109/guards-scalar/global-rescaling-239/PROOF.md
- path: (as in heading)
- claim: Substituting x_i = R^{w_i} y_i with signed integer weights, deleting the R^4 coordinate and keeping the explicit row y_139 = R^2, maps the 239 system bijectively to a 238-variable, 212-residual system; R > 0 on every solution because the degree-5 contact polynomial in z = X^2 has all positive coefficients and (1 + 22201 r) R = A_N r.
- author / date: /root/v14_arithmetic_review; date not stated
- status: "not independently accepted"; "Independent full review is still required"
- published theorems relied on: none
- in_v17: YES. "Global scalar rescaling: 239 to 238", lines 38339-38357 (weights 38341-38346, positive polynomial 38351-38355); index dictionary at 38427ff.
- note: The retained R^2 row "must not be replaced by a tautology" - a defect the independent reviewer caught in draft; the manuscript repeats the warning (38347).

### research/version15/snapshots/v15-018/work/quartic248-optimization-20261109/guards-scalar/scalar-S-245-001/PROOF.md
- path: (as in heading)
- claim: Replacing the scalar comparison point S - P by S = [a]P (ratio equation Z j_S = h_S S_H, three coordinates and three rows deleted) preserves the defining property: soundness via v(F) > 5 nu/4, v(Z0) > 23 nu/8, v(Z1) > 19 nu/8 and [2m]S' = [4a]H; completeness for every a >= 3 via a Lucas sequence with j divisible by a - 2.
- author / date: /root/v14_arithmetic_review; date not stated
- status: "proposed new construction, not an independent acceptance"
- published theorems relied on: none new
- in_v17: YES. "The arithmetic change: 248 to 245", lines 38275-38299.
- note: Not a witness bijection at fixed root tuple. Removes the earlier need for a = 1 type congruence ("no condition a = 1 mod ... is introduced"). The manuscript condenses the Lucas completeness construction (item 7 of the note) to a sentence plus the determinant identity.

### research/version15/snapshots/v15-018/work/quartic248-optimization-20261109/trace-symmetry/reciprocal-scale-007/PROOF.md
- path: (as in heading)
- claim: Replacing lambda by rho = 1/lambda and deleting the trace coordinate T (imposing rho t1 = (1/4) Tr sum h_l^2, and G(rho)(1+q) = (1-rho)^10 with G = rho^10 F(1/rho)) gives a bijectively equivalent 239-variable, 213-row system; rho != 0 by positivity of the trace, lambda != 0 since F(0) = 0.
- author / date: /root/v14_final_disjoint_assembly_review; date not stated
- status: "author proposal ... Independent review is required"
- published theorems relied on: none
- in_v17: YES. "Reciprocal scale: 240 to 239", lines 38332-38337.
- note: rho = 1 (q = -1) and q = 0 are retained, as stated in both.

### research/version15/snapshots/v15-018/work/quartic248-optimization-20261109/trace-symmetry/root-product-model-006/PROOF.md
- path: (as in heading)
- claim: Each root block's eight field coordinates h, j, x, V, Q, W, I, Kout can be replaced by seven A, B, C, E, i, k, u satisfying nine K-quadrics, by mutually inverse rational maps with no division by A+-B, i, k, C, E; overall 245 -> 240 variables and 219 -> 214 equations.
- author / date: /root/v14_final_disjoint_assembly_review; date not stated
- status: "proposed exact quadratic presentation; independent review required"
- published theorems relied on: none
- in_v17: YES. "Root-product charts: 245 to 240", lines 38301-38330.
- note: Uses that d = 3 - sqrt2 is not a square in K (Norm 7) to get j != 0, and a real embedding to get h != 0; both appear in the manuscript (38326-38327).

### research/version6/optimization/combined/PROOF.md
- path: research/version6/optimization/combined/PROOF.md
- claim: For every rational x, P1272(x, -) has a rational zero iff P962(x, -) does; P962 has 962 coordinates, degree 4, 55,409 monomials, content 1 and height 64 S^2 (S = 3^(2^27)); proved by a new point chart u(X - u/4) = D, regrouped polynomial circuits, guarded quotient fusions, pole rescaling z = C e, and a signed correction chain.
- author / date: not stated
- status: not stated (frozen package with "independent source reviews included"); retains the baseline's Frei-Tinkova qualification
- published theorems relied on: none (pure rational-projection equivalence)
- in_v17: YES. `subsec:v6-962-compilation`, lines 17562-17870 (Theorem `thm:v6-962-polynomial` 17577; point chart lemma 17610-17645; logarithm 17655-17690; weights 17720-17762; correction chain 17778-17797; poles 17801-17822; anchor 17841-17853).
- note: The manuscript states the theorem relative to the "shared-point source" theorem rather than naming P1272 and its hash. The equivalence is of rational projections only; that the projection is Z is inherited.

### research/version6/optimization/field-quotients/final-b/PROOF.md
- path: research/version6/optimization/field-quotients/final-b/PROOF.md
- claim: In each detector the three coordinates R = di/ep, s = n^2, B = R s can be replaced by v, B with ep v = di n, B = n v (ep != 0 from F ep = (A delta)^5), saving nine coordinates (1,025 -> 1,016).
- author / date: not stated
- status: not stated
- published theorems relied on: none
- in_v17: YES. Equation (eq:v6-norm-final-weight) and following, lines 17746-17762.
- note: The intermediate counts 1,025/1,016 do not appear in V17 (only the final 962).

### research/version6/optimization/source-compression/PROOF.md
- path: research/version6/optimization/source-compression/PROOF.md
- claim: Pole rescaling (z = C e with C = 17b != 0, five intermediates instead of six at each of ten poles) and replacing eight Boolean corrections plus seven products by a chain c0^2 = 1, (ci - c(i-1))(ci - p_i c(i-1)) = 0 give an equivalent system with 17 fewer coordinates (1,272 -> 1,255).
- author / date: not stated
- status: "pending independent review"
- published theorems relied on: none
- in_v17: YES. Correction chain (eq:v6-correction-chain) 17778-17797; pole blocks (eq:v6-scaled-poles) 17801-17822.
- note: The note's "Rejected shortcuts" section (why the nine detectors cannot share pole witnesses, why one detector at a sum of two squares fails, why the preparation-zero alternative is not free here) is not in the manuscript; the 1,255 intermediate count is not either. The note stresses that C != 0 comes from the unchanged upstream guards, not from the new first equation.
