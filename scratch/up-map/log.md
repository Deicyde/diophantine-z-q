# up-map log

## Step 1 (survey)
- ~/upstream readable (commit d76bcde). Manuscripts: manuscripts/quartic_v9..v14,v16.tex; archive/quartic_12504 (V2, Nov 5), quartic_9625 (V3, Nov 6), quartic_4973 (V4, Nov 6), quartic_1272 (V5, Nov 6), quartic_v7, v8 (Nov 6); v9-v13 dated Nov 7, v14 Nov 9, v16 Nov 11 (line 42); v15 at research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex. V6 not in tree (manuscripts/README.md: only in a GitHub release).
- N5 = worktree diophantine_zq.tex (11259 lines, date Nov 5, l.37). Upstream V2 (quartic_12504.tex, 14087 lines, Nov 5) has the identical Thm 1.1 (l.63-79) and Thm 4.1 (l.415) and adds §"The base residual compiler" (l.6602) and §"An explicit quartic definition" (l.8679, Thm thm:quartic l.8688: 12504 vars, quartic, coeffs < 2^80).
- V16 (l.98-110): Thm thm:v15-decimal: 314-variable quartic P_314, explicit, 6672 monomials, coeffs < 2^6496; Thm thm:v15-main: 222-variable family P_N, ineffective N_0.

## Step 2 (key statements, N5 vs V16)
- scratch/up-map/extract.py extracts a labelled environment. Statement text of thm:target, lem:assembly, prop:generator, thm:height, hyp:PC, hyp:RC, prop:fixed-prime-pattern, prop:box, prop:cutoff is byte-identical N5 vs V16. VERIFIED.
  N5 lines: 60-76, 110-113, 268-270, 404-409, 1001-1004, 1005-1011, 1267-1297, 1225-1229, 6285-6293.
  V16 lines: 113-129, 204-207, 364-366, 707-712, 1736-1739, 1746-1752, 2076-2106, 2034-2038, 7268-7276.
- Labels present in every version V3..V16 (grep, line table recorded in up-map.md).
- V16 section map: §1-§13 N5 core (l.76-7586, height § grew 473-1705 vs N5 377-973); §Base residual compiler 7587; quartic §§ 9950-13002; appendices; App "Simultaneous primes with coprime adjacent norms" 17544; quartic presentations sec:v9 20357, sec:v12 20981, 394-var 21953, sec:v14 22816; Part GI (polynomial inverse theorem) 23831-30083; Part "222-variable family" 30185-39914.

## Step 3 (section-level diff chain)
- scratch/up-map/secdiff.py; output for N5->V2->V3->V4->V5->V7->V8->V9->...->V16 in scratch/up-map/secdiff-chain.txt. VERIFIED (computation).
- N5->V2: core unchanged except §1 (+8 lines, quartic mention) and de Rham appendix (+64); adds base residual compiler + quartic §.
- N5 core §§2-13 changes occur only at V9->V10 (small, many sections: §3 +3, §4 +5, §5 +9, §6 +41, §7 +22, §8 +53, §13 +16, apps) and V13->V14 (§4 height -146/+778, §5 pole -8/+43, §6 -5/+6, §7 RC -12/+117, de Rham appendix GONE, merged into §4). §§9-12 (limits, compiler, bridge, cutoff) identical N5->V16.
- V15->V16 diffs: App "Simultaneous primes with coprime adjacent norms" (-10/+15), GI "Sections 9--11" (-3/+29), "Integral evaluation and the effective contact height" (-2/+2), explicit 222 quartic (+5), provenance, AI statement.
- New appendices: "Simultaneous primes with coprime adjacent norms" since V5 (quartic_1272 l.15831), grown in V7, V9, V14.

## Step 4 (§4 height and §5 pole, N5 vs V16)
- §4 intro: N5 l.401-403 "direct modularity argument at coefficient prime five"; V16 l.475-477 adds "the preprint's height assertion is not taken as an additional premise" and l.501-503 "published prime-five modularity theorem". Constants H_6 etc. identical (N5 l.390-400 = V16 l.489-499). VERIFIED.
- V16 adds Lemma lem:qm-modularity-descent (l.505-528, proof to ~l.692): QM abelian surface rho_5 -> weight-2 newform via Calegari ICM 2022 p.624 [calegari-icm2022, bib l.39652] (proof source Pan [pan2022, bib l.39309]); also Faltings 1986, Scholze 2013, Fontaine 1994, Deligne-Serre 1974, Kato, Washington, Shimura, Li. "Scope" paragraph l.694-704 cites direct-p5-modularity-project (bib l.39140, research/version14 supplement).
- Citation counts §4 (scratch: cites over line ranges): N5 §4+deRham app: linyang, gr2014, faltings1983, scholze2013, brinon-conrad, pan2022, buzzard, babagranath, cmheight, pazuki, li-newforms, shimura-factors, ...; V16 §4 adds Deligne1971(9), deligne-serre1974, kato, calegari-icm2022, milne-shimura2005, igusa1967, carayol1987, voight2021, serre-tate, and project supplements ly-d6-normalization-project (l.39277), igusa-theta-project (l.39377), a001-moduli-project (l.39273) under research/version14/proofs/.
- §5 (N5 973-1122 vs V16 1705-1898): Q_pole, E_l: y^2=x(x-l)(x+3l), lem:pole, PC, RC statements and the descent reduction text identical. Added: attribution to openaihtp §3 (l.1706-1707); RC is "the E=E_l, s_2(E)=1 case of [openaipointwise, Thm 1.1]" and of [openaigoldfeld, Thm 1.1] (l.1740-1744; cited for attribution, not assumed); non-CM check via Fowler class polynomial; lem:corank proof cites Poonen-Stoll Cor 4,7, Thm 8; lem:forward-rank: BCDT via Silverman C.13.6, Kolyvagin Thm 1 pp.430-431, explicit J_1(N)->A via Picard norm (§v15:picard-norm), Kato Cor 14.3. VERIFIED.

## Step 5 (§6 multiplication / 22P, N5 vs V16)
- V16 is CRLF (use diff --strip-trailing-cr).
- §6 (N5 1123-1759 vs V16 1899-2569): attribution "adapt [openaihtp, Section 2 and Lemma 6.1]" (V16 l.1900-1901); twelve tests redefined explicitly with conjugated primed ratios A_i - sigma(A'_i) (V16 l.1951-1958 vs N5 l.1172-1174); valuation deduction at a contact prime rewritten as an explicit argument (V16 l.1978-2007 vs N5 l.1194-1198). prop:box and prop:fixed-prime-pattern statements unchanged.
- 22P proof: N5 l.1405-1418 uses Green-Tao Main Theorem p.1763 + Green-Tao Moebius Thm 1.1 + [gtz, Thm 1.3] (GTZ inverse theorem, arXiv v5 + erratum); V16 l.2214-2224 replaces gtz by Section v15:gi-full (local polynomial inverse theorem proof, Part at V16 l.23831-30083), "GI(20) and MN(20)". Rest of 22P proof (catalogue, Dirichlet, W-trick, Mertens) unchanged. VERIFIED.

## Step 6 (§7 RC, N5 1760-2717 vs V16 2570-3651)
- Added attribution: organisation follows [openaipointwise] (ring-class interpolation, determinant transfer, coefficient systems), broader converse in [openaigoldfeld] (V16 l.2571-2577).
- Non-CM: explicit invariants + Fowler class polynomial (V16 l.2582-2600). Modularity: BCDT via Silverman C.13.6/C.16.4, newform via [amirhong Thm 3.1], Shimura Thm 1, Faltings 1983 isogeny (l.2612-2677, was BCDT+Milne MF). Parity: [ddselmer Thm 1.4] replaces [dd Thm 1.8] (l.2686-2689). At 2: [kato1999 Thm 0.8] (l.2781-2785). New paragraph "native genus lattice" (l.3317-3342). Cornut-Jetchev Thm 3.1 replaced by §v15:cm-oriented (l.3448-3449). VERIFIED (diff).

## Step 7 (quartic constructions and their inputs, V16)
- scratch/up-map/refmatrix.py: per-section \ref matrix of key labels in V16 (output recorded in up-map.md). VERIFIED.
- Base residual compiler §(V16 l.7587, label sec:degree8-original): prop:o8-finite F_8 in 15672 vars, degree 8, 129497 monomials, coeff < 2^80 (l.7598-7610); thm:o8-conditional (l.7612-7619); inputs: hyp:o8-height five-contact estimate (l.7651-7656: contacts {inf,0,1,2401,-343/32}, S_* = primes <= 76176, h(a) <= H_* M_5(a)^24, via Shimura curve disc 210, Gonzalez-Rotger 2006), hyp:o8-pole seven-variable pole lemma (l.8803) proved from hyp:RC (l.8870), not from PC (l.7622-7626 says thm:height has a different contact set and is not used).
- Quartic thm:quartic (l.9957), sharper five-contact thm:quartic-height19 (l.10005), uses GI (l.10406). 962-var quartic (l.11789, thm l.12479) uses thm:v5-simultaneous-primes (App l.17544-, Sun arXiv:2610.20691v2 [v5sun bib l.39185], Mitsui, Green-Tao, GI) + hyp:o8-pole + hyp:o8-height. 523/540 (sec:v9 l.20357): thm:quartic-height19 + hyp:o8-pole + simultaneous primes. 498 (l.20981) refs hyp:o8-pole.
- 222 family (Part l.30185): v15:height (l.30186) refs thm:quartic-height19 (l.30731); amplification, selection, dependencies ref thm:v5-simultaneous-primes.
- None of the quartic/222 sections references thm:height (H), hyp:PC or prop:fixed-prime-pattern. RC is used by hyp:o8-pole (quartic route). VERIFIED (refmatrix).
