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
