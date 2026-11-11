# up-cr3 log

## Step 1: pole sections located and diffed (script: scratch/up-cr3/extract.sh, diff of sec:pole .. sec:mult)
- N5 diophantine_zq.tex sec:pole 973-1122: template E_l: y^2=x(x-l)(x+3l), PC thm 1001, RC thm 1005 (l = 11 mod 12 squarefree, corank Sel_{2^oo}=1 => ord L=1), RC proved in sec:rc..sec:limits (1760-5744).
- V13 manuscripts/quartic_v13.tex sec:pole 1049-~1207; V14 quartic_v14.tex 1681-1874; V15 research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex 1705-1898 (CRLF); V16 manuscripts/quartic_v16.tex 1705-1898.
- diff N5 vs V13: only two additions: attribution to [openaihtp, Sec 3] (V13 1050-1051) and a paragraph saying RC is the E=E_l, s_2(E)=1 case of [openaipointwise, Thm 1.1] and of [openaigoldfeld, Thm 1.1], "cited for attribution, not assumed" (V16 1742-1746).
- diff V13 vs V14: non-CM by Fowler class polynomial instead of nonintegral j; Poonen-Stoll locators (Cor 4, 7, Thm 8); BCDT via Silverman C.13.6; Kolyvagin pages 430-431; explicit J_1(N)->A modular quotient construction for Kato Cor 14.3.
- diff V14 vs V15: one sentence (pointer to Section v15:picard-norm) (V16 1871). V15 = V16 identically in sec:pole.
- Outcome: Q_pole, Lemma pole, PC, RC statement, descent S11-S12, Lemma corank, rational-point production (Sha[2]=0 from rank 1 + finite Sha) are unchanged N5 -> V16.
