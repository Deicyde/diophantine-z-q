# up-cr3 log

## Step 1: pole sections located and diffed (script: scratch/up-cr3/extract.sh, diff of sec:pole .. sec:mult)
- N5 diophantine_zq.tex sec:pole 973-1122: template E_l: y^2=x(x-l)(x+3l), PC thm 1001, RC thm 1005 (l = 11 mod 12 squarefree, corank Sel_{2^oo}=1 => ord L=1), RC proved in sec:rc..sec:limits (1760-5744).
- V13 manuscripts/quartic_v13.tex sec:pole 1049-~1207; V14 quartic_v14.tex 1681-1874; V15 research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex 1705-1898 (CRLF); V16 manuscripts/quartic_v16.tex 1705-1898.
- diff N5 vs V13: only two additions: attribution to [openaihtp, Sec 3] (V13 1050-1051) and a paragraph saying RC is the E=E_l, s_2(E)=1 case of [openaipointwise, Thm 1.1] and of [openaigoldfeld, Thm 1.1], "cited for attribution, not assumed" (V16 1742-1746).
- diff V13 vs V14: non-CM by Fowler class polynomial instead of nonintegral j; Poonen-Stoll locators (Cor 4, 7, Thm 8); BCDT via Silverman C.13.6; Kolyvagin pages 430-431; explicit J_1(N)->A modular quotient construction for Kato Cor 14.3.
- diff V14 vs V15: one sentence (pointer to Section v15:picard-norm) (V16 1871). V15 = V16 identically in sec:pole.
- Outcome: Q_pole, Lemma pole, PC, RC statement, descent S11-S12, Lemma corank, rational-point production (Sha[2]=0 from rank 1 + finite Sha) are unchanged N5 -> V16.

## Step 2: V16 limits on Kato 1999 / Ribet 1990, and their uses
- research/version16/README.md:19 "Fable's four-pass report leaves Kato 1999 and Ribet 1990 unread"; FINDINGS.json:33 "Kato1999 pp314-318 and Ribet1990 pp440-443 unread by Fable"; protocol/CURRENT-CORRECTIONS.md:23 (uninspected Kato and Ribet pages remain a limitation); review/current/REVIEW.md:55 (earlier four-contract review checked the enlarged-index Kato interface "without claiming all local-control results").
- Use of kato1999 (V16 bib 39545: Kodai Math J 22 (1999) 313-372, Thm 0.8, Ex 0.6.2): V16 2779-2784 and app:even-source 13780-13870: justify Kato [Asterisque 295] Thm 13.4(2) divisibility at p=2 (open image in SL2(Z2) over Q^ab via Ex 0.6.2; index set of Sec 0.1; norm relations (0.1.1)). Part of the RC proof (sec:rc), Kato Euler-system divisibility at 2.
- Use of ribet-geometry-1990 (bib 39489, Invent 100, Prop 3.3, 3.5(a)(b), 3.6): V16 15102-15122 (app:odd-source, paragraph "The finite-field evaluation map" 15078): supersingular enhanced curves / Eichler order of level N, Frobenius acts as involution, so supersingular points lie in X_0(N)(F_{l0^2}). Also inside the RC proof.
- Both are inputs of RC only; neither is used by PC's descent or the forward lemma.
- V16 sec:rc 2570-2576: RC's organization "follows" openaipointwise (OpenAI preprint 7 Oct 2026, Thm 1.1 "pointwise 2-converse for elliptic curves with rational two-torsion"; bib 39551); not readable here (no copy in ~/upstream: find -iname '*pointwise*' empty; upstream docs/manuscript-revisions/version10/sources.json:52-56 lists it as "Unpublished attribution source only").
- V16 2577-2601: E_l non-CM (j=35152/9); so RC concerns non-CM curves, while Route K's C_d have CM by Z[i].

## Step 3: later pole modules in V16 and the 214 proposal
- V16 RC proof span: sec:rc 2570 .. sec:compiler 6728 (RC concluded 6720) plus app:even-source 13339, app:odd-source 14844, app:endpoints 16582-17543 (~8,300 lines). N5: 1760-5744 plus 6825-10935.
- V16 seven-variable pole Psi(b) (eq:o8-pole, 8793-8798; B=17b; curves p^2=B(1-e)(1+3e), Bq^2=(s^2-Bh)(s^2+3Bh): same x(x-l)(x+3l) family, exceptional set {2,3,17}); Lemma hyp:o8-pole 8806-8815 proved from RC + Lemma corank; Lemma original-seven-simultaneous-realization 8870ff re-does the S11-S12 descent with RC (statement 8871-8882). V16 7622-7625: "seven-variable pole lemma ... proved from Theorem hyp:RC; it is not inferred from hyp:PC".
- V16 Prop "Linear-unit ordinary pole" 10671-10700: new module, soundness by valuation parity; completeness "under the same inherited realization and rank hypotheses" (10680-10682), i.e. RC again.
- 214 proposal (~/upstream-p214 110cf72, research/quartic214/): PROOF.md:25 source-carry; proofs/source-carry.md C04 (lines 11-17) retains RC verbatim for E_l, l=11 mod 12, applied to n_pole and n_pole*theta (V15:8870-8970 descent), points via finite Sha; proofs/existence.md:86 pole input squareclasses at 2,3,17 unchanged. No new pole route.
- grep Tian|Kriz|Smith|congruent number in V13-V16: no hits on the pole side (only Yuan2024 = integral moduli, and the Q(sqrt2) congruent-type curve y^2=x^3-d^2x with d=75-53sqrt2 of sec:model, V16 353).
