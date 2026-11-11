# rv-up log

Adversarial verification of up-map, up-h, up-cr3, up-rest. Sources: N5 = diophantine_zq.tex (this worktree);
V13-V16 under ~/upstream (commit d76bcde); V15 = ~/upstream/research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex.

## Step 0
- No prior log; fresh start. Read docs/research/up-map.md (556 lines).

## Step 1 — item 1 (statements byte-identical N5 vs V16)
Script: scratch/rv-up/envcmp.py (own, independent of up-map's extract.py); compares CR-stripped lines.
- thm:target N5 60-76 = V16 113-129 IDENTICAL; thm:height N5 404-409 = V16 707-712 IDENTICAL;
  hyp:PC 1001-1004 = 1736-1739; hyp:RC 1005-1011 = 1746-1752; prop:fixed-prime-pattern 1267-1297 = 2076-2106;
  prop:cutoff 6285-6293 = 7268-7276; lem:pole 988-991 = 1723-1726; prop:generator 268-270 = 364-366;
  lem:assembly 110-113 = 204-207; prop:box 1225-1229 = 2034-2038. All IDENTICAL.
- H setup + constants block: N5 378-399 = V16 479-500 IDENTICAL (22 lines; constants F_0..H_6 at N5 391-396 = V16 492-497).
  up-map's "N5 l.390-400 = V16 l.489-499" is a misalignment (ranges differ, offset is +101 not +99); up-rest's
  "N5 L389-397 = V16 L491-499" also off by ~one. Minor locator error only. The line after (N5 400 vs V16 501) differs:
  "direct modularity argument" -> "published prime-five modularity theorem" (not part of statement).
- Pole section opening N5 973-1011 vs V16 1705-1752: only additions = openaihtp attribution (V16 1706-1707) and
  openaipointwise/openaigoldfeld paragraph (V16 1740-1744). Q_pole, E_l: y^2=x(x-l)(x+3l) (N5 986 = V16 1721) identical.
- Catalogue definition N5 238-245 = V16 331-338 IDENTICAL.
- Sections 9-12 (+ start of 13): N5 4382-6442 = V16 5365-7425 IDENTICAL (2061 lines). Includes catalogue bound in §12.
- lean/Frozen/BoundedIntegerPolynomial.lean: cmp byte-identical (sha256 0889579a...). lean/: 60 files each, only README.md differs.
- construction/: 28 files each; only README.md differs (upstream retitles "Original large construction"). up-rest says
  exactly this; the task prompt's "construction/ byte-identical" is true except README.md.
Verdict item 1: CONFIRMED (with locator correction for the constants block; construction/ modulo README.md).

## Step 2 — item 2 (up-h)
(a) envcmp.py: thm:height and H setup/constants block (N5 378-399) IDENTICAL in V13 (480-485), V14 (682-687),
    V15 and V16 (707-712); constants block at F_0 line -13..+8 identical in all four. CONFIRMED.
(b) V16 lem:qm-modularity-descent statement L505-528, proof L530-692 read.
    - C3: F chosen finite Galois over Q (V16 L536-537); Milne 1986 Thm 15.1(a) p.129 (L561); Fontaine 1994 Thm 3.8 p.142
      (L564-565); descent from a finite Galois local K'/Q5 (L566-571). Restriction F->F' step not needed. CONFIRMED.
    - C8: arithmetic Frobenius, Deligne-Serre §§1.6-1.9 + Lemma 3.2 for a primitive normalized f (L586-601); k=1 excluded via
      Deligne-Serre Thm 4.1 (L604-616); Kato 2004 §6.3, §9.4 p.188, §§5.4, 8.3 all levels incl. 5|N (L618-634);
      det V = eps^{1-k} eps_f^{-1} (14.10.2-3) (L635-640) -> HT(U_f)={0,1-k}, det U_f = eps_f eps^{k-1} (L644-650);
      k=2, m=0 (L652-659); determinant finiteness (L660-667). CONFIRMED.
    - A9: Milne, Introduction to Shimura varieties (Clay 2005), Thms 6.7-6.8, Cor 6.9, p.319 at V16 L1271. CONFIRMED.
    - All present in V14 (grep: fontaine L540, Kato §9.4 L597, alpha L635, milne-shimura2005 L1247); absent in V13.
      V14 L505-667 = V16 L530-692 IDENTICAL (163 lines). V14 §4 vs V16 §4: 5 hunks only (b11 citations). "From V14 on" CONFIRMED.
(c) N5 769-775 = V16 1468-1474 IDENTICAL (C9 Euler-factor). CM branch N5 578-631 = V16 1285-1338 IDENTICAL.
    N5 868-907 = V16 1589-1628 IDENTICAL (Javanpeykar/GR). N5 828 = V16 1539, N5 835-839 = V16 1546-1550 IDENTICAL (rv-h-novel R2,R3).
    A9 descent C->Qbar sentence (N5 568-571) identical in V16 L1275-1278 (up-h says L1274-1276 = N5 L568-570: off by one;
    V16 adds a Galois-descent sentence at L1264-1269 but it concerns L, not C->Qbar): R-A9-2 kept CONFIRMED.
    I2 / l-independence uncited at V16 L1486-1489: CONFIRMED.
(d) Determinant argument checked by hand (see rv-up.md §2): sound. Requires (HT) for psi's weight to get k=2, but no
    local algebraicity. Changes no constant, no Lean statement (proof text of a trust note only).

## Step 3 — item 3 (Baba-Granath record), reading
- Read ~/upstream/research/version14/proofs/a001-moduli-current-v1/ADVERSE-CASE.md (14 lines) and PROOF.md (57 lines).
  Record: BG Prop 3.7 proof (printed p.743) infers phi=(f1_*,f2_*): J(C(-24)) -> E1 x E2 is an iso from "f1(a)=f1(b),
  f2(a)=f2(b) => a=b"; record shows phi phi^dagger = ([2],[2]), deg phi = 4; counterexample (+-sqrt r, 0). Says it is a
  proof concern, not a falsity claim about 3.7's statement. Chain: LY eq.(2) attributed to BG; BG 3.9 uses 3.7's CM calc.
- Read ~/upstream/research/version14/proofs/ly-d6-normalization-v1/PROOF.md: derives [J2..J10](j) from LY Example 30
  (divisor identities, Y1 and Y'5 parametrizations, disc -24 intersection x=-6+-6sqrt(-3)) + LY (13)-(14), without
  LY eq.(2) or BG 3.7-3.10.
- Fork: N5 cites BG at L422 (branch data, with LY) and L533 (polarized relation V_Z = V/W, A7); LY eq.(2) at N5 L911 (F1).
  h-trust: BG at l.89, 185-188 (A2: Thm 2.1 + "§3"), 252 (A5 Lemma NV: W=(Z/2)^2), 286-291 (A7: Thm 2.1), 786, 853, 928, 972, 1025;
  F1 l.688-696 lists "Lin-Yang 2020, eqs. (2), (14), (13)".
- scratch/h-v14/igusa_check.py (read): derives c1..c4 from LY Ex.30 data at P_-4 (Y1, u=1728) and P_-24 (Y'5,
  x=-6+6sqrt(-3)), then [J2..J10](j) and the theta constant 3779136. It does NOT consume LY eq.(2); its -19 line is an
  arithmetic tautology (c1*81/64 = 81/64), not an input. So F1's computation route = upstream's ly-d6 route.
- scratch/rv-up/bg37.py (output bg37.output.txt): for generic y^2=f(x^2), the Weierstrass points (+-s,0), f(s^2)=0,
  have equal images under both bielliptic quotients; the separation claim fails exactly at iota-fixed points.
  deg phi = 4 from phi phi^dagger = diag([2],[2]) (STANDARD; Frey-Kani 1991 / Kani: J ~ (E1xE2)/graph of E1[2]->E2[2]).
  The record's numbers for C(-24) (disc f = 442368 = 2^14*3^3, f(0)=1-sqrt 2) NOT checked: BG's curve not available here.
  The printed BG sentence itself NOT read (no copy of CJM 60 here); verdict on "printed sentence" rests on upstream's quotation.
- scratch/rv-up/theta24.py (mpmath, 40 digits; output theta24.output.txt): at the four disc -24 Heegner points of X_0(5)
  (forms [5,+-4,2],[10,+-4,1]) x(z) = -6 +- 6 sqrt(-3) (|x^2+12x+144| < 2e-37), and F1's theta expression
  3779136 (prod theta)^4/(sum theta^8)^5 at Omega = z[[3,5],[5,10]] equals -16/27 to < 2e-39. Independent of LY's
  polynomials, LY eq.(2) and BG. Remaining input: Omega(z) is the QM point P_-24 (next: endo24.py).
- scratch/rv-up/endo24.py (exact; PARI matkerint + sympy; output endo24.output.txt), A = C^2/(Omega Z^2+Z^2),
  Omega = z[[3,5],[5,10]], z root of 5z^2+4z+2 (disc -24), principal polarization E=[[0,I],[-I,0]]:
  End(A) rank 8, a ring, Rosati-stable; an embedding of N5's O = Z<1,I,(1+J)/2,(I+IJ)/2> with Rosati
  a -> mu^{-1} conj(a) mu, mu = 2J+IJ, exists (found as iota(O) with induced mu' = (-3I+4J+IJ)/2, mu'^2=-6, then conjugated
  by a normalizer element gamma with gamma mu' gamma^{-1} = +-mu; final I, J printed and all relations rechecked on 4x4
  integer matrices). Commutant of iota(O) in End(A): rank 2, discriminant -24 (basis 1, w with w^2+4w+10=0), i.e. the
  maximal order Z[sqrt(-6)]. So A is the QM point P_-24 (CM by the maximal order of disc -24) for N5's datum.
  With theta24.py: F1's formula gives j(P_-24) = -16/27, with no use of BG 3.7/3.9, LY eq.(2) or LY's Y'5 claims.
- Consistency at a third CM point: theta24.py 5 1 1 81 64 (theta19.output.txt): at z=(-1+sqrt(-19))/10, x=36 and F1's theta
  expression = 81/64 to 3e-39; endo24.py 2 5 1 1 (endo19.output.txt): same O-embedding with mu-Rosati exists, commutant
  disc -19. Agrees with LY's / BG's j(P_-19)=81/64 (a consistency check only; the global shape on X still needs LY Ex.30's
  divisor statements).
- h-trust dependence: only F1 (l.691) and l.797 name LY eq.(2); no step names BG Props 3.7-3.10. A2 (l.185-188) cites BG
  "§2.1 (Thm 2.1) and §3" (locator broad enough to include 3.7-3.9); A5 (l.252) BG for W=(Z/2)^2; A7 (l.286-293) BG Thm 2.1
  + LY (13)-(14), Ex. 29-30 via igusa_check.py; l.89, l.928 general. h-v14.md l.335 (A017) also cites LY (2).

## Step 4 — item 4 (22P / GI / route AP)
- V16 L2215-2228: 22P proof takes GI(20) from Section v15:gi-full (L2217) [with greentao Main Thm p.1763, moebius Thm 1.1].
- v15:gi-full = Part at V16 L23831 (next Part L30185). diff V15->V16 hunks: 40, 42, 20060-20077 (TZ), 26822-26842 and
  26908-26915 (horizontal normalization, inside the GI Part), 30664, 30677 (GR), bib 39342-39346, 39920-39926.
- research/version16/FINDINGS.json: first finding "horizontal-normalization": "missing at finite-cover site". So V16's first
  correction (in FINDINGS order) fills a step missing in the GI Part that 22P consumes. (up-map §4 lists TZ first, manuscript
  order; no conflict.) up-rest "L26821-26842": diff says 26822-26842 (off by one).
- Fork: ZInQ.greenTaoDense (ZInQKernel/External/GreenTaoDense.lean:28) and ZInQ.Density.goodPrimeDensity
  (ZInQKernel/Density/PropDFinal.lean:24) are theorems; no `sorry` in those dirs, no `axiom` decl in ZInQKernel (grep);
  MainGreenTao.lean:21-31 feeds them to the main theorem. aud-ap.md l.238-239 records #print axioms = [propext,
  Classical.choice, Quot.sound] (not rerun; no Lean run needed). Green-Tao 2008 = transference + Szemeredi, no GI (STANDARD).
Verdict item 4: CONFIRMED.

## Step 5 — item 5 (pole side)
- diff N5 sec:pole 973-1122 vs V16 1705-1898: hunks 1a2-4 (openaihtp attribution), 32a36-41 (RC = case of openaipointwise /
  openaigoldfeld, "cited for attribution, not assumed"), 41-42c50-53 (non-CM via Fowler), 107-109c118-125 (Poonen-Stoll
  locators), 120-121c136-139 (BCDT via Silverman C.13.6), 132c150-176 (Kolyvagin pp.430-431 + explicit J1(N)->A).
  Removed text: only the 8 lines of those sentences. Q_pole, E_l template, lem:pole, PC, RC, descent, points unchanged.
- V16 1887-1897: RC on n and n theta + lem:forward-rank (Kolyvagin Thm 1, V16 1843) -> rank 1, Sha finite, Sha[2]=0 ->
  Kummer class represented by points. V16 2779-2785: Kato 13.4(2) at 2 via kato1999 Thm 0.8. Ribet 1990 V16 15105-15116.
- grep V16: Kriz 0, "congruent number" 0; "Tian" 4 hits = Cai-Shu-Tian (explicit Gross-Zagier; V16 3353, 13307, 14908, 30146,
  bib 39483), not TYZ; "Smith" = Smith normal form; Gross-Zagier bib 39456 cited once (V16 13316 table). up-cr3 l.182
  "grep Tian, Yuan finds only Yuan2024" is inaccurate (CST); its conclusion "TYZ never cited" stands.
- openaipointwise/openaigoldfeld cited at V16 1741-1742, 2572-2574 ("organization ... follows"), 13066 (source catalogue:
  S30, S18, S29, S32 = Sections 2,4,5,9 of openaipointwise, "provenance labels ... not independent arithmetic
  assumptions", V16 13064-13069). The S12/S18/S29/S30/S32 *-frozen-4eaee875.tex rows are already in N5 L6627-6647.
  So: no logical premise per the manuscript; textual provenance of RC sections. up-cr3 does not mention the catalogue.
Verdict item 5: CONFIRMED with two minor corrections.

## Step 6 — item 6 (quoting)
- scratch/rv-up/quotes.py: 8-token shingle match of the four notes + all scratch/up-*/ files against an upstream corpus
  (scratch/rv-up/quotes.corpus.txt: 7307 files, 362 MB: every manuscripts/*.tex, the V15 snapshot tex, research/version14-16,
  collaborator notes, docs/, p214 research/quartic214, top-level READMEs; files > 5 MB and other snapshots excluded).
  Runs >= 25 words: none (quotes.output.txt empty). With 6-token shingles and >= 12 words (quotes12.output.txt): 19 runs,
  longest 21 words (up-map l.162-164, the V16 l.155-159 sentence), then 16, 15 words; all bibliographic titles or one-sentence
  quotations. No passage longer than about 1.5 lines. Verdict item 6: CONFIRMED.

## Step 7 — deliverables
- docs/research/rv-up.md written (verdict table, details §§1-7, proposed h-trust changes §3.5).
- .fleet/rv-up.md written.
- Additional finding while drafting: up-h did not treat the BG ADVERSE-CASE handed over by up-map (grep up-h.md/log: no hit).
