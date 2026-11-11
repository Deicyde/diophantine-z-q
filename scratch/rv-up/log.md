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
