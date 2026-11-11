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
