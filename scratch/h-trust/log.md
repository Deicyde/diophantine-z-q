# h-trust work log

## Step 1 (inputs located)
- Base: 8718d41d. h-map.md read (on main).
- origin/wip/h-b1 (d7d8d78f): h-b1.md read. Lemma PR (i)(ii), Prop. TS, Lemma NV; all PROVED HERE, unreviewed.
- origin/wip/rv-h-b1 = 8718d41d (no review yet) -> B1 status: "repository argument, unreviewed".
- origin/wip/rv-h-novel: rv-h-novel.md read. 9 steps correct; repairs R1 (state omega_p(-1)=chi_p(-1)),
  R2 ("If e<=D" -> "Since e<=D"), R3 (cite subgroup formula, Serre Local Fields IV§1 Prop2, §3 Prop15; uses L_v/Q2 Galois).

## Step 2 (rv-h-a011 read)
- B2 verdict "proved after repairs" R1-R5 (rv-h-a011 §5): R1 cite Pan arXiv:1901.07166v2 Thm 1.0.4 (JAMS 35 (2022) 1031-1169, numbering UNCHECKED);
  R2 Pan's proof internally uses SW99/SW01/Kisin/Hu-Tan (policy: leaf = Pan's stated theorem); R3 Berger removed from hypothesis check only;
  R4 Breuil Cor 5.3.4 direction used (good=>crys, sst=>sst) is unreferenced attribution to Fontaine; R5 extra V14 places.
- pst at 5 routes: (a) Lemma PG (B ramified at 3 => good reduction over K'), (b) SZ Thm3.5 + Breuil Cor 5.3.4, (c) Scholze dR + Berger.
- HT weights: Scholze 2013+erratum (or Tate 1967 under route (a), F5 SPECULATIVE).
- rv-h-a011 line numbers are V14, not N5; need N5 mapping.

## Step 3 (N5 L377-972 read; sha256 cb1148cd..., commit 97cec7fd)
- N5 proof of thm:height cites NO project supplement by key (grep: supplement words only at L6611+).
  Supplement content is inline: integral model L443-507 (Buzzard Thm2.1/Cor2.3 + inline stable-model/tame-quotient),
  pullback L509-523, K and good reduction L524-530.
- N5 already applies Pan directly: L756 \cite[Theorem 1.0.4]{pan2022} at l=5; pst via Scholze2013+erratum (dR, lem:de-rham-descent)
  + Berger2002 (L737-741) = rv-h-a011 route (c). Oddness by Betti L742-752 (Milne-av? no cite). Twist: Conrad local chars App B, Li p.296, Shimura Thm1.
- N5 citation keys in proof: linyang, babagranath, buzzard, milne-av (Pt I Thm2.8-2.9), fowler (Prop2.7), cmheight (Eq 6.2), gr2014 (Thm1.4, §9),
  faltings1983, milne (ADT Ch I), scholze2013, scholze-erratum, berger2002, pan2022 (Thm1.0.4), conrad-local-characters (App B pp32-33),
  li-newforms (p296), shimura-factors (Thm1), serrelocal (4.1-4.3), silverbergzarhin (Thm3.5), silverman (IV.6.4 p132),
  javanpeykar (Thm1.1.1, §2.3), lny (§2.2 p4), pazuki (Cor1.3(2)).
- Conductor->level L852-857: "local-global compatibility", no citation in N5 (Carayol uncited) = I1.
- Uncited in N5: I2-type (L550-561 inertia on Tate module of W_0 / Hom reduction), l-independence (L782-783), Carayol (L854),
  Hom theorem L863 cites faltings1983 nearby (L733) only.
- Steps L531-545 (all conjugates geometrically isomorphic; Igusa invariants in j) and L546-563 (Hom field L, [L:Q]<=D)
  are N5's own arguments; not in rv-h-novel scope (premises).
