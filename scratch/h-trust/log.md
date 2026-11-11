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

## Step 4 (N5 lem:de-rham-descent L10939-11000; h-v14 §2.7, §3.2-§4)
- lem:de-rham-descent cites scholze2013 Cor1.8, Thms 9.1/9.3 + erratum; milne-av Pt I Thm 12.1(a); brinon-conrad Thm5.2.1, Prop6.3.3, 6.3.8.
  So N5's pst route = (c): Scholze dR + Berger dR=>pst. Brinon-Conrad = lecture notes (unrefereed) -> replaceable by Fontaine 1994 (h-v14 §4.4).
- a001 = (form correction: reproduced by scratch/h-v14/form_check.py) + (coarse-moduli application: NOT reproduced; BG "local index slip" in Lemma 3.1).
- ly-d6, igusa-theta: reproduced by scratch/h-v14/igusa_check.py from LY arXiv v1 + Igusa normalization.
- Uncited in V14/N5: free-quotient, effective descent, stable-model uniqueness (A078; removed by B1), I2, l-independence, Faltings Hom, Skolem-Noether, Chebotarev.

## Step 5 (rv-h-cm read)
- NoCM verdict "correct after repairs" R1-R5 (rv-h-cm §7.1). Corrected proof §7.2: (1) BG coordinate t=1+27j/16; (2) model
  Q(t)(sqrt(-t),sqrt(3(t-1))) from W-action + Shimura reciprocity at elliptic pts (Elkies = cross-check, R3);
  (3) fibre over t(u) has residue field Q(i), free W-orbit (scratch/rv-h-cm/check.py). Then GR(Gonzalez-Rotger JMSJ 58 2006) Thm5.12, Prop5.6
  (only under (f,6)=1), Thm5.8 (reciprocity), Lemma5.9; Vigneras (Emb). Removes Fowler, cmheight, GR14 CM use.
  Replace N5 L578-631, keep L564-577. H6 unchanged.

## Step 6 (h-leaves §4-§6 read)
- h-leaves §5.1 final table rows 1-23 with N5 lines + best sources. I1 Carayol 1986 Thm (A) (direction level<=conductor), I2 BLR Néron models §1.2 (used at N5 L781-784).
- h-leaves R5.1 (Faltings finiteness -> GR14 + Tate argument) is unreviewed; decision for T3: KEEP Faltings 1983 (refereed) for
  semisimplicity/End/Hom -> GR14 non-circularity (W4) becomes irrelevant (only matters if Faltings is derived from GR14).
- Raynaud criterion: SGA7 IX Prop 4.7 alternative to SZ95 Thm3.5 (UNCHECKED).
- §4.4 published replacements for unrefereed sources: Milne course notes -> Mumford 1970 / Milne 1986 (Cornell-Silverman);
  Brinon-Conrad -> Fontaine Astérisque 223; Conrad preprint App B -> Serre 1968 Ch III; Stacks -> SGA1/DM69 (moot after B1).

## Step 7 (N5 bibliography L11010-11209)
- Unrefereed sources cited in N5's H proof: brinon-conrad (CMI notes 2009), milne-av (course notes v2.00), babagranath (2005 MPI preprint),
  buzzard (author version 1996/2002), linyang (arXiv v1), conrad-local-characters (preprint 2011), milne ADT (book, 2nd ed 2006 = published).
  pan2022 cited as arXiv v2 with JAMS 35 (2022) 1031-1169.
- carayol bibitem = Ann. Sci. ENS 19 (1986) 409-468, Thm A: in N5 bib but not cited in H proof.

## Step 8 (Lean files + h-v14 summary)
- Height.lean module doc names "Shimura curves, Buzzard's integral models, modularity at five, effective CM"; SixContactEstimate docstring
  is statement-only. HeightMin.lean module doc + SixContactMin docstring are statement/derivation only (no trust statement).
- KERNEL_PLAN.md L20 H row: names "five unpublished upstream proof supplements" (target of T3 success criterion).
- h-a011/rv-h-a011 analysed V14's lem:qm-modularity-descent, not N5. N5 L720-774 already applies Pan Thm 1.0.4 directly
  (route (c): Scholze + Berger), twist via Conrad App B (V14: Deligne-Serre/Kato). So for N5: hypothesis discharges = rv-h-a011 table
  §3.1 transfers (same r_5, same hypotheses), but N5's twist paragraph L757-768 is not model-reviewed against N5 text.
- Twist/weight check (by reading): Pan => r ~ rho_g (x) psi, psi in Hom(rho_g, r) de Rham char a.e. unramified => finite * eps^n
  (Serre 1968 Ch III / Tate); weights {n, n+1-k} = {0,-1} => (n,k)=(0,2) only (n=-1 gives k=0). VERIFIED as argument.

## Step 9 (script reruns, sequential, each < 15 s CPU, ~/pyenv/bin/python, cwd /tmp/htrust-run)
- scratch/h-v14/form_check.py: output identical to form_check.output.txt.
- scratch/h-v14/igusa_check.py: identical to igusa_check.output.txt.
- origin/wip/h-b1:scratch/h-b1/b1_checks.py: identical to b1_checks.output.txt ("all 30 agree: True"). 0.7 s.
- scratch/rv-h-cm/check.py: identical to check.output.txt. 12.6 s.
- origin/wip/rv-h-novel:scratch/rv-h-novel/c1_constants.py, c2_sqrt_criterion.py: no output file committed on that branch
  (.out not tracked); rerun outputs saved in scratch/h-trust/reruns/; they match rv-h-novel log lines C1, C2
  ("transfer chain exact at Q=1e12, M in {1,2,7}: ok"; "tested 135 mismatches 0").
- c3_breaks.py (PARI idealramgroups) not rerun.
