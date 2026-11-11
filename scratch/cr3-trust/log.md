# cr3-trust work log

## Step 1 (read sources)
- Read h-trust.md (format: marks VERIFIED/STANDARD/UNVERIFIED/SPECULATIVE; status [R]/[P]/[M]/[U]/[S];
  §1 outline, §2 residuals, §3 docstring drafts).
- Read nt-tyz.md (Prop N, I1-I7, Lemmas N1, N2, F3-F6, §5.2 unrefereed sources, §1.1 journal version).
- Read rv-nt-tyz.md: verdict (a),(b),(c) proved; repairs B1 (I2 as congruence, m=3 w_K), A1 (set
  partition convention), B2/B3 (F4 and 2nd half F3 unused; eps on (5,3) unused), A2, B5 (L2076).
  B4: deep inputs Thm 3.3, Thm 3.5 first assertion, Lemmas 3.18, 3.21 not re-verified.
  C1: Prop 0, tyz-5b Lemma 4.1, Thm 4.3, Thm 3.6 not re-proved there (tested on 50 curves).

## Step 2 (Lean forms and implications, read from source at 14b28b23)
Definitions (file:line):
- CertifiedRank: Hypotheses/CertifiedRank.lean:50 (system Σ(𝒞_d) 8 sols, first coord a, |a|≡7 ⟹ point x≠0, x/a square)
- CertifiedRankSel: RouteK/Selmer/Covering.lean:385 (#Sel2=8, ∃(a,b)∈Sel2 |a|≡7 ⟹ ∀ Sel class Loc)
- CertifiedRank5b: RouteK/Rank5b/Row5b.lean:209 (#Sel2=8, det M5b=1 ⟹ ∀ Loc)
- CertifiedRankTYZ: Rank5b/Sec3/TYZ.lean:125 (#Sel2=8, T5b=1 ⟹ ∀ Loc)
- CertifiedRankTYZCl: Sec3/RedeiStatement.lean:99 (#Sel2=8, T5bCl=1 ⟹ ∀ Loc)
- CertifiedRankRk / TYZRk / TYZClRk: Rank/Statements.lean:43/59/72 (⟹ point of infinite order; TYZ(Cl)Rk no Sel2 cond)
- CertifiedRankDLRk: RankDL.lean:78; CertifiedRankDLAdmRk: RankDL.lean:190
- Inf forms: RankInf.lean:109,120,131,143 (InfinitelyManyPoints d)
Implications:
- certifiedRank_of_certifiedRankSel (Selmer/Prop0.lean:100); certifiedRankSel_of_certifiedRank5b (Row5b:214);
  certifiedRank5b_of_certifiedRankTYZ (TYZ.lean:130); certifiedRankTYZ_iff' (Redei/FourRank.lean:363, Cl↔TYZ);
  certifiedRankTYZ_iff_of_redeiFormula (RedeiStatement:115)
- Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk (FourRank:367); certifiedRankRk_of_certifiedRankTYZRk (Statements:80)
- certifiedRankSel_of_certifiedRankRk' / certifiedRank_of_certifiedRankRk' / certifiedRankTYZ_of_certifiedRankTYZRk' /
  certifiedRankTYZCl_of_certifiedRankTYZClRk' (RankVariants.lean, with fg_points = MW)
- certifiedRankDLRk_of_certifiedRankRk, _of_certifiedRankTYZRk (RankDL:119,108); certifiedRankDLAdmRk_of_certifiedRankDLRk (198)
- poleCompleteness_of_certifiedRankDLRk (174), _DLAdmRk (206)
- Inf ↔ Rk: certifiedRank{,TYZ,TYZCl,DL}Inf_iff_... (RankInf:148-164), via exists_infinite_order_iff_infinitelyManyPoints
Main-theorem variants: MainGreenTao.lean:38 (CertifiedRank), :45 (Sel); Rank5b.lean:37 (5b, ALSO takes 22P
  FixedPrimePattern hypothesis!); Rank5bSec3.lean:54 (TYZ), :67 (TYZCl); RankVariants:52,59,67 (Rk forms);
  RankDL:220 (DLRk); RankInf:176-197 (Inf). No main-theorem variant takes DLAdmRk directly (only PC).
Observation: CertifiedRank docstring still lists Kriz first route and "Gross–Zagier–Kolyvagin"; TYZ.lean cites GZ only.

## Step 3 (selection scan, select.py -> out_select.txt)
Input: squarefree d ≡ 5 mod 8, d < 30000, 3-5 primes. T5b by Redei bits (mirror of Lean T5b,
rv-cr5b-sec3/mirror.py), #Sel2 by mirror.sel2 (local Kummer images, Lean's Loc conditions).
Outcome: 386 d with T5b = 1; ALL have #Sel2 = 8; none with #Sel2 > 8.
So on this range the premise #Sel2 = 8 of the TYZ forms is implied by T5b = 1 (empirical; rv-cr5b-sec3
§1.6 left this open). SPECULATIVE that it is a theorem (det M5b = 1 forcing minimal Selmer).

## Step 4 (reviews located)
- rv-cr3-rank (branch origin/wip/rv-cr3-rank, aec3b570; NOT in this base) reviewed the three Rk
  statements (faithful, shortCurve(-d^2), Mathlib AddCommGroup instance) and RK9/MW; remarks R1-R4.
- rv-cr3-dl.md reviewed CertifiedRankDLRk (in base). d2-check.md: numerical guard on DLRk curves.
- Inf forms (RankInf.lean): no model review found (only blueprint pages + .fleet/cr3-inf.md on branch).
  Checked here by reading: InfinitelyManyPoints d = Set.Infinite {(x,y) ∈ ℚ² | y² = x³ − d²x};
  four ↔ theorems proved via exists_infinite_order_iff_infinitelyManyPoints (fg_points).
- rv-redei §1.1 (gCl = #Cl² of full ring of integers = TYZ g), §1.4 (T5bCl = Prop N's T_5b).
- rv-cr5b-sec3 §1.4-1.7 (T5b = TYZ (7,3) bracket mod Redei; premises; chain), §2.2 (GZ + aux).
- pc-audit RK4 (TYZ def of 𝓛(n) uses regulator of generator: needs GZ+Kolyvagin inside TYZ), RK7.
- First tyzcl_check run: 23/30 ok, 7 "FAIL" only because ellrank returned [1,1,0,[]] (no point);
  script patched to fall back to ellheegner; rerun in progress.

## Step 5 (tyzcl_check reruns)
- ellheegner fallback too slow at conductor 32·10293² (killed at the 10-min background limit).
- ellrank(E, effort 2/4/8) on d = 10293, 15565: still [1,1,0,[]] (no point listed).
- cover_point.py (ell2cover + hyperellratpoints, nontrivial images only): d = 165 fine; 10293, 15565
  no point up to height 10^6 (85 s each): generators too large for 2-covers.
- Final tyzcl_check: ok = (T5bCl=1, rootno=-1, anrank=1, #tors=4, ellrank lower ≥ 1); explicit point
  reported separately (ellrank, else 2-cover search to 10^5). Rerun started.
- Draft note docs/research/cr3-trust.md written (RESULT_A6 placeholder).

## Step 6 (final)
- tyzcl_check final: 0 failures (T5bCl=1, rootno -1, anrank 1, ellrank [1,1] on 30/30); explicit
  non-torsion point on 24/30 (23 ellrank, 1 ell2cover); none found for 10293, 15565, 18309, 21909,
  26285, 27213.
- Note completed (A6 filled, summary step counts 26); docstring code blocks max 99 chars.
- .fleet/cr3-trust.md written.
