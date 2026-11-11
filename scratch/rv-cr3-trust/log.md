# rv-cr3-trust log

Target: docs/research/cr3-trust.md (base of that note: 14b28b23; this worktree: 8b71bfdf).

## Step 0
- Read cr3-trust.md in full (621 lines).

## Step 1: Lean implication graph (read at 8b71bfdf)
- Rank/Statements.lean: CertifiedRankRk:43, TYZRk:59, TYZClRk:72 (same lines as cr3-trust). Conclusion
  `∃ P : (shortCurve (-(d:ℚ)^2)).toAffine.Point, ¬IsOfFinAddOrder P`. VERIFIED by reading.
- certifiedRankTYZ_of_certifiedRankTYZRk' (RankVariants.lean), Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk
  (FourRank.lean:367), certifiedRank5b_of_certifiedRankTYZ (Sec3/TYZ.lean:130),
  certifiedRankTYZCl_of_certifiedRankTYZClRk' all exist with no extra hypotheses.
- FINDING F1 (error in cr3-trust §0.2, Summary 1, §3 TYZClRk docstring): TYZClRk DOES imply TYZ, TYZCl, 5b in Lean:
  TYZClRk -> TYZRk (Redei) -> TYZ (RK9+MW, primed thm) -> 5b (Thm 3.6). The premise #Sel2=8 is a premise of the
  target forms, which only weakens them. So TYZClRk implies all 13 forms (+ DLAdmRk). The sentence
  "Those three are not implied by it in Lean as stated, because of the extra premise #Sel2 = 8" is false;
  so is the draft docstring clause "It implies every other form of CR3 except the three ...".
- FINDING F2 (§0.3 out of date): new variants exist:
  exists_..._of_sixContactMin_certifiedRank5b (Rank5bSec3.lean:51, no 22P) and
  exists_..._of_sixContactMin_certifiedRankDLAdmRk (RankDL.lean:232). cr3-trust §0.3 says DLAdmRk has no
  variant and recommends adding the 5b one; both are done. Line numbers in Rank5bSec3 shifted
  (TYZ 54->64, TYZCl 67->77).
- CertifiedRank5b docstring (Row5b.lean ~195) still cites "Gross–Zagier and Kolyvagin (manuscript Lemma 5.5)";
  CertifiedRankRk docstring lists Kriz first. cr3-trust §4 already lists aligning these (consistent).
- DLAdmRk docstring (RankDL.lean:182) has no trust paragraph of its own; fine (points to DLRk).

## Step 2: KERNEL_PLAN and docstrings vs cr3-trust
- KERNEL_PLAN.md lines 21, 67-70: lead with Kriz, then "TYZ with Gross–Zagier–Kolyvagin (only GZ needed)".
  Lines 153-176 on Rk/Inf/DL forms agree with the Lean files. KERNEL_PLAN does not mention the two new
  variants (5b without 22P; DLAdmRk). Consistent with cr3-trust except emphasis (cr3-trust drafts lead with TYZ).
- Hypotheses/CertifiedRank.lean:29-37 docstring: Kriz first, "Gross–Zagier–Kolyvagin gives rank one".

## Step 3: the analytic-to-algebraic step (D1-D3), by hand
- Root number of C_d^D for fundamental D<0, (D,N)=1, all p|N split: eps(E^D)=eps(E) chi_D(-N) = (-1)(-1)(+1) = +1,
  so the premise L(C_d^D,1) != 0 of D2 is compatible with the sign. STANDARD.
- Heegner hypothesis at 2 with N = 32 d^2: D square mod 4N=128 iff D = 1 mod 8 (odd squares mod 2^k, k>=3).
  For odd p | d (p^2 || N), "p splits" suffices for an ideal n with O/n = Z/N. STANDARD.
- Trace step: complex conjugation acts on the Heegner point y_K by ybar_K = -eps(E) y_K^sigma up to torsion
  (Gross–Zagier 1986 / Gross, "Heegner points on X_0(N)"); with eps=-1, y_K+ybar_K = 2y_K + tors, infinite
  order. cr3-trust D3 states the conclusion but names no locator for this sign relation. Minor repair.
- FINDING F3 (D2 supplier): for ord_{s=1} L(C_d,s)=1 the auxiliary field needs a NONVANISHING CENTRAL VALUE
  L(C_d^K,1) != 0 (twist with sign +1). Murty–Murty 1991 ("Mean values of DERIVATIVES of modular L-series")
  is the derivative theorem (L'(E^D,1) != 0), the input for the analytic-rank-0 case of GZK. It is not the
  supplier for this step (STANDARD from the title and the usual GZK citations; theorem text UNVERIFIED).
  Suppliers that fit: Bump–Friedberg–Hoffstein 1990 (values and derivatives), Waldspurger, or
  Friedberg–Hoffstein, Ann. of Math. 142 (1995) 385-423 (general GL2, prescribed local behaviour; locator from
  memory, UNVERIFIED). Level: N=32d^2 is even and not squarefree; whether BFH 1990's theorem allows that is
  UNVERIFIED; Friedberg–Hoffstein 1995 is stated for general cuspidal GL2 (SPECULATIVE from memory).
- Modularity (D1): needs a nonconstant map X_0(N) -> C_d, not just L(C_d,s) = L(f,s). Shimura,
  Nagoya Math. J. 43 (1971) 199-208 ("elliptic curves with CM as factors of Jacobians of modular function
  fields") gives exactly that; cr3-trust D1 says "Deuring; Shimura" without locator. Minor repair (UNVERIFIED
  locator, STANDARD content). Alternative: C_1 = X_0(32) and C_d is its twist by chi_d.
- Kolyvagin: B9 (TYZ's definition of L(n) uses a generator of E_n(Q)/tors when ord=1, citing CW/Rubin/GZ/K)
  and B4 (Thm 3.3's proof) put Kolyvagin's published papers on the route. cr3-trust says so (D3 end, §3
  drafts "enter only inside TYZ"). Honest. But "Kolyvagin ... not needed for the positive-rank forms" is true
  only of the last step D; the overall route uses Kolyvagin (published, refereed). Wording must keep that.
- Consequence of B9: once L(n) != 0 is meaningful, TYZ's framework already presupposes rank = ord in rank one;
  D is therefore logically redundant given B9 but harmless; it makes the final step independent of Kolyvagin.

## Step 4: independent recheck of A6 (scratch/rv-cr3-trust/indep_check.py)
- Inputs: squarefree d = 5 mod 8, d < 30000, 3..5 primes. T5bCl from its Lean definition (set partitions,
  one block =7, one =3, rest =1 mod 8; product of #Cl^2 mod 2), with exact class numbers by counting reduced
  forms (no PARI) and genus theory #Cl^2 = h / 2^(t-1).
- Outcome: 386 values with T5bCl = 1 (matches cr3-trust's 386 with T5b = 1: consistent with T5bCl_eq_T5b').
- Sample of 30 (L[6::13], disjoint from cr3-trust's sample): dim Sel2 by PARI ell2cover (independent of
  mirror.py; calibrated: d=1 ->2, 5 ->3, 34 ->4, 1254 ->5) = 3 on all 30; ellrootno = -1 on all 30; conductor
  (ellglobalred) = 32 d^2 on all 30. Outputs out_indep_check.txt (first 16, killed by the 10-min cap after
  16885) and out_indep_check_part2.txt (indices 16-29, run with 'noheegner'). failures: 0.
- Heegner field (first 16 values): a fundamental D < 0, D = 1 mod 8, all p | d split, with ellanalyticrank of
  C_d^D equal to 0 (numerical) exists, smallest |D| <= 455. So the premise of D2/D3 is met on these 16
  (numerical in the L-value only).
- Note: Sel2 enters only the non-Rk forms; their derivation from TYZClRk is Lean-proved relative to Lean's
  own Sel2, so the Sel2 definitional match affects how they read, not whether TYZClRk justifies them.

## Step 5: further checks (reading)
- ellrank on d=10293 (one of cr3-trust's 6 pointless curves): output [1,1,0,[]]: lower bound r=1 with NO point
  listed. So on those 6 curves ellrank's "r = 1" is not witnessed by a point (it rests on a parity/Cassels–Tate
  step, i.e. on finiteness assumptions on Sha). cr3-trust A6 says "ellrank gives the bounds [1,1]" for all 30;
  for the 6 it should say that the lower bound is not certified. Minor.
- rv-cr3-rank (A5, E3 supplier) is still not an ancestor of HEAD (origin/wip/rv-cr3-rank aec3b570). Its
  verdict (read via git show): no blocker; 38/38 axioms standard; Point instance = Mathlib's
  instAddCommGroup. A trust statement that cites it should have it merged.
- rv-prop-n §1 also checks gCl = TYZ's g and T5bCl = T_5b by reading -> A1 now has two model reviews, A2 three.
- rv-prop-n §6: I1's inclusion H'_{d0} ⊂ H'_n is a quoted fact; cr3-trust B5 calls B5 "a definition, not a
  theorem" while listing that inclusion in it. Repair: mark the inclusion as a TYZ fact (ARXIV-READ).
- rv-prop-n: one lift β' serves all Z(e) at once; cr3-trust B8 says "any lift β'". Repair wording.
- Group law: cr3-trust A5 does not say why GZ's (classical) non-torsion point is non-torsion for Mathlib's
  Point group. STANDARD: Mathlib's addition is the chord-tangent law (Silverman III.2.3 formulas); and the Inf
  form avoids the group law entirely (Lean-proved equivalence). Add one sentence.
- Form count: with the DLAdmRk variant there are now 14 forms with main-theorem variants (cr3-trust: 13).

## Step 6: Lean run (load 4.7, 135 GB available)
- lake build ZInQKernel.RouteK.RankDL RankVariants Rank5bSec3 RankInf: Build completed successfully (9843 jobs).
- lake env lean scratch/rv-cr3-trust/Check.lean (output out_check_lean.txt): elaborates without error.
  rv_tyz_of_tyzClRk, rv_tyzCl_of_tyzClRk, rv_5b_of_tyzClRk, rv_dlAdm_of_tyzClRk (F1 compositions),
  the two new variants (…certifiedRank5b, …certifiedRankDLAdmRk), …TYZClRk variant and
  certifiedRankTYZClInf_iff_certifiedRankTYZClRk: all [propext, Classical.choice, Quot.sound]. F1 VERIFIED.
