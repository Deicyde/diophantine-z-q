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
