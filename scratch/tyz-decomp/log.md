# tyz-decomp results log

## 2026-11-13 (run 1)
- 04:40 start; merged origin/main (2dd83306) into wip/tyz-decomp (merge commit b2a5abc0).
- ~/tyz-src/Period7.tex is NOT on this host (VERIFIED: ls fails). All TYZ line numbers below are
  quoted from nt-tyz.md / pn-design.md / rv-*.md, where earlier tasks read them in Period7.tex;
  every locator not found there is marked UNVERIFIED.
- Journal locators (Asian J. Math. 21 (2017)): only those printed in docs/research/locators.md
  (AI audit, 2026-11-12): Thm 1.4 (= arXiv Thm 1.2) pp. 723-724; Thm 3.5(2) p. 740; proof of
  Prop 3.4 pp. 751-753; final odd-n step p. 760; Lemma 2.9 same number. Not re-read here.
- Finding F0 (VERIFIED, Lean, already in repo): ZInQ.Contrib.PSide.tyzInputs_iff_readingA_of_hecke:
  HeckeContinuation -> (PropN.TYZInputs <-> TYZThm35ReadingA). So TYZInputs, whose L and GenusData
  are existential, adds no trust reduction over reading A itself.
- PARI/cypari2 is not installed on this host and installing it needs the network (forbidden):
  no new numerics. The normalization of lcalSq (2^{2k-3}, Omega_m = (2/sqrt m) int_1^oo dx/sqrt(x^3-x))
  is copied from scratch/rv-tyz-inputs/tyzcalc.py (transcribed there from TYZ L338-353), where
  ~200 values were VERIFIED to be integer squares and Lemma 2.9 mod 2 / Thm 1.1 (Lam reading) held on
  30 m (rv-tyz-inputs log step 8); calL_small.py gives value 1 at m = 1, 3, 11, 19, 33.
- 05:20 scratch/tyz-decomp/TYZDecomp.lean COMPILES (lake env lean, no errors), all 10 #print axioms
  = [propext, Classical.choice, Quot.sound]. Declarations (namespace ZInQ.Contrib.TYZDecomp):
  defs S51B S51C Thm35Reading Thm35ReadingA/B/C omegaInt omegaTYZ lValOne lcalSq IsTYZLcal
  leaves TYZThm11Integral TYZLcalOne TYZLemma29Mod2 TYZThm11Mod2 TYZGenusPackage;
  theorems readingA_iff, not_reading_of, lValOne_eq, isTYZLcal_lcalChoice, lemma29Mod2_of_thm11Mod2,
  tyzInputs_of_leaves, tyzThm35ReadingA_of_leaves(+'), genusData_nonempty_iff,
  genusPackage_iff_readingA (given TYZThm11Integral, TYZLcalOne, TYZLemma29Mod2:
  TYZGenusPackage <-> TYZThm35ReadingA; Hecke discharged by ZInQ.Contrib.heckeContinuation).
- 05:45 CurveA.lean COMPILES: curveA = shortCurve 4 (y^2 = x^3 + 4x, Q-iso to TYZ's 2y^2 = x^3 + x by
  (x,y) -> (2x,4y)), Qbar, iQ, nonsingular_iPt (proved), iPt ([i]), IsDefinedOver, Qi, leaf
  TYZLemma316 : Prop := forall P, IsDefinedOver Qi P <-> 2 • (P + iPt P) = 0; lemma316_zero.
  Axioms: standard three. (Mathlib's AddCommGroup on points needs DecidableEq Qbar: classical.)
- TYZDecomp.lean: added Thm35ReadingA' (d1 = 1 admitted AND distinguished: (5,1) part T5a + S51C);
  recompiled OK. Review finding: A' is a fourth reading, refuted at n = 26565 by nt-tyz's numbers
  (T5a = T5b = 0, reading-C sum = 1).
- Numeric consistency of TYZLcalOne (by hand, from LMFDB-style constants recalled, UNVERIFIED):
  omegaInt = Gamma(1/4)^2/(2 sqrt(2 pi)) ~ 2.622, Omega_1 = 5.244, L(E_1,1) ~ 0.6555 = Omega_1/8,
  so lcalSq 1 = 8 L / Omega_1 = 1; agrees with calL_small.py (VERIFIED there by PARI).
- 06:40 CurveA.lean extended and COMPILES: slope_iPt, iPt_some, iPt_add ([i] additive on A(Qbar)),
  iHom : PtA →+ PtA, iPt_iPt ([i]^2 = -1). Axioms standard three. (Report §4.2 item 1, first half.)
- 07:30 independent AI review (subagent) of TYZDecomp.lean, CurveA.lean, tyz-decomp.md: no blocker,
  9 findings (provenance of reading A' = rv-nt-tyz reading D; TYZLcalOne justification; stale names;
  Thm 3.5(1) mis-cite; Lemma 3.16 "field" overclaim; conditional non-vacuity; rank >= 3; omegaInt
  integrability only in prose; caveats in §0 table). 1-7, 9 fixed (Thm35ReadingA' renamed
  Thm35ReadingD); TYZDecomp.lean recompiled OK.
