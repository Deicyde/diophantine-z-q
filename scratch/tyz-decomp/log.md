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
