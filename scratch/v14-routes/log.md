# v14-routes log
- Start 2026-11-09. ~/gt-src/v14/quartic_v14.tex is a 127-byte GitHub API 404 JSON, not source.
  Upstream (elliotglazer/diophantine-z-q) unreachable: Go proxy says tree >500MB; raw/jsdelivr/api fail.
  Available: addition.tex (sec:v14, header says it does not modify the polynomial or V13) and quartic_v13.tex.
- Diffed Nov5 vs V13 main body (scratch main.diff) and appendices (app.diff): attribution lines, multiplication
  test text (A_i - sigma(A'_i)) and valuation deduction expanded, RC: Kato 1999 Thm 0.8 at 2, off-filter scope,
  determinant specialization lemma; template dictionary. Thm 4.1, Lemma 5.1, Thm 5.2, 5.3, Prop 6.2 statements unchanged.
- Quartic route (V9-V14): five-contact height (hyp:o8-height, thm:quartic-height19; Shimura disc 210), seven-witness
  pole Psi(b) from RC (x+3l curves), Sun-type simultaneous Gaussian primes (thm:v5-simultaneous-primes). No weaker input.
- openai/math pointwise 2-converse preprint: Go proxy times out (commit ts 20261030003535); not on arXiv. UNCHECKED.
- checks.py: quartic curve/point = main E,P0 under (eps^4 x, eps^6 y), eps=1+s; V14 norms and Q=0 roots verified.
- Height in quartic route: hyp:o8-height (L6854) and thm:quartic-height19 (L8922); H19 uses X_H (nebentypus kernel),
  GR2023 Thm 1.9(1) (not on arXiv), vonKaenel2021, Mascot; Thm 4.1 uses J_1(N), GR2014 Thm 1.4.
- Recommendation decided: GPD/GTD stay first (in flight); next new attack = CertifiedRankSel elementary bridge
  (tyz-5b Sec 4 Lemma 4.1 + Thm 4.3 in Lean, now that Prop 0 is in Lean). Writing docs/research/v14-routes.md.
