# mcheck-rc-deep2 log

- 2026-11-17 start (fresh; no earlier log). Read docs/research/mcheck-rc-deep.md and scratch/mcheck-rc-deep/.
- Read ex:arith-paired-functional (L3704-3880) with context L2718-2833 (setup, conjugate duality), L3411-3500 ((4.3), (4.4)).
- Paired functional first pass: proof ends at L3875 (\end{proof}); L3877-3880 is ex:arith-coordinate. No false step found. a = 0 is claimed (all comparison maps integral); K enters only through the old places, where K_w = Q_p and the local types come from a fixed finite list. Integrality at (t): moving-prime Frobenius contraction with limit determinant 2 - lim(chi a_r) != 0 (from v2(2 +- a_r) <= c_E); at (t+2): C = t = -2, a unit.
- p1_checks.py 26/26 (first runs: two script bugs, rand_unimod(1) and the cone-contraction sign/degree indexing in P8; fixed, not manuscript issues).
- Residual bound first pass: every count re-derived; no false step. Chain (5.1) has slack 8 at s = v+A+1+j. Genus bound checked on 1217 fields.
- r_checks.py 18/18 (compose() first draft half-written; replaced by Buell united-form composition before the first full run).
- Added P5b (moving prime with B' = 2i: (4.4) gives DC = CA exactly). p1_checks.py 28/28.
- No error verdict, so no .fleet/mcheck-rc-deep2-verdict.md. Gaps filled: P-a (4.4) norm at the moving prime; P-b K missing from the statement of the exponent's independence.
- Unverified: ex:arith-local-kummer proof, ex:arith-moving-character construction, ex:limits-inner-limit, Nekovar/Milne locators.
- Report docs/research/mcheck-rc-deep2.md written; tex line citations re-checked with grep/sed.
