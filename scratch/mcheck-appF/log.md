# mcheck-appF log

- Start. Target range from appendix map (docs/research/mcheck-rc-app.md, "largest own steps" item 1): tex L8408-9405
  (ex:app-theta-form statement and proof, ex:app-theta-comparison statement and proof). Setup read: L8206-8407.
- Read L8206-9445 in full (setup, target, (O.8)) and the uses: L2072-2090, L2440-2560 ((3.7), (3.8)), L2585-2590, L10176-10200.
- First pass: no false step found. Plan: s1 (local/constant checks), s2 (Weil index, Hilbert symbols, operator relations),
  s3 (global weighted toy theta on B_{3,inf}: recurrence + (O.7) analog), s4 (root-number sign bookkeeping behind alpha(-1)=1).
- s1_local.py: 48/48 PASS (12 negative controls fail as they should). First version's neighbour brute force at p^3 was too slow; reduced to y mod p^2 (sufficient). One trivial negative control replaced by a real one (AL conjugation of diag(1,-1)).
- s2_weil.py: 20/20 PASS (6 negative controls fail). Weil index computed as Gauss-integral phase with psi_p = exp(-2 pi i {t}_p); product formula holds in this convention and fails in the opposite one.
- s3_toy_theta.py: 27/27 PASS. Global toy on B=(-1,-3) (ell0=3, h=1), h*=-7,-31, P=1: (O.6)-analogue on 1617 (p,n) pairs per case; (O.7)-analogue: support count 12h(F), H(m)=+-12h(F) with all orientation weights equal, H(mD)=0 for D>1 (genus character). Negative controls (s:=1, (n/p), genus char dropped, one ell0-orientation) fail.
- s4_rootnumber.py: 2/2 PASS (root numbers of 11a1, 37a1, 15a1, 14a1 and 8 negative odd twists computed from the L-series; negative control without chi(-1) fails). Next: s5, numerical test of the inverse-idele convention (L8990-9015) on a unary theta with an order-4 character, and of the (m/.) extraction rule.
- s5_convention.py: 4/4 PASS (order-4 character mod 17: classical character is prod alpha_p(d), not the inverse; theta(m tau) carries (m/d)). Writing report.
- Report docs/research/mcheck-appF.md written (conclusion, uses of (O.7), table of 54 rows, known issues). Line numbers re-checked with grep.
- No error verdict: .fleet/mcheck-appF-verdict.md not written. Gaps filled: F-a (Brandt adjointness step), F-b ((-1) = (-1/l0)), F-c (mod 2^M O), F-d (zeta up to sign).
- Unverified: CJ specialization and reduction identity (print offline), Weil III Thm 6 / holomorphy at cusps, double-cover normal form, Hecke/AL/Frobenius compatibility of P_M (standard), Voight/Jetchev-Kane locators.
- Fleet note written. Done.
