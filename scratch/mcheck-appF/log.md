# mcheck-appF log

- Start. Target range from appendix map (docs/research/mcheck-rc-app.md, "largest own steps" item 1): tex L8408-9405
  (ex:app-theta-form statement and proof, ex:app-theta-comparison statement and proof). Setup read: L8206-8407.
- Read L8206-9445 in full (setup, target, (O.8)) and the uses: L2072-2090, L2440-2560 ((3.7), (3.8)), L2585-2590, L10176-10200.
- First pass: no false step found. Plan: s1 (local/constant checks), s2 (Weil index, Hilbert symbols, operator relations),
  s3 (global weighted toy theta on B_{3,inf}: recurrence + (O.7) analog), s4 (root-number sign bookkeeping behind alpha(-1)=1).
- s1_local.py: 48/48 PASS (12 negative controls fail as they should). First version's neighbour brute force at p^3 was too slow; reduced to y mod p^2 (sufficient). One trivial negative control replaced by a real one (AL conjugation of diag(1,-1)).
- s2_weil.py: 20/20 PASS (6 negative controls fail). Weil index computed as Gauss-integral phase with psi_p = exp(-2 pi i {t}_p); product formula holds in this convention and fails in the opposite one.
