# mcheck-rc-deep2: fleet note

Task: a detailed Manuscript check of the two results that the uniform bound (5.5) rests on. The
previous check (mcheck-rc-deep, item D4) left both unchecked. Report: docs/research/mcheck-rc-deep2.md.
Scripts and outputs: scratch/mcheck-rc-deep2/ (p1_checks 28/28 PASS, r_checks 18/18 PASS; every check
has a negative control that fails, as it must). Log: scratch/mcheck-rc-deep2/log.md.

**ex:arith-paired-functional (L3704-3875) holds as written.**
- The exponent is uniform in K; in fact a = 0. K enters only at the places above 2N. There K_w = Q_p,
  and each local diagram comes from a fixed finite list (one per p | 2N and per squareclass type).
- Active and moving places contract integrally over O[G]. The cone of the orthogonal comparison j is
  therefore integrally contractible, and λ_z = PD(-, j^{-1}c(z)) is integral.
- Integrality at (t) and (t+2) holds for the scalar primitive constituent:
  - at active primes, inertia - 1 = -2;
  - at (t+2), the moving inertia - 1 = t ≡ -2;
  - at (t), the Frobenius contraction works because det(1 - Φ_0) = 2 - lim χa_r ≠ 0. This uses
    v_2(2 ± a_r) ≤ c_E from ex:arith-moving-character.

**ex:limits-residual-bound (5.1) (L4453-4648) holds as written.**
- Every count was re-derived: the Kummer and genus count (genus bound checked on 1217 fields), the
  Euler-characteristic and Schreier routes, the local table and the per-prime costs.
- The chain (5.1) holds with slack 8.
- After inverting t, every active block is acyclic.

**Errors: none.** No verdict file was written.

**Gaps filled (small):**
- P-a: the norm N_q(g) in (4.4) is the g² = 1 form, yet it is used at the moving prime. It is still
  valid there, because r ≡ 1 mod 2^{B'} with B' ≥ n_i ≥ 2i.
- P-b: the statement gives a as independent of "the active list and G" but omits K. The proof does
  prove K-independence.

**Unverified:**
- the proofs of ex:arith-local-kummer, ex:arith-moving-character and ex:limits-inner-limit (only their
  use was checked);
- the Nekovář and Milne locators.

**Next most valuable checks:** ex:arith-local-kummer (the integral old-place comparison) and
ex:arith-moving-character (the uniform c_E). Both now carry (5.5) directly.
