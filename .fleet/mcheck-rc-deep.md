# mcheck-rc-deep (fleet note)

Report: `docs/research/mcheck-rc-deep.md`. Log: `scratch/mcheck-rc-deep/log.md`. Scripts and outputs are
in `scratch/mcheck-rc-deep/`: b1_checks 17/17, b1_transfer 6/6, b1_homotopy 5/5, b2_checks 18/18, all PASS.
The transfer and homotopy scripts each have a negative control, and both controls fail as they should.

**Result: no error, so no verdict file.** These are a step-by-step Manuscript check of Elliot's two largest
pieces of his own work in the proof of Theorem 5.3:

- **Finite Heegner descent** (ex:arith-finite-heegner, tex L2834-3410; the proof ends at L3410, not
  L3393). It holds as written. This is a Kolyvagin derivative computation at p = 2 with one uniform
  multiplier L = m_0 C_pi C_bad 2^{2e}. I checked every computation: e = n+2, the matrix span, (H5),
  (H6), the precision rule (H12), the Frobenius algebra (H13)-(H18), the twisted transfer (H21) in degrees
  0-2, the tame local model, res/cor, and the 3-arrow homotopy identity.
- **Switches and (5.5)** (L4747-5205). This also holds as written, relative to inputs proved elsewhere.
  I checked the following:
  - the switch lemma, with its equal-valuation claim written out;
  - the outer-DVR contradiction, where u = ±αβ/Δ holds for every nonzero maximal minor;
  - the quadratic case at (t) and (t+2) (sign planes, (5.5a), (5.5b), polarization);
  - orthogonality at derivative primes, and Λ[1/2] as an intersection;
  - (5.5) + (4.6) ⇒ (3.5).

**Gaps filled (small, presentation level).**

- B1-a: P_{I,m} needs (H12)-type divisibility at every prime of I, not only the new one.
- B1-b: the twisted split norm relation needs θ trivial on Gal(H_f/H_{f/q}). The use at (4.5) satisfies
  this.
- B2-a: the switch lemma's equal-valuation claim.
- B2-b: β ≥ -a after switches in the (5.5) argument. This is proved only in the regularity paragraph.

**GZ/TYZ.** Neither block uses either one. Block 2 reaches lem:forward-rank (a Kolyvagin print) only
through "central dimension one" in the (4.6) hypotheses.

**Unverified.**

- All print locators: CCL 2.15, Elkik, Nekovář, Lang, Silverman, Howard, Serre.
- Whether the local data meet Nekovář 8.6.2.x.
- The outside inputs to (5.5): (5.1) ex:limits-residual-bound, the inner and outer limit lemmas,
  ex:arith-paired-functional (the exponent a uniform in K, and integrality at (t) and (t+2)), and central
  dimension one.
- The constant C(E,A) is ineffective, which is fine for RC.

**Next.** The checks of most value are ex:arith-paired-functional (L3704-3880) and
ex:limits-residual-bound (5.1) (L4458-4648), because (5.5) rests on both.
