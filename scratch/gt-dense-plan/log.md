# gt-dense-plan log
- 2026-11-09: started; no prior log. Reading GreenTao/ assembly chain.
- Read GreenTao/*, Primes/*, Extraction, DiagonalNegligibility, RelativeSzemeredi statement. Answer to Q2: GENERAL
  (relativeAPCount_lower_bound_of_linearFormsCondition, RelativeSzemeredi.lean:114, any f with 0 ≤ f ≤ ν).
- Structural issue found: original density is eventual in the modulus, cofinal-prime predicate exposes only ∃M;
  A needs "all large prime moduli" + Bertrand modulus selection + dyadic window lemma (needs Chebyshev upper bound).
- gt-import vendors under ThirdParty/GreenTao with module names Submission.* (lean_lib GreenTaoVendor).
- Mathlib 56a0058 has Chebyshev.theta_le_log4_mul_x, psi_le_primeCounting_mul_log, psi_ge, Bertrand.
- Next: write docs/research/gt-dense.md, commit; then scratch Lean for window lemma + residue pigeonhole.
- Wrote docs/research/gt-dense.md (first full draft). Next: scratch Window.lean.
