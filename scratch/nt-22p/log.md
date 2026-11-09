# nt-22p log

## Step 0 (start)
- Read rs-pattern.md (all), rs-global.md (F3-F4, A3, A8), PrimePattern.lean, ShiftChoice.lean,
  SlopeCompleteness.lean (exists_shift), manuscript 1123-1300 (slope predicate), 1267-1760
  (Prop 6.2 + proof + application), 225-262, 6310-6350 (M0).
- Q1 first facts (VERIFIED by reading):
  - gcd(d1,d2)=4 used only in `shift_choice` via `exists_shift` (SlopeCompleteness.lean:51-66);
    `tests_precision_selected` needs only d1 | h, d2 | h - c_*.
  - Manuscript handles gcd: odd l | gcd iff l | a and l | p+1 (lines 1592-1598); l <= L excluded
    by the progression (Psi_nu != -1 mod q, lines 1384-1390, 1352-1356); l > L by an elementary
    Gaussian-lattice sieve (1600-1642), bound X/(L log X) + X^{7/8}; combined with fibre count
    (1644-1680) and the order of choices (1682-1704). No GRH. Analogue: Serre cyclicity for CM
    curves (Murty 1983, Cojocaru 2003) which is unconditional.
