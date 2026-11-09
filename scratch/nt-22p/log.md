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

## Step 1: key observation (the witness a absorbs poles at old primes)
- PC (Pole.lean:62) needs only: B.den square, 0<B<1/2, v_p(B)>=4 for p in S0={2,3,5,7,13}.
- Slope predicate (ms 1177-1182): a = 1 - R0 q^2 with q a free witness, R = l0^2 a^2 R0.
  a only changes valuations by even amounts, so soundness is untouched.
- If t=u/v has a pole of order e at old prime l (l^e || v, all u-c'v units at l), then
  R0 = eta v^2 F(u,v)/(u-v)^8 and F(u,v)/u^6 = prod(1 - c v/u) == 1 mod l^e, so for eta=+1
  (F(t)>0) R0 is a square in Q_l (l odd, e>=1; l=2, e>=3). Choose q ~ R0^{-1/2} l-adically
  (weak approximation) => v_l(a) = alpha arbitrary. Then v(RC^2) >= 2E+2alpha-2e(k-2),
  W_g == 1, Theta == 12, v_l(B) = v(R) - 2 v(12) >= 4. (SPECULATIVE until written out; local
  algebra checked by hand.)
- Consequence: the bounded-valuation condition on the common difference v (R4's obstacle) can be
  dropped; 22P2 without the v-condition, with u-v and u-(A+9)v also prime, is a homothetic copy
  of a 14-point set in G = good primes => follows from Green-Tao 2008 Thm 1.2 once G has positive
  relative upper density (CM + Hecke/sieve, unconditional).
- rs-pattern 2.3 claimed this condition unavoidable ("fixed l0 and c_* cannot compensate"); it did
  not consider the witness q.

## Step 2: computations
- scratch/nt-22p/density.py: all primes 11..3e6. Point-count GoodSlopePrime = CM description on
  all primes < 2e5 (1925 good, matches rs-pattern). Good primes: 10.64% of primes, 85.04% of the
  class p=1(8),(7/p)=-1; Euler product prod_{l=1(4)}(1-2/(l-1)^2) = 0.8482. VERIFIED.
- scratch/nt-22p/atrick.py: 30 random (u,v) with v_l(v) up to 40 at l in S0, u-cv, u-v units:
  R0 square in Q_l at all l in S0 in 30/30; explicit q (CRT + auxiliary prime 1009, as in
  weak_approx_q) with v_l(1-R0 q^2) >= 25 e_l + 10 at all l in S0 and |a| < 1e-300: 30/30.
  Control: v_2(v) <= 2 gives non-squares in Q_2 (22 of the valid samples) -> those cases use the
  old bounded-valuation argument (e <= 2 <= B_2).
- Literature (arXiv abstracts only; other hosts unreachable): Green-Tao math/0404188 (Szemeredi
  in primes via transference), Tao-Ziegler math/0610050 (polynomial progressions, P_i(0)=0,
  m <= x^eps: no valuation control), 2408.17441 (constellations with Artin-symbol restrictions,
  unconditional; primitive roots under GRH), 1509.04955 (narrow progressions), 1305.5440
  (Conlon-Fox-Zhao relative Szemeredi). No theorem with valuation-restricted differences found.
