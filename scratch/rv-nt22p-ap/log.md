# rv-nt22p-ap log

Step 0: read docs/research/nt-22p.md (all 590 lines) and Hypotheses/PrimePattern.lean.

Step 1 (reading): Lean interface.
- GoodSlope (PatternSlopes.lean:27) field `old` is consumed ONLY in PoleValuations.lean:126 (part1
  of pole_input_valuations); old_le_Cp is unused. So replacing field 2 touches part1 and hq_old only.
- goodSlope_of_primeValues (TwoSlope.lean): fields 1,3,4 use only primality/goodness of the six
  numerators and u-v != 0; `hold` is used only for field 2. CORRECT: fields 3,4 of Prop AP carry over.
- goodSlope_neg_ten is kernel-proved with the old field 2; implies 2' trivially. CORRECT.
- Manuscript 1177-1190: eta, q free per slope (private witnesses); 1733-1735: eta chosen so R0>0.

Step 2 (Green-Tao source): fetched arXiv math/0404188v6 TeX. Theorem counter is [subsection] and
there is no subsection before it, so `sz-primes` is Theorem 1.2: "Let A be any subset of the prime
numbers of positive relative upper density, thus limsup pi(N)^{-1}|A cap [1,N]| > 0 ... Then A
contains infinitely many arithmetic progressions of length k for all k." Degenerate r=0 discarded
(line 1429), progressions genuine integer APs (terms in [eps N, 2 eps N]). CORRECT as quoted.
NOTE: the proof of Thm 1.2 is only sketched in GT08 sec. 10 ("we leave the details to the reader":
pigeonhole a class b mod W). The CFZ exposition arXiv:1403.2957 proves only Thm 1.1 completely and
lists Thm 1.2 under "extensions" (sec. 'Szemeredi's theorem in the primes'). Minor trust-base point.

Step 3 (density, own script scratch/rv-nt22p-ap/density.py, PARI 2.17 via cypari2, own venv):
- literal GoodSlopePrime (both roots r, brute-force affine point count + 1) vs CM description
  (p = 1 mod 8, (7/p) = -1, p = a^2+b^2 with a odd, no odd l | gcd(a, p+1)): all primes
  325 <= p <= 40000: 0 mismatches (450 good primes p < 40000 in total).
- same with PARI ellcard for all p <= 2e5: 0 mismatches, 1925 good primes (matches note);
  good p <= 324: 17, 41, 73, 97, 241, 257, 313.
- primes 11 <= p <= 3e7 (1,857,855 primes): class share 0.12503, good share 0.10610,
  good/class 0.84860; Euler product prod_{l=1(4), l<1e7}(1-2/(l-1)^2) = 0.84820 (x 1/8 = 0.10602).
- By hand: 2-part of gcd is exactly 4 (difference 4a, a odd; full 2-torsion forces trace = 2 mod 4,
  so trace is +-2a with a odd); (7/p)=1 => curves isomorphic (a1/a2 = d1^4/49 a 4th power iff 7 is a
  square, -1 being a square); (7/p) = -1 => quadratic twists, orders p+1-+2a. CORRECT.

Step 4 (Prop AP, own script scratch/rv-nt22p-ap/apcheck.py, exact rationals): for A in [-80,60]
and A in {+-10^6, +-1000, -71..-68}, 3 random samples each (seeds 1 and 2), with v = prod_{l in S0}
l^{e_l} (e_l in 1..30) times a cofactor and x = 1 mod 2*3*5*7*13 (so all terms are S0-units):
- closed form K_A = A'+120 (A' >= -59), 2-A' (A' <= -60); min K_A = 61 (A' = -59). The note's
  "K_A ~ |A| + 71" is wrong (K_A = A+130 for A >= -69, -A-8 for A <= -70); cosmetic.
- every u - c'v (c' in S_A+) is the term of index max S - c' in [0, K_A]: holds.
- t1+t2-10 = A; t1, t2 not in C u {1}; F(t1) > 0, F(t2) > 0, t2 < -60 for every sample,
  including the switch A' = -59/-60 (A = -69/-70): holds. Hand proof: t2 = A' - max S - x/v and
  A' - max S = -60 (A' >= -59) or A' - 1 <= -61 (A' <= -60). CORRECT.
- numerators of t2 - c are -(u - (A'-c)v): holds.
- v_l(t-1) = -e, v_l(R0) = 2e for all l in S0, both slopes: holds.
- whenever e > B_l (3882 + 3896 cases): e >= 2, e >= 5 at l=2, and R0 is a square in Q_l
  (eta = 1): holds in all cases. Lemma P(1) also checked by hand. CORRECT.
- control: l=2, e<=2 gives a non-square in 200/200 (by hand: the c=-15 factor is 3 mod 4 or
  5 mod 8). Moot for AP: all terms are 1 mod 8, so 8 | v always.
- Fields 3,4: TwoSlope.lean proof of fields 3/4 uses only primality/goodness of numerators: CORRECT.
- Lowest terms: CORRECT (common prime divides all K_A+1 >= 62 distinct prime terms).
- PoleCompleteness (Hypotheses/Pole.lean:62) needs v_p(B) >= 4 only on S0 + square den: remark 3
  CORRECT (v_l(B) = 2v(l0) + 2v(a) + 2e - 2v(Theta), even).
- Interface: SlopeRepresentation consumed only via slope_complete (Core.lean:17); field `old` only in
  pole_input_valuations part1. So Prop AP + a modified slope_complete is all that is needed.

Step 5 (trust base): GT08 Thm 1.2 is a special case input; it rests on Szemeredi (finitary, no
bounds), transference, GY correlation estimates; the manuscript route (GT10 + GTZ + MN) is strictly
deeper. Caveats: (a) the main theorem only rests on GoodPrimeAP after Lean work for field 2' (not
done); (b) Prop D is a sketch; (c) GT08 Thm 1.2's proof is sketched in GT08 sec. 10.
