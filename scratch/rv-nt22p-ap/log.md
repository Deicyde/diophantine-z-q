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
