# rv-nt-tyz log

## Step 0 (setup)
- No earlier log; fresh start from f927237.
- Downloaded arXiv:1411.4728v1 e-print independently; sha256 b295b160...fed2 matches nt-tyz's. Single file Period7.tex.

## Step 1 (source reading; Period7.tex)
Checked statements quoted in nt-tyz 1.2 against the source:
- Thm 1.1 (L371-380), Thm 1.2 (L389-409) incl. final sentence "non-ordered with all d_i>1": CORRECT quotation.
- Recursion (L1320-1327): d_1>1 explicit; eps "as in Theorem GZ": CORRECT.
- Thm 3.3 eps-classification (+-i iff (5,3)): CORRECT quotation.
- Prop 3.4 statement silent on ordering / d_1=1: CORRECT. Proof L2024-2105: sketch; "contribution by d0=d0''=n, d1=1 is Z(n)" at L2076-77 (one line off): CORRECT.
- Thm 3.5 (L1353-1374) lacks the "d_i>1" sentence: CORRECT. First assertion proof L2343-2380 read.
- Lemma 2.8 (L1062), L(1)=1 (L1082), Prop 2.3 (L580): CORRECT quotations. Lemma 2.8 normalisation: 2^{k-a}w_K vs 2^{h2-delta}: equal for m=1,3 mod 8 except m=3 (w_K=3, odd factor) -- harmless mod 2.
- Lemma 3.16, 3.18, 3.21 statements: CORRECT quotations. beta'_j any lifting to Gal(Qbar/Q).
- Def of calL(n), calP(n)=0 if calL(n)=0 (L1295): CORRECT.

Hand derivations:
- Lemma N1 (both cases m=1, m=3 mod 8): CORRECT (counts 2^{b-1}-1 and 2^{|S|}-1 re-derived).
- Lemma N2: CORRECT. Chain unwinding, class bookkeeping (q_j in {1,3} forced), eps=i exactly on 7->5 steps, bijection with (partition, ordered admissible grouping), involution for s>=2, Fubini parity. Observed: result does not depend on the eps-class of (5,3) steps at all (they only occur when s>=2, which cancels).
- Prop N proof: CORRECT given I1-I7. Observations: F4 is not needed (l_e integers; X only needs X^{beta'}+X in A(H'_n)); second half of F3 (negation of sqrt(-n)) not needed.
- F3: CORRECT (redone with product formula). F5: CORRECT (generalized dihedral => subfields of ring class field over K are Galois over Q).
- Readings: found a 4th literal reading D (d_1=1 admitted AND d_1 distinguished among class-1 factors) giving T5a + Sum k w + T5b; nt-tyz's A must be understood as "set partitions counted once" semantics. To check numerically on the counterexamples.

## Step 2 (counterexamples of nt-tyz 1.4; own code genus.py, counterexamples.py, rank_lower.py)
- Factorisations 26565 = 3*5*7*11*23, 33117 = 3*7*19*83, both = 5 mod 8: CORRECT.
- g(d) on all 31 resp. 15 divisors by three methods (reduced forms h/#ambiguous, Redei 4-rank, PARI quadclassunit): all agree. g(n)=1 for both.
- Sums: T5a = T5b = 0; second sum A = 0, B = 1, C = 1, and also reading D (d_1=1 admitted, d_1 distinguished) = 1. CORRECT (and D refuted too).
- Rank: points found by ellrank (different from nt-tyz's points), checked exactly on curve; Kummer images of T1,T2,P1..P3 span dim 5 => rank >= 3 (exact). Regulators 39.4026, 269.7036 (match nt-tyz). Root number -1. So ord >= 3 by GZK, calL(n)=0. CORRECT.
- Conclusion: claim (a) holds: Theorem 1.2 under readings B, C (and D) is false; only the set-partition reading A survives these tests.

## Step 3 (coefficients of the genus point; own code coeff_recompute.py, coeff_real.py)
- 360 abstract configurations (40 each for r = 1..9 primes; random classes with product 5 mod 8, random g on subsets).
  L(q) computed from the Lemma 2.8 recursion mod 2 (not from Lambda); P(D) from the section 3.1 recursion in F_2[i].
  20440 coefficients c_n(e) compared: 0 mismatches with Lambda(n/e) (Lemma N2), 0 non-real, 0 Lemma N1 mismatches
  (L(q) vs Lambda(q) on all q), brackets (C1, C2) = (T5a, T5b) in all 360 trials; T5b odd in 136 trials.
- Reading D of Prop 3.4 (d1 = 1 admitted, distinguished) disagrees on 10023 coefficients (298 trials): Prop 3.4 must be read with set-partition semantics.
- Mutation tests (90 trials each): eps(5,3) class = 1 instead of i: still 0 mismatches (confirms the hand observation that the (5,3) class is irrelevant); eps = i on (5,1) or (7,3) steps: thousands of mismatches (test is sensitive).
- 30 actual n = 5 mod 8 (3..7 primes, n < 3e6) with g from reduced forms: 152 coefficients, 0 mismatches; T5b odd for 14.
- Verdict: Lemma N2 / N1 CORRECT, numerically corroborated.

## Step 4 (section 5.1, Kriz; own code cr3_sample.py, propN_diff.py)
- Logical chain of nt-tyz 5.1 checked against CertifiedRank.lean and tyz-5b (Cor 1.2, Thm 3.6, Thm 4.3, Cor 4.4):
  Lean hypotheses (d = 5 mod 8 squarefree, a | d squarefree, |a| = 7 mod 8, 8 solutions, a first coordinate)
  give, via Proposition 0 (descent-alt 4.1; NOT re-checked here), dim Sel2 = 3 and a in pi_1(Sel2). |a| = 7 mod 8
  implies |a|_odd = 3 mod 4, so Cor 4.4 applies to every such d. Cor 4.4 -> Thm 4.3 (Lemma 4.1 + bordered det),
  Thm 3.6, Cor 1.2 (Prop N + GZK + RK9). No step uses Kriz, Cassels-Tate or Smith: CORRECT (logic).
  Not re-proved here: tyz-5b Thms 3.6, 4.3, Lemma 4.1, Prop 0 (UNCHECKED by this review, but see test below).
- Independent test (own full 2-descent via local Kummer images, sanity-checked against ellrank on 9 curves incl. both
  counterexamples): 30 random CR3-admissible (d, a), d < 2e6 (2-5 primes): T5b(d) = 1 in all 30. Two of them
  (226733, 265341): PARI finds a generator and a point with x/a a square (CR3 conclusion end to end).
  A separate check of 20 admissible d with 4-5 primes: T5b = 1 in all 20.
- Differential test of Prop N: 30 random n = 5 mod 8, n < 2e5, >= 3 primes: 24 have T5a or T5b odd, all of
  analytic rank 1 (numerical); 0 contradictions.

## Step 5 (loose ends)
- n = 7 remark of nt-tyz 4.4 (c_n(e) = i Lambda(n/e) for e = 5, Lambda(n/e) for e = 7): hand check (7->5 step carries i,
  s = 1 for e = 5) and coeff_n7.py: 120 configs, 3825 coefficients, 0 mismatches. CORRECT.
- TYZ Lemma 2.8 normalisation at m = 3: Thm 2.1 gives P(3,1) = +-2^{k-a} w_K L(3) L(1) = +-3 L(3) with w_K = 3, and
  Q(3) = P(3,1) (one genus character), so Lemma 2.8's "sum eps L L = Q" reads +-L(3) = +-3 L(3): literally off by the odd
  factor w_K = 3 (true: w_K * sum = Q). calL(1)^2 = calL(3)^2 = 1 numerically (calL_small.py). Harmless for Lemma N1 (mod 2),
  but I2 as quoted ("= Q(m)") is inaccurate for m = 3: MINOR.
- F6 (the "i.e." of Thm 3.5(2)): the direction needed for Thm 1.2 (2^{-rho}L even => P(n) in A(K_n)^- + A[4]) is immediate
  from Thm 3.5 first assertion + Lemma 3.18 (P(n) - m alpha_n torsion, m = 2^{-1-rho} L). So reading A of Thm 1.2 for
  n = 5 is fully proved by nt-tyz 4.4's argument plus F3 (both halves) -- strengthens nt-tyz.
- Line refs: "L2077" is L2076-2077; harmless.
