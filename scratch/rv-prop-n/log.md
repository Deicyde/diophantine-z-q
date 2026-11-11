# rv-prop-n log

Scope: second review of nt-tyz §4 (Prop N, I1-I7, Lemmas N1, N2, proof 4.4) and F1, F2 (§2.2).
rv-nt-tyz.md NOT read until own verdicts are written.

## Step 1. Read nt-tyz §§1-4, Lean statements
- Lean: CertifiedRankTYZRk: d%8=5, Squarefree d, T5b d = 1 -> point of infinite order on y^2=x^3-d^2x.
  CertifiedRankTYZClRk: same with T5bCl d = 1, T5bCl = sum over set partitions (one block ≡7, one ≡3,
  rest ≡1 mod 8) of prod gCl(d_B), gCl(m) = #(Cl(O_{Q(sqrt -m)})^2) (squares subgroup).
  T5b: same with Rédei bits gBit (Legendre bits a_ij, y_i=[p≡3 mod 4], z_i=[p≡±3 mod 8]).
- Prop N conclusion used: T_5b(n) odd => ord_{s=1} L(E_n,s) = 1; then GZ gives rank>=1 (outside Prop N).

## Step 2. PARI sanity for I4 (torsion_A.py)
- A: 2y^2=x^3+x ~ Y^2=X^3+4X (cond 32). Tors over Q: Z/4; over Q(i): Z/4 x Z/2 (order 8 = #Z[i]/(1+i)^3);
  over Q(zeta8)=Q(sqrt2,i): Z/4 x Z/4 = A[4]; over Q(sqrt2), Q(sqrt-2): Z/4. Consistent with Lemma 3.16.
- 2*A[(1+i)^3] = A[1+i] = {0, tau(1)} (tau: C/(1+i)Z[i]), checked by hand.

## Step 3. Own abstract check of N1, N2, brackets (abstract_check.py, seed 7)
- Model: abstract primes with classes, random g; L(m), m≡1,3, defined from I2 used ONLY mod 2 (random signs,
  random even error in Q and in L: "congruence only"); c_n(e) unwound exactly in Z[i] with random units
  eps (±i iff (d0,d1)≡(5,3)) and random integer lifts of L.
- 453 trials, r = 1..9 primes: 0 mismatches for L≡Lambda (N1), c_n(e)≡Lambda(n/e) with Im≡0 (N2),
  a≡T5a, N≡T5b. (T5a,T5b) distribution {(0,0):166,(1,0):140,(0,1):72,(1,1):75}.
- Teeth: the distinguished-d0 reading sum b(pi)w(pi) differs from Lambda in 184/453 trials.
- Hand check of 4.4: P(n)^{β'} = Σ ℓ_e Z(e)^{β'} + 2X^{β'} uses only additivity of β' (ℓ_e ∈ {0,1});
  F4 ([i] commutes with β') is NOT needed in §4.4 (Z[i]-coefficients are absorbed in X).

## Step 4. PARI ground truth, run 1 (tyzlib.py, ground_truth.py -> out_run1.txt)
- tyzlib: g(d) = [all cyclic factors of Cl(Q(sqrt -d)) have v2 <= 1] (= parity of #Cl^2), field disc -d or -4d,
  quadclassunit (GRH-conditional for large D; cross-checked against Rédei bits implemented as Lean redeiG:
  agreement on every sample). T5a, T5b = set-partition sums (Lean Admissible5bNat for T5b).
- Selection (not ground truth): select_rank3.py seed 11, 600 random squarefree n≡5, >=3 primes, in [3000,2e5],
  kept ellrank upper bound >=3 (no look at T5a/T5b): 10 values. select_genus.py: products of 5-6 primes with
  >=2 primes ≡3 and >=1 ≡7 mod 8 (forces chains with (5,3)-steps), sorted by (T5a,T5b).
- Run 1, 30 inputs: 10 Selmer>=3 candidates (7 have analytic rank 3: 99645, 60229, 92045, 134805, 41181,
  23709, 26565; all T5a=T5b=0, as Prop N predicts); 12 with T5b odd (5-6 primes, incl. 285285, 2535645,
  2028117): all analytic rank 1; 3 with only T5a odd: rank 1; 5 with T5a=T5b=0: rank 1 (no prediction).
  Violations: 0. Rédei/class-group agreement: 30/30.

## Step 5. PARI ground truth, run 2 (21 inputs, out_run2.txt)
- Selection: select_rank3b.py (products of k=4..7 small primes, >=1 prime ≡7 and >=1 ≡3 mod 8, ellrank upper
  bound >=3; seeds 21-24) and select_genus.py k=7 seed 25.
- Results: 15 values of analytic rank 3 with 4-7 primes (e.g. 2817661 = 7·11·23·37·43, 13498485 = 7 primes):
  all T5a = T5b = 0. T5b odd with 7 primes (4849845, 12777765, 10975965): analytic rank 1. T5a odd only
  (13803405): rank 1. 1101565, 1564437 (Selmer bound 3, an. rank 1): T5a=T5b=0. Violations 0; Rédei = class
  group on 21/21.
- Totals runs 1-2: 51 inputs, 22 of analytic rank 3 (all T5a=T5b=0), 15 with T5b odd (all rank 1),
  4 with only T5a odd (all rank 1). [corrected in step 8: earlier count 21/5 was a miscount]

## Step 6. Alternative readings on the 22 rank-3 values (alt_readings.py, out_alt.txt; no new L-runs)
- g(n)=1 for 7 of them: 134805, 26565, 141141, 887565, 2379405, 2422245, 13498485.
- So (a) reading B (T5a+g(n)+T5b even) fails on 7 values (nt-tyz had 26565, 33117); (b) a recursion with an
  even coefficient in place of L(d1) (which would give c_n(e)≡0 for e≠n, i.e. "rank>=2 => g(n) even") is
  refuted: indirect numerical support that the quoted recursion coefficient is L(d1) without a factor 2.

## Step 7. Sensitivity of Lemma N2 to the eps-classification (abstract_eps_variants.py, seed 3, r<=7, 420 trials)
- IPAIRS = set of class pairs (d0,d1) with eps ≡ i (mod 2):
  {(5,3)} (TYZ Thm 3.3): 0 mismatches;  {} (all eps ≡ 1): 0 mismatches;
  {(7,3)}: 1929; {(5,3),(7,3)}: 1929; {(5,1)}: 3007; {(7,1)}: 1100 mismatches.
- So N2 needs eps ≡ ±1 at (5,1), (7,1), (7,3), and is insensitive to eps at (5,3) (the s>=2 terms cancel by
  the involution whatever their weight). The only part of I1's eps-input actually used is "eps(d0,d1) = ±1
  unless (d0,d1) ≡ (5,3)".

## Step 8. Own verdicts written (docs/research/rv-prop-n.md §§1-6), before reading rv-nt-tyz
- Verdict: Prop N holds as stated relative to quoted I1-I7; corrections: F4 unused in §4.4; single β' serving
  all ℍ'_e should be stated; ℍ'_{d0} ⊂ ℍ'_n is quoted; state which eps-info is used.
