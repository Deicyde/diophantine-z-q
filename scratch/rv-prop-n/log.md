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
