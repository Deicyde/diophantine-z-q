# rv-tyz-inputs log

## Step 0 (setup)
- Read nt-tyz.md (inputs I1–I7 at §4.2), rv-nt-tyz.md, rv-prop-n.md.
- rv-nt-tyz: compared I1–I7 quotations with Period7.tex (all CORRECT, I2 only mod 2 because of w_K=3 at m=3, B1);
  B4: proofs of Thm 3.3, Thm 3.5 first assertion, Lemma 3.18, Lemma 3.21 "read but not re-verified".
- rv-prop-n: inputs "quoted", no source access; checked I4 (Lemma 3.16) by PARI torsion_A.py; numerics §5.

## Step 1: I2 read against source (L496–1162)
- Lemma 2.8 (L1062–1077) proof: (PQ) Σ' P(d1,d2) = 2^{h2} Q(n) (L1001), ordered for n≡1, non-ordered for n≡3;
  symmetry Lemma 2.6 halves the n≡1 sum; then Thm 2.1 P = ±2^{k-a} w_K 𝓛𝓛. Exponents checked by hand:
  n≡1: h2=k, δ=1 → 2^{k-1}; n≡3: h2=k-1, δ=0 → 2^{k-1}; Thm 2.1 gives 2^{k-1}w_K. Match. Printed lemma drops
  w_K (=3 at n=3; =1 for n>3 odd) — agrees with rv-nt-tyz B1. At n=1, h2-δ=-1 (lemma meaningless), 𝓛(1)=1 separate.
- Character count (L993–999) checked: n≡1: 2^k ordered decompositions, all characters distinct
  (d1*d2* = n, so χ_{d1,d2}=χ_{d2,d1}χ_0); n≡3: d1*d2* = -n, χ_{d1,d2}=χ_{d2,d1}, 2^{k-1} characters. Correct.
- Lemma 2.6 (symmetry, n≡1): g0 = ai+bj+(c+√n)k conjugates v/√n to k (checked: v g0 = -n+√n vk = √n g0 k);
  Nrd g0 = 2(n+c√n), n+c√n ≡ 1 mod 4 → (·,-1)_2 = 1; other solutions g0(u+vk), norms u²+v² from Q2(i). Correct.
- Thm 2.1 proof (L929–985): "χ trivial on K_2^× ⟺ d2*≡1 mod 8" is incomplete for n≡3 (K_2=Q2(√5) also contains
  √d2* when d1*≡1). Literal Thm 2.1 false for ordered pairs at n≡3, e.g. P(1,3)=P(3,1)≠0 though d2=3≢1.
  Harmless: χ_{d1,d2}=χ_{d2,d1} at n≡3 and Lemma 2.8 sums non-ordered pairs with the ≡1 factor as d2. NEW minor finding.
  Power of 2: |P|² = 2^{4+c} w² (L1/Ω1)(L2/Ω2) with 𝓛² = L/(2^{2k-2-a}Ω) gives 2^{2k-2} (n odd, c=0) ✓,
  2^{2k} (n even, c=1) ✓.
- Prop 2.3 (L1134–1160): f_n(t) for t∈2Cl equals f_n(s²) (left K^×, right Ô_K^×⊂U_n, centre) → odd; Q ≡ #2Cl = g.
  The oddness uses Thm 2.3/2.4 (f_x ±1-valued). n≡1: K_2=Q2(i), f_n(h²)=f_{(i+j)/2}(h²g) since χ_0(h²g)=χ_0(g)=1. ✓
- Depends on (not re-derived): Thm 2.3/2.4 (§2.2 test vectors), explicit Waldspurger Thm 4.2 (§4, from YZZ),
  Petersson-norm constants, modular degree 2 of X_0(32)→y²=x³−x. A wrong power of 2 here would break integrality
  and the parity identity → numerical test planned (Step N1).
