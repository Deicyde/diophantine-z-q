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

## Step 2: I1 (recursion + ε of Thm 3.3) and I3 (Thm 3.5 first assertion) read (L1163–1376, L1860–2023, L2343–2380)
- Thm 3.3 first part (non-torsion only for χ_{d0,d1}): Lemma 3.8 (char') + Tunnell–Saito root-number condition +
  K_2^×-invariance of f_n "up to torsion" (Prop 3.1). Lemma 3.8 case analysis checked: n≡5 → (5,1),(7,3); n≡7 → (7,1),(5,3);
  n≡6 → (6,1),(7,2). Note: for n≡5, the class (5,3) never occurs as (d0,d1) with d0d1=n; it occurs inside P(D), D≡7 | n.
- ε-class: Lemma 3.9 (multiples1): 4P(d0,d1) ∈ A(Q(√-d0))^- unless (5,3), where ∈ A(Q(√d0))^- = [i]A(Q(√-d0))^-.
  Checked: fields K_{d0,d1}, actions of c, τ, cτ; [i]P Galois-equivariance computed by hand. χ(σ_ϖ) = -1 ⟺ d1≡3 (n≡7). ✓
  Typo: d1=1 case says "(4P)^c = 4P" — should be -4P (from (2P)^c = -2P [+|Cl|τ(1)]); conclusion A(K_n)^- correct. NEW minor.
  Then proportionality (GZ + Kolyvagin: E(K_{d0})^- rank 1 when L'≠0) + equal heights → ε = ±1 resp. ±i. ✓ (given Thm 3.6, Prop 3.2(4)).
- Exact constant 2^{h2(n)}𝓛(d1): proof is "computations similar to that in the proof of Theorem 2.1" (L~2015) — the
  explicit Gross–Zagier bookkeeping is NOT printed. Reduction to ĥ(R_χ)=L'(E_{K_n},χ,1)/(2^{2k-2h2-2-a}Ω_{d0}Ω_{d1}) checked by
  hand (needs ĥ(β_{d0}) = R_{d0}/2, consistent with "R_n = twice NT height"). NEW finding (gap in exposition).
- I3 proof: Σ_χ P_χ = 2^{h2} Z(n) (character formula, Φ0 = Φ∩2Cl'), then Thm 3.3 termwise; induction. Correct given Thm 3.3.
  Implicit: ε(n,1)=1 (sign of α_n) and 𝓛(1)=1.
- Robustness (VERIFIED by argument): if Thm 3.3 held with 𝒫(d0) replaced by λ(d0)𝒫(d0) (λ any nonzero rational depending
  on d0 only), the same recursion represents λ(n)𝒫(n); Prop N unchanged. So Prop N is insensitive to the ρ-normalisation
  of 𝒫 and to the uniform 2^{h2(n)}; it needs the d1-factor to be (2-adic unit)·𝓛(d1) with the stated ε-class.
  The d1-dependence of the constant is the same 2-power bookkeeping as Thm 2.1 (tested numerically via I2).
- ε when 𝓛(d1)𝒫(d0)=0: undetermined by Thm 3.3; any choice in the stated class keeps I3 (P(d0) torsion then). OK.

## Step 3: I4 read (Lemmas 3.16–3.18, L2167–2342)
- Lemma 3.16: CM description F^×\F̂^× ≅ (1+(1+i)^3Ô_F)^× (h_F=1, units cover (O/(1+i)^3)^×) ✓; F(A[4]) = fixed field of
  (1+4Ô_F)^×, quotient of order 2 → Q(ζ8) ✓ (they call it "ring class field", it is the ray class field mod 4 — wording only).
  A(Q(i)) torsion (ranks of A, A_{-1} over Q are 0); stabiliser of x∈A[4]\A[(1+i)^3] is 1+4Ô ✓; odd part by Step-1 argument (omitted, valid).
- Lemma 3.18 Step 1 (odd p): e_p(ℍ'_n/Q) ≤ 2 since ℍ'_n/L_n(i) is abelian (L_n(i) ⊇ all K_{d0}) and unramified outside 2,
  L_n(i) multiquadratic tame; F(x)/F totally ramified at ℘ with e = N℘-1 ≥ 4. ✓
- Step 2: p ≡ 3 mod 8 inert in every K_{d0} (d0≡5,6); (d0/p)=1 from (a)(b)(c) checked for d0≡5 (even # of 3-mod-4 primes)
  and d0≡6 ((2/p)=-1 times (m/p)=-1). p splits totally in H_{d0,4} (idele p ~ unit ideles) ✓. A(F_{p²}) = A[p+1] ≅ (Z/(p+1))²,
  2-part (Z/4)² = 16 ✓. Reduction injective on 2-power torsion ✓.
- Step 3 (√2 ∉ ℍ'_n, n odd): Q2(√-d0) = Q2(√-5) as subfields (d0/5 ≡ 1 mod 8); 1+2ϖ_{d0} ≡ 1+2ϖ_5 mod 4O (u odd) ✓;
  M_{5,4} = N_{5,4}(√2) ramified over N_{5,4} (generated by a unit) ✓; L_n(i)_v = Q2(i)·unramified ✓. Case with no d0≡5:
  ℍ'_n = L_n(i), conductor of Q(√2) is 8 ∤ 4n ✓. Imprecision only: local "ring class field" depends on a uniformiser,
  harmless (everything is up to unramified extensions). Verdict: proof complete and correct as far as checked.

## Step 4: I5 read (Lemma 3.21, L2489–2560), reduction to Thm 3.6
- Fixed field of 2Cl'_n in H'_n is L_n (n≡5): σ=σ_ϖ² ∈ 2Cl'_n ✓.
- β_j vs σ_ϖ∘c on L_n(i), n≡5: σ_ϖ|_{Q^ab} = r_2(N ϖ) = r_2(n+1); u=(n+1)/(-2) ≡ 1 mod 4 and all quadratic subfields of
  L_n(i) have 2-conductor | 4 → same action ✓; β_2: 6/(-2) = -3 ≡ 1 mod 4 ✓.
- α = σ_ϖ c β'^{-1} ∈ Gal(H'_n/K_n) needs H'_n/Q Galois (= nt-tyz F5 via Prop 3.2(1)); α trivial on L_n(i) → α∈2Cl'_n ✓;
  Z^α - Z ∈ Zτ(1) from z^σ = z+τ(1) (Thm 3.6(1)) ✓.
- "checked easily by Theorem 3.6" (not printed) — re-done here for (1): c inverts Cl'_n (H'_n ⊂ H_{n,4}, dihedral),
  c(Z) ≡ -Z + gτ(1); σ_ϖ: z ↦ z+τ((1+i)/2), t∈Φ0⊂2Cl' fixes i∈L_n, so Z^{σ_ϖ c}+Z ≡ -gτ((1+i)/2) ≡ gτ((1-i)/2) mod Zτ(1) ✓
  (either composition order). For (4): Φ0=2Cl_n, Thm 3.6(3) conj gives (z^{σ_{ϖ^5}})‾ = τ(1/2) - z → Z^{..}+Z = gτ(1/2) ✓.
- Minor imprecisions: (i) "Z^{β1'+1} = Z^{β2'+1}" in (1) is only shown mod Zτ(1) (only membership is used);
  (ii) for n≡7 "β_j acts on L_n(i) as σ_ϖ∘c" holds on L_n for every ϖ (what is used), on L_n(i) only for ϖ with unit part ≡ -1 mod 4. NEW, harmless.
- So I5 ⇐ Thm 3.6(1),(3) + Prop 3.2(1) (Galois/dihedral structure). Next: read Thm 3.6 / Prop 3.2 proofs (L1433–1860).
