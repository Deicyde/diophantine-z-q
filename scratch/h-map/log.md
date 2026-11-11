# h-map log

## Step 1. Lean consumers of SixContactMin (VERIFIED by reading source, commit d549dabb)
- SixContactMin (Hypotheses/HeightMin.lean): ∀ u ∈ ℚ \ 𝒞, h(u) ≤ H₆(D)·M_{S_mul}(u)^24, 𝒞={0,-15,-20,-24,-30,-60}.
  H₆(D)=A0=2·10^13·max(1,C_cm,(D^(D E0))^17), D=324!·3^(256·324!^4).
- Consumer 1 (precision / main branch): Assembly/Top/MainBranch.lean ratHeight_le_bound_of_test:
  t with Test(n,κ,t) has M_{S_ht}(t) | κF(n) (test_dvd); H at S_ht (via M_{S_mul}≤M_{S_ht}) gives
  h(t) ≤ A0|κF(n)|^24 = 𝓑(n,κ); then |t-n|<e^{-𝓑} forces t=n (eq_int_of_real_abs_sub_lt_exp_neg_of_height_le).
- Consumer 2 (multiplication soundness): Multiplication/Soundness/ContactSupport.lean slope_height_le:
  slope t with SlopePred has M_{S_mul}(t)^25 | f = n1n2-n3 (local congruence), so h(t) ≤ A_ht|f|^{24/25};
  FiniteBox.finite_box_of_heights: N^2 < 24 A N^{48/25}+10 ⇒ |n_i| < (48A)^13 = T.
  A_ht = H₆(R), R=max(D,H_max,c_*,10^12) ≥ D (monotone).
- Frozen target: ∃ P in 292890231905 vars, totdeg < 2↑↑7, |coeff| < 2↑↑8, defining ℤ in ℚ.

## Step 2. Manuscript Thm 4.1 proof (diophantine_zq.tex l.377-972), structure (VERIFIED by reading)
1. Shimura curve disc 6, level-3 curve Y_3, deg(Y_3→P^1_j) ≤ 324; integral model via Buzzard (V_1(5) aux).
2. Pull back by J(u) = -57600F^2/G^6; normalized cover of P^1_u branched only at 6 contacts, ramif. supp = M_S(u).
3. Fiber field K, [K:Q] ≤ 324!; fiber QM surface A/K, good red. outside S ∪ supp M.
4. Hom field L, [L:Q] ≤ D; CM case (Fowler class number + CM Faltings height + GR isogeny) → C_cm.
5. Non-CM: scalar descent (sign cocycle, Brauer, character β of order ≤ 2R^R M), ρ_ℓ of G_Q, 2-dim r_ℓ,
   de Rham (Scholze), odd; Pan Thm 1.0.4 at ℓ=5 ⇒ modular weight 2, Shimura A_f.
6. Conductor: exponent ≤ E_0 at p ≤ R, ≤ 2 at p>R in supp M, 0 elsewhere ⇒ N ≤ Q M^2 (needs local-global compat.).
7. Faltings Hom ⇒ A ⊂ J_1(N) up to isogeny over L'; Javanpeykar h_F(J_1(N)) ≤ 1.3e7 N^12; GR isogeny ⇒ h_F(A) ≤ Q^17 M^24.
8. Theta/Igusa (Lin–Yang, Pazuki) ⇒ h(j) ≤ 40 h(theta)+22, h(u) ≤ h(j)+74 ⇒ h(u) ≤ 10^13 max(1,h_F(A)).
Exponent 24 = 2 (N ≤ QM^2) × 12 (h_F(J_1(N)) ≪ N^12).

## Step 3. rs-height.md re-checked against current Lean
- Precision constant is an NExpr (Compiler/Precision/CappedTest.lean: NExpr lit/add/mul/max/pow/fact; eA.eval = A0): VERIFIED.
  So use P tolerates any NExpr-computable bound Φ(M) (rs-height §2.2) — change of program + decision proof only.
- Use M: h ≤ A M^e, M^k | f, needs e < k (now k=25, e=24); constant budget log2log2log2 T < 65536 (rs-height §2.3; not re-derived here).
- rs-height routes: R1 (H_min, now DONE in Lean as SixContactMin), R2 Baker very low, R3 per-curve very low, R4 elliptic very low,
  R5 citation swaps (R5.3 CM branch → now h-cm.md), R6 shape freedom, R7 contact set.

## Step 4. h-a011.md, h-v14.md read (summaries + leaf tables)
- Upstream Version 14 (V14 L448-1680) is the current paper proof; frozen 11/5 tex in repo differs.
- V14 leaves: 30 published keys, 1 survey sentence (Calegari ICM), Pan (arXiv v2/JAMS 35 (2022)), 5 supplements
  (direct-p5-modularity, a001-moduli, ly-d6-normalization, b11-integral-model, igusa-theta; unreadable here).
- h-a011: Pan Thm 1.0.4 applied directly, pst via Silverberg–Zarhin 3.5 + Breuil Cor 5.3.4; removes survey + direct-p5 → 4 supplements.
  ly-d6, igusa-theta, a001(form part) reproduced by scratch/h-v14 scripts; b11 (integral model) carries unchecked content.
- Uncited: I2 (μ_σ extends over local abelian schemes, V14 L1459), independence of ℓ (L1462), Faltings Hom (L1552), Stacks inputs of b11.
- Open: GR14 non-circularity (GR14 not on arXiv), Carayol 1987 locator.
