# rv-h-c3 log

## Step 1. Source read (N5 = diophantine_zq.tex in repo root)
- Lemma lem:de-rham-descent: N5 L10939-10992; remark L10994-10997.
- Use: N5 L733-741 (de Rham + weights 0,-1; Berger -> pst), L755-768 (Pan at 5; twist; weights).
- Setup feeding hypothesis: N5 L632-657 (mu_1=1, mu inflated from Gal(L/Q), a_sigma constant),
  L709-712 (L' = kernel field of beta|G_L), L718-731 (rho_l = beta^-1 a_sigma mu_sigma o sigma on
  V_l(A) (x) C_l, rho ~ r+r via matrix units of B (x) C_l = M_2(C_l); on G_L' it is the Tate action).
- Application data: K = Q_l (decomposition group via a fixed embedding Qbar -> Qbar_l),
  F = completion of L' at the induced place, A = base change of A/L to F, C_l as in N5 L719-721.
  On G_L': mu_sigma = mu_1 = 1, a_sigma = 1, beta = 1, so rho_l|G_F = Tate action (x) C_l. Hypothesis of
  the lemma holds exactly.

## Step 2. Step-by-step check of the proof (own review; rv-h-trust C3 section NOT read)
Notation: D_E(W) = (B_dR (x)_{Q_l} W)^{G_E}; W de Rham over E iff dim_E D_E(W) = dim_{Q_l} W.
- P1 (H^1_et(A_Fbar,Q_l) de Rham). Scholze 2013 Cor 1.8 for proper smooth rigid spaces over a
  discretely valued K with perfect residue field: F finite over Q_l qualifies. Algebraic vs analytic
  comparison (Huber; Scholze Thm 9.3 cited) needs l^n invertible on A, true since char F = 0.
  Correct; STANDARD. Overkill: Faltings 1989 / Tsuji 1999 (C_dR for proper smooth schemes) or, for
  abelian varieties, semistable reduction (SGA 7 IX) + C_st give it directly. Locators UNVERIFIED (no
  network; sources not in repo).
- P2 (V_l(A) = H^1^dual, G_F-equivariant). STANDARD (Mumford §19-20 / Milne 1986 §15; N5's Milne
  notes are a [P] source).
- P3 (duals, subquotients). STANDARD (Fontaine Ast. 223 Exp. III; BC Thm 5.2.1 formalism).
- P4 (coefficient extension = finite direct sum over Q_l; r|G_F is a Q_l-direct summand of
  (V (x) C_l)^{[C_l:Q_l]}... precisely V(x)C_l = V^{[C_l:Q_l]} as Q_l[G_F]-module, r|G_F a summand of
  r+r = V(x)C_l). Correct.
- P5 (descent F -> K). F' Galois closure of F over K. Unstated step: W|G_F de Rham => W|G_F' de Rham.
  Proof: F'(x)_F D_F -> D_F' injective (B_dR^{G_F'} = F', linear-independence lemma), so
  dim D_F' >= dim W; the reverse inequality always holds. Then D_F' carries a semilinear Gal(F'/K)
  action (B_dR^{G_F'} = F'), D_F'^{Gal(F'/K)} = D_K, Hilbert 90 / Speiser: F'(x)_K D_K = D_F'.
  Each Fil^i D_F' = (Fil^i B_dR (x) W)^{G_F'} is a Gal(F'/K)-stable F'-subspace, so descends too.
  dim_K D_K = dim W. Correct. (This is the finite case of de Rham being insensitive to finite
  extensions, BC Prop 6.3.8 as cited; Fontaine Ast. 223 Exp. III 3.x; STANDARD.)
- P6 (weights). Fil on H^1_dR(A/F): Fil^0 = all (dim 4), Fil^1 = H^0(A,Omega^1) (dim 2), Fil^2 = 0.
  Convention "Q_l(1) has weight -1" = weight is a jump i with gr^i D_dR != 0
  (D_dR(Q_l(1)) = K t^{-1} (x) e lies in Fil^{-1}, not Fil^0). So H^1_et has weights {0,0,1,1},
  V_l(A) = dual has {0,0,-1,-1}. Per component E of F (x)_{Q_l} C_l (a product of fields), the
  filtration of D_F(V) (x) C_l is Fil^i (x) C_l with Fil^1 free of rank 2 over F, so every component
  sees {0,0,-1,-1}. D(r+r) = D(r)^2 componentwise => D(r) has {0,-1} at every component. Descent
  F'(x)_K Fil^i D_K = Fil^i D_F' gives the same multiset at every component of K (x) C_l.
  Correct. Weights distinct: yes.
- Sanity of convention: elliptic curve, ordinary reduction: 0 -> Q_l(1)(x)unr -> V_l(E) -> unr -> 0,
  weights {-1,0}. Consistent.
- Can any step fail? De Rham-ness over K is a property of W|G_E for any finite E/K (P5); no
  2-dim r with r|G_F de Rham and r not de Rham exists. No counterexample possible; none sought by
  computation (no finite computation bears on P1-P6).
Outcome: proof correct as written; one unstated routine step (restriction F -> F').
