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

## Step 3. Use of the conclusion in N5 (L733-768)
- U1 (L733-737): "the representation is de Rham at l, weights 0,-1" = lemma with K = Q_l,
  F = L'_lambda, r = r_l|G_{Q_l}. Exactly the lemma's conclusion. OK.
- U2 (L739-741): Berger, de Rham => pst. OK (C4, [R]). Simplification available: pst over Q_l is by
  definition a property of r|G_E for some finite E; r|G_F is a summand of V_l(A_F)(x)C_l, which is
  pst by semistable reduction (SGA 7 IX) + C_st (Tsuji 1999) [or Breuil/Coleman-Iovita for abelian
  varieties]. So pst follows without the descent paragraph and without Berger. STANDARD.
- U3 (Pan 1.0.4 hypotheses, statement as quoted in h-a011 §1.1, FM.tex L167-177, L226-233):
  needs pst at p (U2) and distinct HT weights at p: {0,-1} distinct. Pan's convention: eps has
  weight -1 = N5's. OK. Coefficients: Pan has GL_2(Qbar_p); r_5 over C_5 subset Qbar_5. OK.
- U4 (C8, L757-768): r_5 = rho_g (x) psi. psi is a de Rham subrep of Hom(rho_g, r_5): needs rho_g
  de Rham at 5 (C8 supplier, not C3) and r_5 de Rham (lemma). Then psi|I_5 = eps^n x finite
  (Tate/Serre). Weights: with eps of weight -1, rho_g (x) eps^n has weights {w - n : w in wt(rho_g)}.
  * If rho_g is in the Tate/arithmetic normalization (trace of arithmetic Frob_p = a_p,
    det = eps^{k-1} x finite), wt(rho_g) = {0, 1-k}; {-n, 1-k-n} = {0,-1} => (n,k) = (0,2) or
    (1,0); k >= 2 => k = 2, n = 0. This is N5's "k=2 and power zero".
  * Pan fixes Frob_v geometric (h-a011 §1.1). If "comes from a cuspidal eigenform" is read in the
    cohomological normalization (trace of geometric Frob = a_v), wt(rho_g) = {0, k-1}; then
    {-n, k-1-n} = {0,-1} => k = 2, n = 1, not "power zero". Harmless: for k = 2,
    rho^coh = (rho^Tate)^dual = rho^Tate (x) eps^{-1} chi^{-1} (chi = nebentypus), so
    rho^coh (x) eps = rho^Tate (x) finite. Conclusion (k = 2; r_5 = rho_f^Tate (x) finite, absorbed
    into f) unchanged. Repair (wording): fix the normalization of rho_g (or say "power zero after
    normalizing rho_g to weights {0,1-k}").
- Only the multiset {0,-1} at the single embedding of K = Q_5 is used downstream. The lemma's
  per-embedding statement for general K is more than needed.

## Step 4. Own verdict (written before reading rv-h-trust's C3 treatment)
HOLDS AS STATED (mathematically). Repairs are citation/wording only:
- R1: add the one-line restriction step (de Rham over F => over F') or cite it.
- R2: replace [P] sources (Milne notes, Brinon-Conrad notes) by refereed ones
  (Mumford §19-20 or Milne 1986 §15; Fontaine Ast. 223 Exp. III); Scholze locators unverified here.
- R3 (C8, not C3): fix rho_g's normalization before "power zero".
Consequence for H: C3 can move from "[M] single model review" to "[M] two independent model
reviews"; the lemma is a routine consequence of standard p-adic Hodge theory, with an alternative
route (pst directly) that needs neither the descent paragraph nor Berger.
