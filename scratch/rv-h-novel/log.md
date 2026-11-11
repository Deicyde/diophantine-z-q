# rv-h-novel log

Source: diophantine_zq.tex (N5), sha256 cb1148cd...792b (differs from the Astra-reviewed hash bfc4192d...; Astra line numbers are older).
Scope: N5 L631-716 (scalar descent), L796-857 (system at 3/5, break bound, p=2, N <= QM^2), L860-905 (transfer).

## Step 1: line-by-line reading (no computation)

Notation: A/K fibre, L normal, d=[L:Q]<=D, T=S u supp M, End^0(A_Qbar)=B (disc 6).

S1.1 L634-644 mu_sigma, c(sigma,tau) in Q^x. Checked: mu_tau ^tau b = b mu_tau => applying sigma,
  c commutes with B; centralizer of B in B is Q. OK.
S1.2 L645-664 a_sigma=(deg mu)^(-1/4), eps in {+-1}: a_s a_t/a_st = 1/|c| (deg[c]=c^4, g=2), so
  factor = c/|c|. Normalized since mu_1=1. OK. Under any embedding C->Qbar_l the identity
  a_s a_t/a_st=1/|c| (rational RHS) is preserved, so Qbar_l images of a_sigma are harmless.
S1.3 L668-671 [eps]_p=0 for p notin T: restriction inflated from Gal(Q_p^ur/Q_p)=Zhat, H^2(Zhat,Z/2)=0. OK.
S1.4 L671-678 chi = prod chi_p (odd chi_p mod p, chi_4 at 2), m=ord chi <= lcm <= 2 prod_{p in T odd}(p-1)
  <= 2 prod_{p<=R}(p-1) prod_{p|M}(p-1) <= 2 R^R M. OK (S subset [1,R], primes of M outside S).
S1.5 L680-693 local square-root criterion: Q_p^x = Z x mu_{p-1} x Z_p (p odd), Z x {+-1} x Z_2 (p=2);
  finite-order chars of Z, Z_p are 2-divisible; on cyclic even-order part squares = chars trivial on -1.
  Local component omega_p(-1)=chi_p(-1) (p-part of chi). So delta(chi)_p != 0 iff p in T_-; agrees with
  [eps]_p at all finite p, real place by reciprocity, Hasse injectivity. OK. (computation C2 planned)
S1.6 L693-700 beta=beta_0*gamma, gamma continuous sign cochain (continuous cohomology). beta^2=chi, d beta=eps. OK.
S1.7 L701 beta|G_L homomorphism and G_Q-invariant: eps(g,s)=eps(s',g)=1 for s in G_L gives
  beta(g s g^-1)=beta(s). OK.
S1.8 L702-709 p notin T: I_p subset G_L, beta|I_p^2 = chi|I_p = 1; quadratic chars of I_p (p odd)
  factor through tame inertia prod_{l!=p} Z_l(1): unique nontrivial one. Twist eta = prod Legendre
  symbols mod P (P odd, prime to T): unramified on T (incl. 2), eta^2=1, d eta=1. OK.
  ("possibly at 2" is vacuous.)
S1.9 L711-716 [L':L] | 2m (beta'^{2m}=chi^m=1 on G_L), [L':Q]<=2md<=4DR^RM<=R^{R+2}M<=QM. OK.
S2.1 L770-794 rho_l(s)rho_l(t)=rho_l(st) checked with eps=beta(s)beta(t)/beta(st). OK.
S2.2 L797-818 same system: trace of mu_bar_sigma o Frob on V_l(A_bar_v) is rational, l-independent
  (Mumford AV par.19); arithmetic Frobenius on homology = relative Frobenius on points. OK.
S2.3 L820-834 break bound: delta <= e-1+e v_p(e) (Serre LF III par.6), Hilbert delta=sum(|G_i|-1),
  delta/e = 1-1/e+int_0^inf(1-1/|G^u|)du (phi'=|G_t|/e), integrand>=1/2 below last break ->
  u_last <= 2 delta/e <= 2(1+v_p(e)) <= 2(1+log2(a!)) <= 4a^2. OK. Upper numbering passes to quotients
  (Herbrand) so this is an absolute bound.
S2.4 L836-845 F'=L_v(A[3]) (A[5] if p=3), [F':Q_p]<=D*|GL4(F_5)|; Raynaud n>=3 prime to p; semistable =>
  wild inertia of F' trivial on V_l. Absolute G^u, u>U_0=4(DG_0)^2: in G_{F'} (normal closure) and
  pro-p => in P_{F'}. OK.
S2.5 L846-848 odd p: beta^2=chi tame at p, so beta on pro-p wild inertia has order<=2, trivial. OK.
S2.6 L848-865 p=2: beta^4 = chi_2^2 o N = 1 on U_F (2-part of chi has conductor<=4);
  log: U^{e+1}=m^{e+1} (r>e/(p-1)=e), 4 m^{e+1}=m^{3e+1} => beta trivial on U^{3e+1} => on G_F^u, u>3e
  (LCFT maps G_F^u onto U^{ceil u}). Subgroup formula G^u cap G_F = G_F^{psi_{F/Q2}(u)}: TRUE for all u
  since L_v/Q_2 Galois (H_x=G_x cap H plus transitivity of psi). OK. "If e<=D" should read "Since".
S2.7 L866-867 a(r_l)<=codim r^I + Swan <= 2+2U_0 = 2+8(DG_0)^2 <= E_0=10(DG_0)^2. OK.
S2.8 L869-877 p>R: [L_v:Q_p]<=D<p tame; good reduction (p notin S); conductor <=2. N<=prod_{p<=R}p^E0 M^2
  <= R^{R E0} M^2. OK (Carayol: N = conductor of rho_f at p != l; r_3 used at 5).
S3.1 L860-868 Faltings Hom + Poincare: isogeny A x Z -> J_1(N) over L'. OK.
S3.2 L868-877 index Gamma_1(N) <= N^2, genus, Belyi degree <= N^2; Javanpeykar 13e6 g deg_B^5 <= 13e6 N^12.
S3.3 L879-899 GR14: log deg <= 1024g^3(64g^2 log14g + log d' + 2 log max(..)). With g<=Q^3M^4:
  320Q^7M^12+2QM^4+38QM^4 <= 360Q^7M^12; *1024Q^9M^12 = 368640 Q^16 M^24. OK (C1 planned).
  Lower bound h_F(Z) >= -c dim Z: any c<=Q^14 suffices; normalization constant irrelevant.

## Step 2: computations C1, C2
C1 scratch/rv-h-novel/c1_constants.py (.out): G0=116064000000=|GL4(F5)| exactly; |GL4(F3)|=24261120<=G0;
  2+2U0<=E0; 2(1+log2 a!)<=4a^2 (sample a<=2000 and 10^4..10^39); transfer chain
  (360Q^7M^12, 368640Q^16M^24<=Q^17M^24, final sum <= Q^17M^24, 13e6 N^12<=Q^13M^24) exact at Q=1e12,
  M in {1,2,7} (all monotone in Q,M). Outcome: all hold. VERIFIED.
C2 scratch/rv-h-novel/c2_sqrt_criterion.py (.out): 13 inputs (p,k) in {2^1..2^4,3^1..3^3,5,25,7,49,11,13};
  for every character psi of (Z/p^k)^x: psi is a square of a character of (Z/p^{k+2})^x iff psi(-1)=1.
  135 characters, 0 mismatches. VERIFIED (unit part of the L683-689 criterion).
