import ZInQKernel.OneProof.H.TailZ74
import ZInQKernel.Contrib.OneProof.GaudronRemondSection9

/-! # bost-gr9 fold dry run: the Bost field replaced by Gaudron–Rémond §9 (weaker-leaf bypass)

`ZInQ.BostGR9.GaudronRemondSec9LowerAn` (`h_F ≥ -(3/2) dim`) is weaker than the field `bostLowerBoundAn` it replaces
(`h_F ≥ -(g/2) log(2π²)`), so the next generation cannot map to `OpenResearchLeaves48`. This file copies the 110
declarations of the live path that carry the field (Closure.lean: the research bundles `OpenResearchLeaves8EB`–`48`,
their conversions, the height-row consumer and the `sixContactMin_of_open*` chain) verbatim into `HDec.HSyn.GR9`, with
the field's type weakened at each generation and its three conversions replaced by the GR §9 analogues
(`gen_bypass.py`). Scratch only; generated. -/

set_option linter.style.longLine false

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1280 (HDec.HSyn.OpenResearchLeaves48)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves47` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves48 : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
  /-- bost-gr9, printed form: Gaudron-Remond, Polarisations et isogenies, Duke Math. J. 163 (2014), section 9, proof of Lemme 9.1, p. 2098 (read by the locator audit; cited by the manuscript at L894-895, step E4): h_F(A) >= -(3/2) dim A for every abelian variety over a number field, Faltings' original normalization, over ZInQ.R3Residual.IsAnStableHeight (the object of gaudronRemondThm14An). Replaces bostLowerBoundAn (strictly stronger: -(g/2) log(2 pi^2)); consumed through BostGR9.sec9Printed_of_an, BostGR9.grBostBound_of_sec9Printed_chevalley and BostGR9.r21_of_grBost' (R21). -/
  gaudronRemondSec9LowerAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn
  /-- r3-residual, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over ZInQ.R3Residual.IsAnStableHeight (Faltings' normalization (i/2)^g; the archimedean metric integrated over the complex manifold A_tau(C)^an, densities in every holomorphic chart). Replaces gaudronRemondThm14Printed (ZInQ.R3Residual.gaudronRemondThm14Printed_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35). -/
  gaudronRemondThm14An : _root_.ZInQ.R3Residual.GaudronRemondThm14An
  /-- Hodge-Tate decomposition of V_p(A), tensor form OR Hom form, bases chosen, dimensions unnamed: C_p (x) V_p(A) = C_p(1)^a + C_p^b (Fontaine, Invent. Math. 65 (1982), Theoreme principal, if printed in tensor form) or Hom_{Q_p}(V_p(A), C_p) = C_p^a + C_p(-1)^b (Tate 1967 4, corollary on Hom(T(G), C), good reduction; Fontaine 1982, if printed in Hom form); the Hom form implies the tensor form by C_p-dualization proved in Lean (htdecomp-or); locators UNVERIFIED -/
  hodgeTateDecompOr : _root_.ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr
  /-- x6-coarse, printed form of x6CoarseModuli: the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a bijection Psi on Qbar-points with QM pairs up to isomorphism, natural for Spec sigma, sigma in Aut(Qbar/Q) (X6ALIdeal.GaloisNatural: if Q is a base change of P along sigma, Psi(Spec sigma . x) = [Q]; Mumford GIT Def. 5.6), the Atkin-Lehner clause in the printed ideal-quotient form (for each m | 6 an automorphism w_m of X over Q sends [(A, iota)] to [(A/A[I_m], iota_m)], I_m = {a in O : m | nrd a} the two-sided ideal of reduced norm m, read as every O-equivariant isogeny with scheme-theoretic kernel A[I_m]; X6ALIdeal.ALIdealClause; Rotger, Trans. AMS 356 (2004)), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve. Implies x6CoarseModuli with no hypothesis (X6ALIdeal.x6CoarseModuli_of_ideal: I_m = O mu_m and iota(mu_m) is such an isogeny onto (A, iota o Ad mu_m); the Galois clause is galoisClause_iff_natural); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.x6CoarseModuliIdeal_iff; the quotient of A by A[I_m] is (A, iota o Ad mu_m) by X6ALIdeal.iso_of_quotient_lat, through the lattice model). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). -/
  x6CoarseModuliIdeal : _root_.X6ALIdeal.X6CoarseModuliIdeal
  /-- x6-coarse: Elkies, Shimura curve computations (ANTS-III 1998, arXiv math/0005160) section 3 with Sigma = {2,3}: X*(1) = X(1)/W (p. 10, w_p : A -> A/ker I_p), X*(1) = P^1_t (p. 17), CM values t = 0, 1, infinity at discriminants -24, -4, -3 (Table 1 p. 26, pp. 22-23), Q(X(1)) = Q(t)(sqrt(-t), sqrt(3(t-1))) (p. 17); for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props) whose X carries the printed Atkin-Lehner automorphisms (X6ALIdeal.ALIdealClause), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) for Elkies' isogeny-form W (X6ALIdeal.atkinLehnerWIdeal), the CM values, and the charts s^2 = -t, r^2 = 3(t-1). Replaces elkiesX6StarEvery (X6ALIdeal.elkiesX6StarEvery_of_ideal', with x6CoarseModuliIdeal, shimuraMainThmIDeligneY3AbU and T5); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.ideal_of_elkiesX6StarEvery). -/
  elkiesX6StarEveryIdeal : _root_.X6ALIdeal.ElkiesX6StarEveryIdeal
  /-- gr512-bridge, printed form: Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description: for an order O of k (Tau Ceti NumberFieldOrder) of conductor prime to 6, Q(x) is Q-isomorphic to the ring class field H_R (Tau Ceti ringClassField O) if D(R) != 1, and to a subfield of H_R of index two otherwise; D(R) = product of the p | 6 with pR prime in R (Eichler symbol (R/p) = -1, GR512Bridge.grD6), N*(R) = 1 at N = 1. The old degree form is GR512Bridge.gonzalezRotgerThm512X6_of_rcf (ClassGroup = CommRing.Pic bridge, finrank_ringClassField, grD6_ne_one_iff); LeafQM.O maximal is GR512Bridge.N1.O_maximal. -/
  gonzalezRotgerThm512X6RCF : _root_.GR512Bridge.GonzalezRotgerThm512X6RCF
  /-- R13, printed existence form over a finite coefficient field (htnew-assembly): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there are a finite extension E of Q_l inside Qbar_l (the print's K_{f,lambda} / Kato's F_lambda, embedded) and a continuous rho : G_Q -> GL_2(E), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight +1) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight -1), the multiplicity of w being dim_E (V tensor_{Q_l} C_l(-+w))^{G_{Q_l}} (Mathlib tensor product, the print's definition). Replaces modularHTPrinted: the assembly lemma dim_E (V tensor C_l(w))^G = htMult(rho dual, -w) (trace-form isomorphism V tensor C_l = Hom(E^n, C_l)), HTDual and the coefficient extension E in Qbar_l are proved in Lean (ModularHTCoeff.lean). -/
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  /-- Grothendieck, SGA 7 I, Exp. IX, Cor. 3.3, p. 348, specialized to traits (as sga7_IX_Cor3_3), with semistable reduction in the form of Def. 3.4 (p. 349) read through Def. 2.1.5: the identity component of the geometric special fibre of the Neron model contains no subgroup isomorphic to G_a (GaRigidity.SGA7.IsSemistableDef34, NoGaInIdComp). Replaces sga7_IX_Cor3_3: the dictionary (extension of an abelian variety by a split torus => no G_a) is proved by rigidity for G_a (GaRigidity.noGaSubgroup_of_semiAbelian) -/
  sga7_IX_Cor3_3_Def34 : _root_.GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34
  /-- Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, p. 350, (i) => (iv) at sigma = tau over a strictly henselian DVR with K^s (as sga7_IX_3_5_ForwardGeom), with semistable reduction in the form of Def. 3.4 read through Def. 2.1.5: a Neron model whose geometric special fibre has no G_a in its identity component (GaRigidity.SGA7.HasSemistableReductionDef34). Replaces sga7_IX_3_5_ForwardGeom: the dictionary (extension of an abelian variety by a split torus => no G_a) is proved by rigidity for G_a (GaRigidity.noGaSubgroup_of_semiAbelian) -/
  sga7_IX_3_5_ForwardGeom_Def34 : _root_.GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous), for every generator eps0 = (1, zeta_p, zeta_p^2, ...) of Z_p(1) in O_Cp-flat: dim_Qp (B_dR (x) V)^{G_Qp} = dim V => there is a finite K/Q_p such that B_st (x)_Qp V has a B_st-basis of G_K-invariant vectors (Fontaine's B_st-admissibility, B_st (x) V = B_st^d equivariantly), with Berger's B_st = B_max[log p~], B_max = B_max^+[1/t], t = log [eps0], B_max^+ = A_max[1/p], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} inside Mathlib's B_dR -/
  bergerPrintedVT : _root_.HDec.PkgI4.PanDict.BergerPrintedVT
  /-- Shimura 1967 Main Theorem I in Deligne's form (Sem. Bourbaki 389, sections 4-5; Milne, Introduction to Shimura varieties, sections 5-8 and 12-14) for Y3 = Sh_K3(B^x, H^pm), B = (2,-3|Q), stated as the print states it, for every witness (Y, Phi) of the printed fine-moduli clause list Y3Fix.R1fpPropsAbP: Psi : H^pm x (B (x) A_f)^x -> Y(C) onto with fibres exactly the print's double cosets B^x \ (H^pm x G(A_f) / K3) (DCRelPM); holomorphic in tau in H for every g; at [tau, u], u in O-hat^x (L_u = O), the abelian surface A with (H_1(A, Z), iota_*, h_A) = (O, left multiplication, h_tau) in genuine form (IsHodgeH1Print: H_1 = pi_1(A(C), 0)^ab for the classical topology, O acting by functoriality, the complex structure of Lie A through a holomorphic homomorphism e = exp_A o L, right multiplication by J_tau); Shimura's reciprocity law at CM points of H (conventions existential). Equivalent to the old field deligneCanonicalModelY3EveryH (Y3Hodge.print_iff_deligneH, both directions proved: restriction to H by exists_upper and dcRelPM_iff, retraction H^pm -> H by mu = 1+i, H_1 dictionary print_iff_hodge). Consequence form: bijective and holomorphic in place of the biholomorphism, moduli clause at O-hat^x without polarization (exists and is unique: Y3Hodge.lemmaP_H1, Lemma P on the genuine H_1) and level structure, reciprocity at CM points of H -/
  deligneCanonicalModelY3EveryPrint : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint
  /-- igusa-gal: Diamond-Shurman Thm 7.6.3 (first part) in its printed form: for N > 1, Gal(L_N/Q(j)) -> GL_2(Z/N) is onto, where L_N = Q(j, E_j[N]) (X1Igusa.LDS N) is the subfield of an algebraic closure of Q(j) generated by the x- and y-coordinates of the N-torsion of the universal curve E_j : y^2 = 4x^3 - g x - g, g = 27j/(j - 1728) (DS (7.12)), j transcendental: for some basis e of E_j[N] (the print fixes (P_tau, Q_tau) of (7.11)) and every g in GL_2(Z/N) some sigma_0 in Gal(L_N/Q(j)) acts on E_j[N] as g in the basis e (on L_N-points, Affine.Point.map). Implies igusaGL2DS with no hypothesis (X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome: one basis gives every basis by conjugation in GL_2(Z/N) (igusaGL2DSGal_of_some), then liftNormal to Aut(Q(j)bar/Q(j)), IsAlgClosure.normal, liftNormal_commutes; N = 1 directly). Pages read by igusa-gal: Thm 7.6.3 p. 290 (2005) / p. 294 (2016); rho p. 287 / p. 291; (7.12) p. 282 / p. 286. -/
  igusaGL2DSGalSome : _root_.X1Igusa.IgusaGL2DSGalSome
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1189 (HDec.HSyn.OpenResearchLeaves46CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves46` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves46CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
  /-- r3-residual, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED; Deligne normalization h_D = h_F + (g/2) log pi), over ZInQ.R3Residual.IsAnStableHeight: height-fix's printed stable height with the archimedean metric (i/2)^g int eta~ wedge eta~-bar integrated over the complex manifold A_tau(C)^an, i.e. with the density of the invariant form read in every holomorphic chart (IsHolChart: biholomorphic to the algebraic coordinates at every point; proved to form a complex atlas, Phi-free). Replaces bostLowerBoundPrinted (ZInQ.R3Residual.bostLowerBoundPrinted_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35; isAnStableHeight_iff proves the two heights equal, so the step R3 'clauses to biholomorphic' is a proved theorem). -/
  bostLowerBoundAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn
  /-- r3-residual, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over ZInQ.R3Residual.IsAnStableHeight (Faltings' normalization (i/2)^g; the archimedean metric integrated over the complex manifold A_tau(C)^an, densities in every holomorphic chart). Replaces gaudronRemondThm14Printed (ZInQ.R3Residual.gaudronRemondThm14Printed_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35). -/
  gaudronRemondThm14An : _root_.ZInQ.R3Residual.GaudronRemondThm14An
  /-- Hodge-Tate decomposition of V_p(A), tensor form OR Hom form, bases chosen, dimensions unnamed: C_p (x) V_p(A) = C_p(1)^a + C_p^b (Fontaine, Invent. Math. 65 (1982), Theoreme principal, if printed in tensor form) or Hom_{Q_p}(V_p(A), C_p) = C_p^a + C_p(-1)^b (Tate 1967 4, corollary on Hom(T(G), C), good reduction; Fontaine 1982, if printed in Hom form); the Hom form implies the tensor form by C_p-dualization proved in Lean (htdecomp-or); locators UNVERIFIED -/
  hodgeTateDecompOr : _root_.ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr
  /-- x6-coarse, printed form of x6CoarseModuli: the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a bijection Psi on Qbar-points with QM pairs up to isomorphism, natural for Spec sigma, sigma in Aut(Qbar/Q) (X6ALIdeal.GaloisNatural: if Q is a base change of P along sigma, Psi(Spec sigma . x) = [Q]; Mumford GIT Def. 5.6), the Atkin-Lehner clause in the printed ideal-quotient form (for each m | 6 an automorphism w_m of X over Q sends [(A, iota)] to [(A/A[I_m], iota_m)], I_m = {a in O : m | nrd a} the two-sided ideal of reduced norm m, read as every O-equivariant isogeny with scheme-theoretic kernel A[I_m]; X6ALIdeal.ALIdealClause; Rotger, Trans. AMS 356 (2004)), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve. Implies x6CoarseModuli with no hypothesis (X6ALIdeal.x6CoarseModuli_of_ideal: I_m = O mu_m and iota(mu_m) is such an isogeny onto (A, iota o Ad mu_m); the Galois clause is galoisClause_iff_natural); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.x6CoarseModuliIdeal_iff; the quotient of A by A[I_m] is (A, iota o Ad mu_m) by X6ALIdeal.iso_of_quotient_lat, through the lattice model). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). -/
  x6CoarseModuliIdeal : _root_.X6ALIdeal.X6CoarseModuliIdeal
  /-- x6-coarse: Elkies, Shimura curve computations (ANTS-III 1998, arXiv math/0005160) section 3 with Sigma = {2,3}: X*(1) = X(1)/W (p. 10, w_p : A -> A/ker I_p), X*(1) = P^1_t (p. 17), CM values t = 0, 1, infinity at discriminants -24, -4, -3 (Table 1 p. 26, pp. 22-23), Q(X(1)) = Q(t)(sqrt(-t), sqrt(3(t-1))) (p. 17); for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props) whose X carries the printed Atkin-Lehner automorphisms (X6ALIdeal.ALIdealClause), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) for Elkies' isogeny-form W (X6ALIdeal.atkinLehnerWIdeal), the CM values, and the charts s^2 = -t, r^2 = 3(t-1). Replaces elkiesX6StarEvery (X6ALIdeal.elkiesX6StarEvery_of_ideal', with x6CoarseModuliIdeal, shimuraMainThmIDeligneY3AbU and T5); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.ideal_of_elkiesX6StarEvery). -/
  elkiesX6StarEveryIdeal : _root_.X6ALIdeal.ElkiesX6StarEveryIdeal
  /-- gr512-bridge, printed form: Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description: for an order O of k (Tau Ceti NumberFieldOrder) of conductor prime to 6, Q(x) is Q-isomorphic to the ring class field H_R (Tau Ceti ringClassField O) if D(R) != 1, and to a subfield of H_R of index two otherwise; D(R) = product of the p | 6 with pR prime in R (Eichler symbol (R/p) = -1, GR512Bridge.grD6), N*(R) = 1 at N = 1. The old degree form is GR512Bridge.gonzalezRotgerThm512X6_of_rcf (ClassGroup = CommRing.Pic bridge, finrank_ringClassField, grD6_ne_one_iff); LeafQM.O maximal is GR512Bridge.N1.O_maximal. -/
  gonzalezRotgerThm512X6RCF : _root_.GR512Bridge.GonzalezRotgerThm512X6RCF
  /-- R13, printed existence form over a finite coefficient field (htnew-assembly): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there are a finite extension E of Q_l inside Qbar_l (the print's K_{f,lambda} / Kato's F_lambda, embedded) and a continuous rho : G_Q -> GL_2(E), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight +1) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight -1), the multiplicity of w being dim_E (V tensor_{Q_l} C_l(-+w))^{G_{Q_l}} (Mathlib tensor product, the print's definition). Replaces modularHTPrinted: the assembly lemma dim_E (V tensor C_l(w))^G = htMult(rho dual, -w) (trace-form isomorphism V tensor C_l = Hom(E^n, C_l)), HTDual and the coefficient extension E in Qbar_l are proved in Lean (ModularHTCoeff.lean). -/
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  /-- Grothendieck, SGA 7 I, Exp. IX, Cor. 3.3, p. 348, specialized to traits (as sga7_IX_Cor3_3), with semistable reduction in the form of Def. 3.4 (p. 349) read through Def. 2.1.5: the identity component of the geometric special fibre of the Neron model contains no subgroup isomorphic to G_a (GaRigidity.SGA7.IsSemistableDef34, NoGaInIdComp). Replaces sga7_IX_Cor3_3: the dictionary (extension of an abelian variety by a split torus => no G_a) is proved by rigidity for G_a (GaRigidity.noGaSubgroup_of_semiAbelian) -/
  sga7_IX_Cor3_3_Def34 : _root_.GaRigidity.SGA7.SGA7_IX_Cor3_3_Def34
  /-- Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5, p. 350, (i) => (iv) at sigma = tau over a strictly henselian DVR with K^s (as sga7_IX_3_5_ForwardGeom), with semistable reduction in the form of Def. 3.4 read through Def. 2.1.5: a Neron model whose geometric special fibre has no G_a in its identity component (GaRigidity.SGA7.HasSemistableReductionDef34). Replaces sga7_IX_3_5_ForwardGeom: the dictionary (extension of an abelian variety by a split torus => no G_a) is proved by rigidity for G_a (GaRigidity.noGaSubgroup_of_semiAbelian) -/
  sga7_IX_3_5_ForwardGeom_Def34 : _root_.GaRigidity.SGA7.SGA7_IX_3_5_ForwardGeom_Def34
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous), for every generator eps0 = (1, zeta_p, zeta_p^2, ...) of Z_p(1) in O_Cp-flat: dim_Qp (B_dR (x) V)^{G_Qp} = dim V => there is a finite K/Q_p such that B_st (x)_Qp V has a B_st-basis of G_K-invariant vectors (Fontaine's B_st-admissibility, B_st (x) V = B_st^d equivariantly), with Berger's B_st = B_max[log p~], B_max = B_max^+[1/t], t = log [eps0], B_max^+ = A_max[1/p], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} inside Mathlib's B_dR -/
  bergerPrintedVT : _root_.HDec.PkgI4.PanDict.BergerPrintedVT
  /-- Shimura 1967 Main Theorem I in Deligne's form (Sem. Bourbaki 389, sections 4-5; Milne, Introduction to Shimura varieties, sections 5-8 and 12-14) for Y3 = Sh_K3(B^x, H^pm), B = (2,-3|Q), stated as the print states it, for every witness (Y, Phi) of the printed fine-moduli clause list Y3Fix.R1fpPropsAbP: Psi : H^pm x (B (x) A_f)^x -> Y(C) onto with fibres exactly the print's double cosets B^x \ (H^pm x G(A_f) / K3) (DCRelPM); holomorphic in tau in H for every g; at [tau, u], u in O-hat^x (L_u = O), the abelian surface A with (H_1(A, Z), iota_*, h_A) = (O, left multiplication, h_tau) in genuine form (IsHodgeH1Print: H_1 = pi_1(A(C), 0)^ab for the classical topology, O acting by functoriality, the complex structure of Lie A through a holomorphic homomorphism e = exp_A o L, right multiplication by J_tau); Shimura's reciprocity law at CM points of H (conventions existential). Equivalent to the old field deligneCanonicalModelY3EveryH (Y3Hodge.print_iff_deligneH, both directions proved: restriction to H by exists_upper and dcRelPM_iff, retraction H^pm -> H by mu = 1+i, H_1 dictionary print_iff_hodge). Consequence form: bijective and holomorphic in place of the biholomorphism, moduli clause at O-hat^x without polarization (exists and is unique: Y3Hodge.lemmaP_H1, Lemma P on the genuine H_1) and level structure, reciprocity at CM points of H -/
  deligneCanonicalModelY3EveryPrint : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1339 (HDec.HSyn.openResearchLeaves46_of_OpenResearchLeaves47_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves46_of_OpenResearchLeaves47`, copied from `TailZ73` with the coeff-field-tc edits. -/
theorem openResearchLeaves46_of_OpenResearchLeaves47_cf (n : OpenResearchLeaves48) : OpenResearchLeaves46CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  chevalleyPerfect := n.chevalleyPerfect
  carayolThmAIrr := n.carayolThmAIrr
  panPrintedP := n.panPrintedP
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := _root_.X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome n.igusaGL2DSGalSome
  y3FineModuliAbP := n.y3FineModuliAbP
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  javanpeykarThm111 := n.javanpeykarThm111
  bostLowerBoundAn := n.gaudronRemondSec9LowerAn
  gaudronRemondThm14An := n.gaudronRemondThm14An
  hodgeTateDecompOr := n.hodgeTateDecompOr
  x6CoarseModuliIdeal := n.x6CoarseModuliIdeal
  elkiesX6StarEveryIdeal := n.elkiesX6StarEveryIdeal
  gonzalezRotgerThm512X6RCF := n.gonzalezRotgerThm512X6RCF
  modularHTCoeff := n.modularHTCoeff
  sga7_IX_Cor3_3_Def34 := n.sga7_IX_Cor3_3_Def34
  sga7_IX_3_5_ForwardGeom_Def34 := n.sga7_IX_3_5_ForwardGeom_Def34
  bergerPrintedVT := n.bergerPrintedVT
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1098 (HDec.HSyn.OpenResearchLeaves45CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves45` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves45CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- y3-fix, printed form (one object: Y3 = Sh_K3(B^x, H^+-) with its moduli interpretation and canonical-model property): for every witness (Y, Phi) of R1fpPropsAbP there is Psi : H x (B tensor A_f)^x -> Y(C), onto with fibres the B^x_+ \ . / K3 classes, holomorphic in tau, with the moduli interpretation at g in O-hat^x in the print's H_1 / Hodge form (IsHodgeH1: for an analytic uniformization A(C) = Lie A / H_1(A,Z), an O-linear beta : B_R = H_1(A,R) with beta(O) = H_1(A,Z) and beta(M J_tau) = i beta(M), J_tau = h_tau(i)) and Shimura's reciprocity law at CM points (conventions existential). Deligne, Sem. Bourbaki 389 (1971) section 4 (moduli interpretation by (H_1(A,Q), h_A) = (B, h)) and section 5 (Cor. 5.7 / Ex. 5.8 per locators.md R1); Milne, Introduction to Shimura varieties sections 8 and 14; locators UNVERIFIED. The passage to the kernel's lattice form is proved (Y3Fix.lattice_of_hodge). -/
  deligneCanonicalModelY3EveryH : _root_.Y3Fix.DeligneCanonicalModelY3EveryH
  /-- sga33-steps, printed form (specialized to traits): SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (semistable reduction: Def. 3.4, p. 349; locator from the 11-16 reading in the task brief): for an extension of DVRs O in O' (O' meet K = O, any K'/K, no henselian condition), Neron models N, N' with N semistable, the canonical u : N x_O O' -> N' (generic fibre the identification, bcDVR) induces an isomorphism N0 x_O O' = N'0 (an iso of open subschemes over N'). Replaces sga7_IX_3_3_SHpre: steps 1-3 (specialization; dictionary and Neron uniqueness; c = u . alpha with alpha an automorphism of N' fixing the unit) proved in SGA33Steps.shpre_of_cor33. -/
  sga7_IX_Cor3_3 : _root_.SGA33Steps.SGA7_IX_Cor3_3
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
  /-- r3-residual, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED; Deligne normalization h_D = h_F + (g/2) log pi), over ZInQ.R3Residual.IsAnStableHeight: height-fix's printed stable height with the archimedean metric (i/2)^g int eta~ wedge eta~-bar integrated over the complex manifold A_tau(C)^an, i.e. with the density of the invariant form read in every holomorphic chart (IsHolChart: biholomorphic to the algebraic coordinates at every point; proved to form a complex atlas, Phi-free). Replaces bostLowerBoundPrinted (ZInQ.R3Residual.bostLowerBoundPrinted_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35; isAnStableHeight_iff proves the two heights equal, so the step R3 'clauses to biholomorphic' is a proved theorem). -/
  bostLowerBoundAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn
  /-- r3-residual, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over ZInQ.R3Residual.IsAnStableHeight (Faltings' normalization (i/2)^g; the archimedean metric integrated over the complex manifold A_tau(C)^an, densities in every holomorphic chart). Replaces gaudronRemondThm14Printed (ZInQ.R3Residual.gaudronRemondThm14Printed_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35). -/
  gaudronRemondThm14An : _root_.ZInQ.R3Residual.GaudronRemondThm14An
  /-- Hodge-Tate decomposition of V_p(A), tensor form OR Hom form, bases chosen, dimensions unnamed: C_p (x) V_p(A) = C_p(1)^a + C_p^b (Fontaine, Invent. Math. 65 (1982), Theoreme principal, if printed in tensor form) or Hom_{Q_p}(V_p(A), C_p) = C_p^a + C_p(-1)^b (Tate 1967 4, corollary on Hom(T(G), C), good reduction; Fontaine 1982, if printed in Hom form); the Hom form implies the tensor form by C_p-dualization proved in Lean (htdecomp-or); locators UNVERIFIED -/
  hodgeTateDecompOr : _root_.ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr
  /-- x6-coarse, printed form of x6CoarseModuli: the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a bijection Psi on Qbar-points with QM pairs up to isomorphism, natural for Spec sigma, sigma in Aut(Qbar/Q) (X6ALIdeal.GaloisNatural: if Q is a base change of P along sigma, Psi(Spec sigma . x) = [Q]; Mumford GIT Def. 5.6), the Atkin-Lehner clause in the printed ideal-quotient form (for each m | 6 an automorphism w_m of X over Q sends [(A, iota)] to [(A/A[I_m], iota_m)], I_m = {a in O : m | nrd a} the two-sided ideal of reduced norm m, read as every O-equivariant isogeny with scheme-theoretic kernel A[I_m]; X6ALIdeal.ALIdealClause; Rotger, Trans. AMS 356 (2004)), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve. Implies x6CoarseModuli with no hypothesis (X6ALIdeal.x6CoarseModuli_of_ideal: I_m = O mu_m and iota(mu_m) is such an isogeny onto (A, iota o Ad mu_m); the Galois clause is galoisClause_iff_natural); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.x6CoarseModuliIdeal_iff; the quotient of A by A[I_m] is (A, iota o Ad mu_m) by X6ALIdeal.iso_of_quotient_lat, through the lattice model). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). -/
  x6CoarseModuliIdeal : _root_.X6ALIdeal.X6CoarseModuliIdeal
  /-- x6-coarse: Elkies, Shimura curve computations (ANTS-III 1998, arXiv math/0005160) section 3 with Sigma = {2,3}: X*(1) = X(1)/W (p. 10, w_p : A -> A/ker I_p), X*(1) = P^1_t (p. 17), CM values t = 0, 1, infinity at discriminants -24, -4, -3 (Table 1 p. 26, pp. 22-23), Q(X(1)) = Q(t)(sqrt(-t), sqrt(3(t-1))) (p. 17); for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props) whose X carries the printed Atkin-Lehner automorphisms (X6ALIdeal.ALIdealClause), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) for Elkies' isogeny-form W (X6ALIdeal.atkinLehnerWIdeal), the CM values, and the charts s^2 = -t, r^2 = 3(t-1). Replaces elkiesX6StarEvery (X6ALIdeal.elkiesX6StarEvery_of_ideal', with x6CoarseModuliIdeal, shimuraMainThmIDeligneY3AbU and T5); equivalent to it given the textbook fields gagaMorphism and mumfordTorsionAlgClosed (X6ALIdeal.ideal_of_elkiesX6StarEvery). -/
  elkiesX6StarEveryIdeal : _root_.X6ALIdeal.ElkiesX6StarEveryIdeal
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1248 (HDec.HSyn.openResearchLeaves45_of_OpenResearchLeaves46_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves45_of_OpenResearchLeaves46`, copied from `TailZ72` with the coeff-field-tc edits. -/
theorem openResearchLeaves45_of_OpenResearchLeaves46_cf (n : OpenResearchLeaves46CF) : OpenResearchLeaves45CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := _root_.GaRigidity.SGA7.sga7_IX_3_5_ForwardGeom_of_def34 n.sga7_IX_3_5_ForwardGeom_Def34
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  gonzalezRotgerThm512X6 := _root_.GR512Bridge.gonzalezRotgerThm512X6_of_rcf n.gonzalezRotgerThm512X6RCF
  chevalleyPerfect := n.chevalleyPerfect
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := _root_.HTNewAssembly.modularHTPrinted_of_coeff n.modularHTCoeff
  panPrintedP := n.panPrintedP
  bergerPrintedV := _root_.HDec.PkgI4.PanDict.bergerPrintedV_of_T n.bergerPrintedVT
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := n.igusaGL2DS
  y3FineModuliAbP := n.y3FineModuliAbP
  deligneCanonicalModelY3EveryH := _root_.Y3Hodge.deligneH_of_print n.deligneCanonicalModelY3EveryPrint
  sga7_IX_Cor3_3 := _root_.GaRigidity.SGA7.sga7_IX_Cor3_3_of_def34 n.sga7_IX_Cor3_3_Def34
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  javanpeykarThm111 := n.javanpeykarThm111
  bostLowerBoundAn := n.bostLowerBoundAn
  gaudronRemondThm14An := n.gaudronRemondThm14An
  hodgeTateDecompOr := n.hodgeTateDecompOr
  x6CoarseModuliIdeal := n.x6CoarseModuliIdeal
  elkiesX6StarEveryIdeal := n.elkiesX6StarEveryIdeal
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1007 (HDec.HSyn.OpenResearchLeaves44CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves44` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves44CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- y3-fix, printed form (one object: Y3 = Sh_K3(B^x, H^+-) with its moduli interpretation and canonical-model property): for every witness (Y, Phi) of R1fpPropsAbP there is Psi : H x (B tensor A_f)^x -> Y(C), onto with fibres the B^x_+ \ . / K3 classes, holomorphic in tau, with the moduli interpretation at g in O-hat^x in the print's H_1 / Hodge form (IsHodgeH1: for an analytic uniformization A(C) = Lie A / H_1(A,Z), an O-linear beta : B_R = H_1(A,R) with beta(O) = H_1(A,Z) and beta(M J_tau) = i beta(M), J_tau = h_tau(i)) and Shimura's reciprocity law at CM points (conventions existential). Deligne, Sem. Bourbaki 389 (1971) section 4 (moduli interpretation by (H_1(A,Q), h_A) = (B, h)) and section 5 (Cor. 5.7 / Ex. 5.8 per locators.md R1); Milne, Introduction to Shimura varieties sections 8 and 14; locators UNVERIFIED. The passage to the kernel's lattice form is proved (Y3Fix.lattice_of_hodge). -/
  deligneCanonicalModelY3EveryH : _root_.Y3Fix.DeligneCanonicalModelY3EveryH
  /-- sga33-steps, printed form (specialized to traits): SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (semistable reduction: Def. 3.4, p. 349; locator from the 11-16 reading in the task brief): for an extension of DVRs O in O' (O' meet K = O, any K'/K, no henselian condition), Neron models N, N' with N semistable, the canonical u : N x_O O' -> N' (generic fibre the identification, bcDVR) induces an isomorphism N0 x_O O' = N'0 (an iso of open subschemes over N'). Replaces sga7_IX_3_3_SHpre: steps 1-3 (specialization; dictionary and Neron uniqueness; c = u . alpha with alpha an automorphism of N' fixing the unit) proved in SGA33Steps.shpre_of_cor33. -/
  sga7_IX_Cor3_3 : _root_.SGA33Steps.SGA7_IX_Cor3_3
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
  /-- r3-residual, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED; Deligne normalization h_D = h_F + (g/2) log pi), over ZInQ.R3Residual.IsAnStableHeight: height-fix's printed stable height with the archimedean metric (i/2)^g int eta~ wedge eta~-bar integrated over the complex manifold A_tau(C)^an, i.e. with the density of the invariant form read in every holomorphic chart (IsHolChart: biholomorphic to the algebraic coordinates at every point; proved to form a complex atlas, Phi-free). Replaces bostLowerBoundPrinted (ZInQ.R3Residual.bostLowerBoundPrinted_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35; isAnStableHeight_iff proves the two heights equal, so the step R3 'clauses to biholomorphic' is a proved theorem). -/
  bostLowerBoundAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn
  /-- r3-residual, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over ZInQ.R3Residual.IsAnStableHeight (Faltings' normalization (i/2)^g; the archimedean metric integrated over the complex manifold A_tau(C)^an, densities in every holomorphic chart). Replaces gaudronRemondThm14Printed (ZInQ.R3Residual.gaudronRemondThm14Printed_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35). -/
  gaudronRemondThm14An : _root_.ZInQ.R3Residual.GaudronRemondThm14An
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1157 (HDec.HSyn.openResearchLeaves44_of_OpenResearchLeaves45_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves44_of_OpenResearchLeaves45`, copied from `TailZ71` with the coeff-field-tc edits. -/
theorem openResearchLeaves44_of_OpenResearchLeaves45_cf (n : OpenResearchLeaves45CF) : OpenResearchLeaves44CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := _root_.X6ALIdeal.x6CoarseModuli_of_ideal n.x6CoarseModuliIdeal
  elkiesX6StarEvery := _root_.X6ALIdeal.elkiesX6StarEvery_of_ideal' n.elkiesX6StarEveryIdeal n.x6CoarseModuliIdeal (_root_.Y3Fix.shimuraMainThmIDeligneY3AbU_of_print _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof n.y3FineModuliAbP n.deligneCanonicalModelY3EveryH) _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  hodgeTateDecompExists := _root_.ZInQ.Contrib.HodgeTateOr.hodgeTateDecompExists_of_or n.hodgeTateDecompOr
  chevalleyPerfect := n.chevalleyPerfect
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := n.modularHTPrinted
  panPrintedP := n.panPrintedP
  bergerPrintedV := n.bergerPrintedV
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := n.igusaGL2DS
  y3FineModuliAbP := n.y3FineModuliAbP
  deligneCanonicalModelY3EveryH := n.deligneCanonicalModelY3EveryH
  sga7_IX_Cor3_3 := n.sga7_IX_Cor3_3
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  javanpeykarThm111 := n.javanpeykarThm111
  bostLowerBoundAn := n.bostLowerBoundAn
  gaudronRemondThm14An := n.gaudronRemondThm14An
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:916 (HDec.HSyn.OpenResearchLeaves43CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves43` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves43CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- y3-fix, printed form (one object: Y3 = Sh_K3(B^x, H^+-) with its moduli interpretation and canonical-model property): for every witness (Y, Phi) of R1fpPropsAbP there is Psi : H x (B tensor A_f)^x -> Y(C), onto with fibres the B^x_+ \ . / K3 classes, holomorphic in tau, with the moduli interpretation at g in O-hat^x in the print's H_1 / Hodge form (IsHodgeH1: for an analytic uniformization A(C) = Lie A / H_1(A,Z), an O-linear beta : B_R = H_1(A,R) with beta(O) = H_1(A,Z) and beta(M J_tau) = i beta(M), J_tau = h_tau(i)) and Shimura's reciprocity law at CM points (conventions existential). Deligne, Sem. Bourbaki 389 (1971) section 4 (moduli interpretation by (H_1(A,Q), h_A) = (B, h)) and section 5 (Cor. 5.7 / Ex. 5.8 per locators.md R1); Milne, Introduction to Shimura varieties sections 8 and 14; locators UNVERIFIED. The passage to the kernel's lattice form is proved (Y3Fix.lattice_of_hodge). -/
  deligneCanonicalModelY3EveryH : _root_.Y3Fix.DeligneCanonicalModelY3EveryH
  /-- sga33-steps, printed form (specialized to traits): SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (semistable reduction: Def. 3.4, p. 349; locator from the 11-16 reading in the task brief): for an extension of DVRs O in O' (O' meet K = O, any K'/K, no henselian condition), Neron models N, N' with N semistable, the canonical u : N x_O O' -> N' (generic fibre the identification, bcDVR) induces an isomorphism N0 x_O O' = N'0 (an iso of open subschemes over N'). Replaces sga7_IX_3_3_SHpre: steps 1-3 (specialization; dictionary and Neron uniqueness; c = u . alpha with alpha an automorphism of N' fixing the unit) proved in SGA33Steps.shpre_of_cor33. -/
  sga7_IX_Cor3_3 : _root_.SGA33Steps.SGA7_IX_Cor3_3
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
  /-- r3-residual, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED; Deligne normalization h_D = h_F + (g/2) log pi), over ZInQ.R3Residual.IsAnStableHeight: height-fix's printed stable height with the archimedean metric (i/2)^g int eta~ wedge eta~-bar integrated over the complex manifold A_tau(C)^an, i.e. with the density of the invariant form read in every holomorphic chart (IsHolChart: biholomorphic to the algebraic coordinates at every point; proved to form a complex atlas, Phi-free). Replaces bostLowerBoundPrinted (ZInQ.R3Residual.bostLowerBoundPrinted_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35; isAnStableHeight_iff proves the two heights equal, so the step R3 'clauses to biholomorphic' is a proved theorem). -/
  bostLowerBoundAn : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAn
  /-- r3-residual, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over ZInQ.R3Residual.IsAnStableHeight (Faltings' normalization (i/2)^g; the archimedean metric integrated over the complex manifold A_tau(C)^an, densities in every holomorphic chart). Replaces gaudronRemondThm14Printed (ZInQ.R3Residual.gaudronRemondThm14Printed_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35). -/
  gaudronRemondThm14An : _root_.ZInQ.R3Residual.GaudronRemondThm14An
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1066 (HDec.HSyn.openResearchLeaves43_of_OpenResearchLeaves44_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves43_of_OpenResearchLeaves44`, copied from `TailZ70` with the coeff-field-tc edits. -/
theorem openResearchLeaves43_of_OpenResearchLeaves44_cf (n : OpenResearchLeaves44CF) : OpenResearchLeaves43CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  chevalleyPerfect := n.chevalleyPerfect
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := n.modularHTPrinted
  panPrintedP := n.panPrintedP
  bergerPrintedV := n.bergerPrintedV
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := n.igusaGL2DS
  y3FineModuliAbP := n.y3FineModuliAbP
  deligneCanonicalModelY3EveryH := n.deligneCanonicalModelY3EveryH
  sga7_IX_Cor3_3 := n.sga7_IX_Cor3_3
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  javanpeykarThm111 := n.javanpeykarThm111
  bostLowerBoundAn := n.bostLowerBoundAn
  gaudronRemondThm14An := n.gaudronRemondThm14An
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:824 (HDec.HSyn.OpenResearchLeaves42CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves42` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves42CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- y3-fix, printed form (one object: Y3 = Sh_K3(B^x, H^+-) with its moduli interpretation and canonical-model property): for every witness (Y, Phi) of R1fpPropsAbP there is Psi : H x (B tensor A_f)^x -> Y(C), onto with fibres the B^x_+ \ . / K3 classes, holomorphic in tau, with the moduli interpretation at g in O-hat^x in the print's H_1 / Hodge form (IsHodgeH1: for an analytic uniformization A(C) = Lie A / H_1(A,Z), an O-linear beta : B_R = H_1(A,R) with beta(O) = H_1(A,Z) and beta(M J_tau) = i beta(M), J_tau = h_tau(i)) and Shimura's reciprocity law at CM points (conventions existential). Deligne, Sem. Bourbaki 389 (1971) section 4 (moduli interpretation by (H_1(A,Q), h_A) = (B, h)) and section 5 (Cor. 5.7 / Ex. 5.8 per locators.md R1); Milne, Introduction to Shimura varieties sections 8 and 14; locators UNVERIFIED. The passage to the kernel's lattice form is proved (Y3Fix.lattice_of_hodge). -/
  deligneCanonicalModelY3EveryH : _root_.Y3Fix.DeligneCanonicalModelY3EveryH
  /-- sga33-steps, printed form (specialized to traits): SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (semistable reduction: Def. 3.4, p. 349; locator from the 11-16 reading in the task brief): for an extension of DVRs O in O' (O' meet K = O, any K'/K, no henselian condition), Neron models N, N' with N semistable, the canonical u : N x_O O' -> N' (generic fibre the identification, bcDVR) induces an isomorphism N0 x_O O' = N'0 (an iso of open subschemes over N'). Replaces sga7_IX_3_3_SHpre: steps 1-3 (specialization; dictionary and Neron uniqueness; c = u . alpha with alpha an automorphism of N' fixing the unit) proved in SGA33Steps.shpre_of_cor33. -/
  sga7_IX_Cor3_3 : _root_.SGA33Steps.SGA7_IX_Cor3_3
  /-- Fontaine, as printed by Berger, An introduction to the theory of p-adic representations (Geometric aspects of Dwork theory, de Gruyter 2004; arXiv math/0210184v1) section II.5.1, p. 19: the Tate modules of abelian varieties are de Rham, i.e. dim_K D_dR(V_p(A)) = dim_{Q_p} V_p(A) with D_dR(V) = (B_dR (x)_{Q_p} V)^{G_K} a K-space through K -> Kbar -> B_dR^+. Lean form: A over a finite F/Q_p, G_F acting through gfToGqp (image G_{F'}, F' the image of F in Qbar_p, so the print's K is F'), D_dR = DeRhamPrint.Direct.ddrF an F'-space through iotaF : F' -> Qbar_p -> B_dR^+ -> B_dR, the unique theta-compatible lift (iotaPlusF_unique), G_F-invariant (bdrAct_iotaF). Equivalent to the old field deRhamVpAbVarPrinted by the tower law (deRhamVpAbVarPrinted_of_direct and its converse, proved). Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarDirect : _root_.DeRhamPrint.Direct.DeRhamVpAbVarDirect
  /-- javanpeykar-direct: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1, over the print's objects: for Kbar any algebraic closure of Q and X a smooth proper connected integral curve over Kbar (IsCurve), projective (closed immersion into P(n; Spec Kbar)), of genus g = genusK X = dim H^1(X, O_X) >= 1, W an abelian variety over Kbar representing Pic^0_{X/Kbar} with the tensor group law (Jac X), h_Fal(Jac X) = any x with IsStableHeightBar W x (x is height-fix's printed stable height IsPrintedStableHeight of a model of W over some number field L inside Kbar), and deg_B(X) = belyiDegree X hB = Nat.find of the existence of a Belyi map of positive degree (hB: X has a Belyi map, javanpeykar-fix's IsBelyiMap; Belyi's theorem is not used): x <= 13*10^6 * g * deg_B(X)^5. javanpeykarPrintedMapHF follows in Lean (JavanpeykarDirect.javanpeykarPrintedMap_of_thm111: specialization Kbar = AlgebraicClosure K, X = X0 x_K Kbar; deg_B(X) <= d for the given Belyi map and the bound increasing in deg_B; L = K for the model V). -/
  javanpeykarThm111 : _root_.JavanpeykarDirect.JavanpeykarThm111
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:975 (HDec.HSyn.openResearchLeaves42_of_OpenResearchLeaves43_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves42_of_OpenResearchLeaves43`, copied from `TailZ68` with the coeff-field-tc edits. -/
theorem openResearchLeaves42_of_OpenResearchLeaves43_cf (n : OpenResearchLeaves43CF) : OpenResearchLeaves42CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := _root_.ZInQ.BostGR9.sec9Printed_of_an n.bostLowerBoundAn _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := _root_.ZInQ.R3Residual.gaudronRemondThm14Printed_of_an n.gaudronRemondThm14An _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := n.modularHTPrinted
  panPrintedP := n.panPrintedP
  bergerPrintedV := n.bergerPrintedV
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := n.igusaGL2DS
  y3FineModuliAbP := n.y3FineModuliAbP
  deligneCanonicalModelY3EveryH := n.deligneCanonicalModelY3EveryH
  sga7_IX_Cor3_3 := n.sga7_IX_Cor3_3
  deRhamVpAbVarDirect := n.deRhamVpAbVarDirect
  javanpeykarThm111 := n.javanpeykarThm111
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:734 (HDec.HSyn.OpenResearchLeaves41CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves41` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves41CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
  /-- javanpeykar-rebase: Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 in printed form at X = X0 x_K Qbar (X0 a smooth proper geometrically connected curve over a number field K, Qbar = AlgebraicClosure K): X projective (closed immersion into a projective space over Qbar), Jac(X) = W an abelian variety over Qbar representing Pic^0_{X/Qbar} with the tensor group law, V a model of W over K (V_Qbar = W), g = genusBar X = dim H^1(X, O_X), beta : X -> P^1_Qbar = Proj Qbar[X0,X1] a Belyi map of degree d (IsBelyiMap), h = height-fix's printed stable height ZInQ.HeightFix.IsPrintedStableHeight of V (sound archimedean metric defined chart by chart; Neron model semistable over the residue fields k(p)): h <= 13*10^6 * g * d^5. javanpeykar-fix's JavanpeykarPrintedMap verbatim over height-fix's height (JavanpeykarRebase.javanpeykarPrintedMap_of_fix: implied by it given T35 and Stacks 04KV). Replaces javanpeykarBound (JavanpeykarRebase.javanpeykarBound_of_printed_rebase, with constantFieldExtensionUnramifiedFinite, mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35, and height-fix's glue semiAbelianDescendsPerfect). -/
  javanpeykarPrintedMapHF : _root_.JavanpeykarRebase.JavanpeykarPrintedMap
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
  /-- aftate-fix2 (r16-det fold): the Hecke operators on J_1(N) over Q. For N >= 2, every model X of Diamond-Shurman's X_1(N)_alg with chosen generators (j_X, t_X) of K(X) = Q(j, f_1) (IsX1Gen: the integer relations of (j_X, t_X) are those of (j(tau), f_1(tau)), f_1 = T5Glue.weber <1,tau> (1/N)), every rational point P0 and every Jacobian (J, aj) (Albanese property): there are endomorphisms T_p (every prime p) and <d> (d in (Z/N)^*) of J over Q acting on degree-0 divisor classes of the points x_tau (AtTau: the complex point where every g in K(X) whose meromorphic function on H has a limit c at tau is regular with value c) by DS's double-coset formulas: T_p[x_tau] = sum_{j<p} [x_{(tau+j)/p}] + [x_{g(p tau)}] (last term for p not dividing N; g in SL_2(Z), N | c, d = p mod N), <d>[x_tau] = [x_{g tau}]. -/
  heckeJ1DS : _root_.AfTateLam.HeckeJ1DS
  /-- aftate-fix2 (r16-det fold): Shimura's A_f over Q. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, N >= 2, X, (j_X, t_X), P0, (J, aj) as in heckeJ1DS and any T_p, <d> with DS's divisor action: K_f is a number field, and there are A, pi : J -> A and theta : K_f -> End^0(A) with IsAfQuotient (pi surjective, kills I_f J, universal among homomorphisms to abelian varieties killing I_f J; I_f = image of the kernel of T_p -> a_p(f), <d> -> chi(d) on the free algebra) and IsAfAction (theta(a_p) is the endomorphism induced by T_p, theta(chi(d)) the one induced by <d>). -/
  afShimura : _root_.AfTateLam.AfShimura
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- x1-igusa: Igusa's theorem in its printed form, Gal(Q(j, E_j[N])/Q(j)) = GL_2(Z/N) for Diamond-Shurman's E_j : y^2 = 4x^3 - g x - g, g = 27j/(j-1728), j transcendental. For N >= 1, every basis e : (Z/N)^2 = E_j[N] over an algebraic closure of Q(j) and every g in GL_2(Z/N), some sigma in Aut(Q(j)bar/Q(j)) acts on E_j[N] as g in the basis e. Used through X1Igusa.x1PointsConjugate_of_igusaGL2DS (the dictionary IsX1Model -> IsX1AlgDS, aftate-or). -/
  igusaGL2DS : _root_.X1Igusa.IgusaGL2DS
  /-- y3-fix, printed form (representability, one object: the fine moduli scheme Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full level-3 structure in Mumford's form (GIT Def. 7.1, O-linear: at every geometric point s the sections eta(a), a in O/3O, are exactly the points of A_s(k)[3]) is represented over Q by a proper smooth curve (some (Y, Phi) satisfies R1fpPropsAbP; no Qbar-point clause). Buzzard, Duke Math. J. 87 (1997) section 1; Boutot-Carayol, Asterisque 196-197 (1991) ch. III; Milne 1979; Mumford GIT Def. 7.1, Thm 7.9; locators UNVERIFIED. Consequence form: universal property used on proper smooth curve bases and read on field points; base Q. Equivalent to the kernel's level form over Q-schemes (Y3Fix.toKer, Y3Fix.ofKer from mumfordTorsionAlgClosed). -/
  y3FineModuliAbP : _root_.Y3Fix.Y3FineModuliAbP
  /-- y3-fix, printed form (one object: Y3 = Sh_K3(B^x, H^+-) with its moduli interpretation and canonical-model property): for every witness (Y, Phi) of R1fpPropsAbP there is Psi : H x (B tensor A_f)^x -> Y(C), onto with fibres the B^x_+ \ . / K3 classes, holomorphic in tau, with the moduli interpretation at g in O-hat^x in the print's H_1 / Hodge form (IsHodgeH1: for an analytic uniformization A(C) = Lie A / H_1(A,Z), an O-linear beta : B_R = H_1(A,R) with beta(O) = H_1(A,Z) and beta(M J_tau) = i beta(M), J_tau = h_tau(i)) and Shimura's reciprocity law at CM points (conventions existential). Deligne, Sem. Bourbaki 389 (1971) section 4 (moduli interpretation by (H_1(A,Q), h_A) = (B, h)) and section 5 (Cor. 5.7 / Ex. 5.8 per locators.md R1); Milne, Introduction to Shimura varieties sections 8 and 14; locators UNVERIFIED. The passage to the kernel's lattice form is proved (Y3Fix.lattice_of_hodge). -/
  deligneCanonicalModelY3EveryH : _root_.Y3Fix.DeligneCanonicalModelY3EveryH
  /-- sga33-steps, printed form (specialized to traits): SGA 7 I, Exp. IX, Cor. 3.3, p. 348 (semistable reduction: Def. 3.4, p. 349; locator from the 11-16 reading in the task brief): for an extension of DVRs O in O' (O' meet K = O, any K'/K, no henselian condition), Neron models N, N' with N semistable, the canonical u : N x_O O' -> N' (generic fibre the identification, bcDVR) induces an isomorphism N0 x_O O' = N'0 (an iso of open subschemes over N'). Replaces sga7_IX_3_3_SHpre: steps 1-3 (specialization; dictionary and Neron uniqueness; c = u . alpha with alpha an automorphism of N' fixing the unit) proved in SGA33Steps.shpre_of_cor33. -/
  sga7_IX_Cor3_3 : _root_.SGA33Steps.SGA7_IX_Cor3_3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:883 (HDec.HSyn.openResearchLeaves41_of_OpenResearchLeaves42_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves41_of_OpenResearchLeaves42`, copied from `TailZ67` with the coeff-field-tc edits. -/
theorem openResearchLeaves41_of_OpenResearchLeaves42_cf (n : OpenResearchLeaves42CF) : OpenResearchLeaves41CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  deRhamVpAbVarPrinted := _root_.DeRhamPrint.Direct.deRhamVpAbVarPrinted_of_direct n.deRhamVpAbVarDirect
  bdRInvariantsPrinted := _root_.BdRInv.bdRInvariantsPrinted_proof
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := n.bostLowerBoundPrinted
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed
  javanpeykarPrintedMapHF := _root_.JavanpeykarDirect.javanpeykarPrintedMap_of_thm111 n.javanpeykarThm111
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := n.modularHTPrinted
  panPrintedP := n.panPrintedP
  bergerPrintedV := n.bergerPrintedV
  heckeJ1DS := n.heckeJ1DS
  afShimura := n.afShimura
  afCharpolyDS965 := n.afCharpolyDS965
  igusaGL2DS := n.igusaGL2DS
  y3FineModuliAbP := n.y3FineModuliAbP
  deligneCanonicalModelY3EveryH := n.deligneCanonicalModelY3EveryH
  sga7_IX_Cor3_3 := n.sga7_IX_Cor3_3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:652 (HDec.HSyn.OpenResearchLeaves40CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves40` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves40CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED); the print assumes a perfect residue field and this statement is for every discrete valuation ring, so it exceeds the print (AI audit 2026-11-17; the chain uses it over number fields only) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
  /-- javanpeykar-rebase: Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 in printed form at X = X0 x_K Qbar (X0 a smooth proper geometrically connected curve over a number field K, Qbar = AlgebraicClosure K): X projective (closed immersion into a projective space over Qbar), Jac(X) = W an abelian variety over Qbar representing Pic^0_{X/Qbar} with the tensor group law, V a model of W over K (V_Qbar = W), g = genusBar X = dim H^1(X, O_X), beta : X -> P^1_Qbar = Proj Qbar[X0,X1] a Belyi map of degree d (IsBelyiMap), h = height-fix's printed stable height ZInQ.HeightFix.IsPrintedStableHeight of V (sound archimedean metric defined chart by chart; Neron model semistable over the residue fields k(p)): h <= 13*10^6 * g * d^5. javanpeykar-fix's JavanpeykarPrintedMap verbatim over height-fix's height (JavanpeykarRebase.javanpeykarPrintedMap_of_fix: implied by it given T35 and Stacks 04KV). Replaces javanpeykarBound (JavanpeykarRebase.javanpeykarBound_of_printed_rebase, with constantFieldExtensionUnramifiedFinite, mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35, and height-fix's glue semiAbelianDescendsPerfect). -/
  javanpeykarPrintedMapHF : _root_.JavanpeykarRebase.JavanpeykarPrintedMap
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda}, with Ribet's irreducibility and oddness (r17-print, r17-rebase): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), irreducible (no stable subspace other than 0 and K_{f,lambda}^2), odd (some involution c in G_Q has det rho(c) = -1), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (Burnside's form from irreducible + odd; IsNewform = printed newform; extension of scalars to Qbar_l; absolute irreducibility gives semisimplicity; conductor invariance under scalar extension and isomorphism; Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17-print's carayolThmA (CarayolPrinted.carayolThmA_of_irr), which replaced r17. -/
  carayolThmAIrr : _root_.CarayolPrinted.CarayolThmAIrr
  /-- R13, printed existence form, reading-robust (htnew-print): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there is a continuous rho : G_Q -> GL_2(Qbar_l), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, 1-k}) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}) (kernel convention: cyclotomic weight -1). No semisimplicity asked; the trace clause is 'if iota_C(alpha) = a_p then tr = iota_L(alpha)'. Replaces eigenformHTNew: semisimplification preserves HT weights, the dual, the newform dictionary and the Chebotarev/Brauer-Nesbitt transport are proved in Lean (EigenformHTPrinted.lean). -/
  modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted
  /-- R12. Pan, J. Amer. Math. Soc. 35 (2022), 1031-1169, Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, pp. 5 and 2; JAMS number and page UNVERIFIED), p >= 5, for each iota_p : Qbar_p = C, printed form for one continuous rho : G_Q -> GL_2(Qbar_p): rho irreducible (no stable subspace but 0 and Qbar_p^2), unramified outside finitely many primes, odd, rho|G_Qp potentially semistable (Fontaine admissibility over Berger's B_st = B_max[log p~] inside B_dR, on a model V = E^n) and with distinct Hodge-Tate weights (multiplicity of w = dim_E (V (x)_Qp C_p(w))^{G_Qp}, cyclotomic weight -1) => rho comes from a cuspidal eigenform up to twist: a cuspidal eigenform g (Tau Ceti EigenformAwayFromLevel N k), rho_g attached to g through iota_p (tr rho_g(Frob_q^geom) = iota_p^-1(lambda_q(g)) and unramified, almost all q), a continuous character psi and P in GL_2(Qbar_p) with rho(s) = psi(s) P rho_g(s) P^-1 -/
  panPrintedP : _root_.HDec.PkgI4.PanDict.PanPrintedP
  /-- R11. Berger, Invent. Math. 148 (2002), Theoreme 0.7 = Cor. 5.22 of the published version (author copy pp. 6, 52) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3, K = Q_p, for one p-adic representation V = E^n (E/Q_p finite inside Qbar_p, rho_E : G_Qp -> GL_n(E) continuous): dim_Qp (B_dR (x) V)^{G_Qp} = dim V => exists finite K/Q_p with dim over B_st^{G_K} of (B_st (x) V)^{G_K} = dim V, Berger's B_st = B_max[log p~] inside Mathlib's B_dR, B_max = A_max[1/p][1/t], A_max = {sum a_n (omega/p)^n : a_n in A_inf -> 0} -/
  bergerPrintedV : _root_.HDec.PkgI4.PanDict.BergerPrintedV
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:795 (HDec.HSyn.openResearchLeaves40_of_OpenResearchLeaves41_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves40_of_OpenResearchLeaves41`, copied from `TailZ66` with the coeff-field-tc edits. -/
theorem openResearchLeaves40_of_OpenResearchLeaves41_cf (n : OpenResearchLeaves41CF) : OpenResearchLeaves40CF where
  r9a := n.r9a
  r9b := n.r9b
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := _root_.Y3Fix.shimuraMainThmIDeligneY3AbU_of_print _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof n.y3FineModuliAbP n.deligneCanonicalModelY3EveryH
  r16CoreY := _root_.AfTateLam.r16CoreY_of_ds965 n.heckeJ1DS n.afShimura n.afCharpolyDS965 n.igusaGL2DS _root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  sga7_IX_3_3_SHpre := _root_.SGA33Steps.shpre_of_cor33 n.sga7_IX_Cor3_3
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := n.bostLowerBoundPrinted
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed
  javanpeykarPrintedMapHF := n.javanpeykarPrintedMapHF
  carayolThmAIrr := n.carayolThmAIrr
  modularHTPrinted := n.modularHTPrinted
  panPrintedP := n.panPrintedP
  bergerPrintedV := n.bergerPrintedV
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:571 (HDec.HSyn.OpenResearchLeaves39CF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves39` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves39CF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
  /-- javanpeykar-rebase: Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 in printed form at X = X0 x_K Qbar (X0 a smooth proper geometrically connected curve over a number field K, Qbar = AlgebraicClosure K): X projective (closed immersion into a projective space over Qbar), Jac(X) = W an abelian variety over Qbar representing Pic^0_{X/Qbar} with the tensor group law, V a model of W over K (V_Qbar = W), g = genusBar X = dim H^1(X, O_X), beta : X -> P^1_Qbar = Proj Qbar[X0,X1] a Belyi map of degree d (IsBelyiMap), h = height-fix's printed stable height ZInQ.HeightFix.IsPrintedStableHeight of V (sound archimedean metric defined chart by chart; Neron model semistable over the residue fields k(p)): h <= 13*10^6 * g * d^5. javanpeykar-fix's JavanpeykarPrintedMap verbatim over height-fix's height (JavanpeykarRebase.javanpeykarPrintedMap_of_fix: implied by it given T35 and Stacks 04KV). Replaces javanpeykarBound (JavanpeykarRebase.javanpeykarBound_of_printed_rebase, with constantFieldExtensionUnramifiedFinite, mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35, and height-fix's glue semiAbelianDescendsPerfect). -/
  javanpeykarPrintedMapHF : _root_.JavanpeykarRebase.JavanpeykarPrintedMap
  /-- javanpeykar-rebase: Stichtenoth, Algebraic Function Fields and Codes (2nd ed., GTM 254), Thm 3.6.3(a), for a FINITE constant field extension, with Stichtenoth's standing hypothesis that K is the full constant field of F: for F/K an algebraic function field (char 0) and L/K finite with F (x)_K L = FL (bijective productMap), every place of FL/L (valuation subring w containing L) is unramified over its restriction to F: a generator of the maximal ideal of w cap F generates that of w. The algebraic case used by the consumer (L = Kbar) is proved from it (JavanpeykarRebase.full_of_finite); finite_of_full gives the converse. -/
  constantFieldExtensionUnramifiedFinite : _root_.JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:705 (HDec.HSyn.openResearchLeaves39_of_OpenResearchLeaves40_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves39_of_OpenResearchLeaves40`, copied from `TailZ65` with the coeff-field-tc edits. -/
theorem openResearchLeaves39_of_OpenResearchLeaves40_cf (n : OpenResearchLeaves40CF) : OpenResearchLeaves39CF where
  r9a := n.r9a
  r9b := n.r9b
  r11r12 := _root_.HDec.PkgI4.PanDict.panBerger_of_printedPV n.panPrintedP n.bergerPrintedV n.dsThm965Printed (_root_.eigenformCoeffFieldFinite_proof) n.dsThm966Printed
  eigenformHTNew := _root_.EigenformHTPrinted.eigenformHTNew_of_printed n.modularHTPrinted (_root_.eigenformCoeffFieldFinite_proof)
  pazukiCor13Upper := n.pazukiCor13Upper
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := _root_.CarayolPrinted.carayolThmA_of_irr n.carayolThmAIrr
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := n.bostLowerBoundPrinted
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed
  javanpeykarPrintedMapHF := n.javanpeykarPrintedMapHF
  constantFieldExtensionUnramifiedFinite := _root_.CFExtProof.constantFieldExtensionUnramifiedFinite_proof
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:487 (HDec.HSyn.OpenResearchLeaves38EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves38EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves38EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
  /-- javanpeykar-rebase: Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 in printed form at X = X0 x_K Qbar (X0 a smooth proper geometrically connected curve over a number field K, Qbar = AlgebraicClosure K): X projective (closed immersion into a projective space over Qbar), Jac(X) = W an abelian variety over Qbar representing Pic^0_{X/Qbar} with the tensor group law, V a model of W over K (V_Qbar = W), g = genusBar X = dim H^1(X, O_X), beta : X -> P^1_Qbar = Proj Qbar[X0,X1] a Belyi map of degree d (IsBelyiMap), h = height-fix's printed stable height ZInQ.HeightFix.IsPrintedStableHeight of V (sound archimedean metric defined chart by chart; Neron model semistable over the residue fields k(p)): h <= 13*10^6 * g * d^5. javanpeykar-fix's JavanpeykarPrintedMap verbatim over height-fix's height (JavanpeykarRebase.javanpeykarPrintedMap_of_fix: implied by it given T35 and Stacks 04KV). Replaces javanpeykarBound (JavanpeykarRebase.javanpeykarBound_of_printed_rebase, with constantFieldExtensionUnramifiedFinite, mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35, and height-fix's glue semiAbelianDescendsPerfect). -/
  javanpeykarPrintedMapHF : _root_.JavanpeykarRebase.JavanpeykarPrintedMap
  /-- javanpeykar-rebase: Stichtenoth, Algebraic Function Fields and Codes (2nd ed., GTM 254), Thm 3.6.3(a), for a FINITE constant field extension, with Stichtenoth's standing hypothesis that K is the full constant field of F: for F/K an algebraic function field (char 0) and L/K finite with F (x)_K L = FL (bijective productMap), every place of FL/L (valuation subring w containing L) is unramified over its restriction to F: a generator of the maximal ideal of w cap F generates that of w. The algebraic case used by the consumer (L = Kbar) is proved from it (JavanpeykarRebase.full_of_finite); finite_of_full gives the converse. -/
  constantFieldExtensionUnramifiedFinite : _root_.JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:622 (HDec.HSyn.openResearchLeaves38EB_of_OpenResearchLeaves39_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves38EB_of_OpenResearchLeaves39`, copied from `TailZ63` with the coeff-field-tc edits. -/
theorem openResearchLeaves38EB_of_OpenResearchLeaves39_cf (n : OpenResearchLeaves39CF) (t : OpenTextbookLeaves16) : OpenResearchLeaves38EBCF where
  r9a := n.r9a
  r9b := n.r9b
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  pazukiCor13Upper := n.pazukiCor13Upper
  gonzalezRotgerProp56X6 := _root_.EichlerBound.r5fpCountLe_of_two t.gagaMorphism t.mumfordTorsionAlgClosed
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := n.bostLowerBoundPrinted
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed
  javanpeykarPrintedMapHF := n.javanpeykarPrintedMapHF
  constantFieldExtensionUnramifiedFinite := n.constantFieldExtensionUnramifiedFinite
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:405 (HDec.HSyn.OpenResearchLeaves37EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves37EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves37EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
  /-- height-fix, printed form: Bost, Sem. Bourbaki 795 (Asterisque 237, 1996), h_D(A) >= -(g/2) log 2pi (display UNVERIFIED), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight: Neron model over a field where A has semistable reduction in the sense of SGA 7 IX Def. 3.4 read over the residue fields k(p) (IsSemistableRes), omega = wedge^g Gamma(S, e*Omega^1), and the archimedean metric (i/2)^g int_{A(C)} eta wedge eta-bar as the total mass of the measure defined chart by chart (density |tau l|^2 in translated algebraic coordinates at every point), which must exist (IsPrintedMetricSq). Replaces bostLowerBound (ZInQ.HeightFix.bostLowerBound_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  bostLowerBoundPrinted : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerPrinted
  /-- semiab-descend, printed form: Chevalley's structure theorem over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002) Thm 1.1; Milne, Algebraic Groups (2017) Thm 8.27; numbers UNVERIFIED): a smooth connected group scheme G of finite type over a perfect field k has a unique normal smooth connected affine subgroup H with G/H an abelian variety. Lean form: existence of a faithfully flat homomorphism pi : G -> B onto an abelian variety (PkgI3.AbVar) whose scheme-theoretic kernel G x_B Spec k is smooth, connected and affine, and uniqueness of that kernel on T-points; G/H read as the target of a faithfully flat homomorphism with kernel H (the definition of a quotient, Milne AG section 5.c). Replaces the glue semiAbelianDescendsPerfect (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley proves it for every perfect field). -/
  chevalleyPerfect : _root_.ZInQ.SemiAbDescend.ChevalleyPerfect
  /-- height-fix, printed form: Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the locator audit), over the printed stable height ZInQ.HeightFix.IsPrintedStableHeight (Faltings' original normalization (i/2)^g; semistability over k(p) as SGA 7 IX Def. 3.4 print it; the metric defined chart by chart and required to exist). Replaces gaudronRemondThm14 (ZInQ.HeightFix.gaudronRemondThm14_of_printed, with uniformizationLeafAll and mumfordTorsionAlgClosed for T35 and the leaf chevalleyPerfect (semiab-descend)). -/
  gaudronRemondThm14Printed : _root_.ZInQ.HeightFix.GaudronRemondThm14Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:542 (HDec.HSyn.openResearchLeaves37_of_OpenResearchLeaves38_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves37_of_OpenResearchLeaves38_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves37_of_OpenResearchLeaves38_eb_cf (n : OpenResearchLeaves38EBCF) (t : OpenTextbookLeaves16) : OpenResearchLeaves37EBCF where
  r9a := n.r9a
  r9b := n.r9b
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  javanpeykarBound := _root_.JavanpeykarRebase.javanpeykarBound_of_printed_rebase_final n.javanpeykarPrintedMapHF n.constantFieldExtensionUnramifiedFinite t.mumfordTorsionAlgClosed (_root_.ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley n.chevalleyPerfect)
  pazukiCor13Upper := n.pazukiCor13Upper
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
  bostLowerBoundPrinted := n.bostLowerBoundPrinted
  chevalleyPerfect := n.chevalleyPerfect
  gaudronRemondThm14Printed := n.gaudronRemondThm14Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:325 (HDec.HSyn.OpenResearchLeaves36EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves36EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves36EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
  /-- Fontaine, Invent. Math. 65 (1982), Theoreme principal: C_p (x) V_p(A) = (C_p(1) (x)_F t_A) + (C_p (x)_F t*_{A'}), G_F-equivariant; bases of the two finite-dimensional F-spaces chosen, both dimensions left unnamed (C_p(1)^a + C_p^b for some a, b); locator UNVERIFIED -/
  hodgeTateDecompExists : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:459 (HDec.HSyn.openResearchLeaves36_of_OpenResearchLeaves37_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves36_of_OpenResearchLeaves37_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves36_of_OpenResearchLeaves37_eb_cf (n : OpenResearchLeaves37EBCF) (t : OpenTextbookLeaves16) : OpenResearchLeaves36EBCF where
  r9a := n.r9a
  r9b := n.r9b
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  bostLowerBound := _root_.ZInQ.BostGR9.grBostBound_of_sec9Printed_chevalley n.bostLowerBoundPrinted _root_.uniformizationLeafAll_proof t.mumfordTorsionAlgClosed n.chevalleyPerfect
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := _root_.ZInQ.SemiAbDescend.gaudronRemondThm14_of_printed_chevalley n.gaudronRemondThm14Printed _root_.uniformizationLeafAll_proof t.mumfordTorsionAlgClosed n.chevalleyPerfect
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
  hodgeTateDecompExists := n.hodgeTateDecompExists
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:247 (HDec.HSyn.OpenResearchLeaves35EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves35EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves35EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
  /-- gr-dict / grx6ab-print, printed form (degree-and-embedding consequence): Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, p. 946 (arXiv math/0612732 v1/v2 pp. 18-19; read by the locator audit), at (D,N) = (6,1), over CM points as Gonzalez-Rotger define them (GRDict.IsGRCMPoint), on every witness of the moduli description (no existence claim): [Q(x):Q] = 2h(R) with k in Q(x) if some p | 6 is inert in k, h(R) otherwise. With x6CoarseModuli replaces gonzalezRotgerX6Ab. -/
  gonzalezRotgerThm512X6 : _root_.GRDict.GonzalezRotgerThm512X6
  /-- grx6ab-print, printed form (the coarse-moduli theorem for X0(6,1), one object): the canonical model X6 = X0(6,1) over Q is a proper smooth curve and a coarse moduli scheme for abelian surfaces with QM by O: a Galois-equivariant bijection on Qbar-points with QM pairs up to isomorphism, Aut(O)-twists induced by automorphisms of X (the Atkin-Lehner group), and the classifying map of a level-3 QM abelian scheme over a proper smooth curve (a specialization of the natural transformation). Locators UNVERIFIED (Shimura 1967; Deligne, Sem. Bourbaki 389; Buzzard, Duke 87 (1997) section 1). With shimuraMainThmIDeligneY3AbU it gives the moduli witness (the forgetful map Y3 -> X6 is proved: GRX6AbPrint.x6ModuliWitness_of_coarse). -/
  x6CoarseModuli : _root_.GRX6AbPrint.X6CoarseModuli
  /-- elkies-print: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, for every witness of the moduli description of X0(6,1) (R1fpPropsAb, X6Props), with no existence claim: some t : X6 -> P1 with Q(X6)^W = Q(t) (whenever X6 is integral and t regular at its generic point, both proved from the charts), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). The witness comes from shimuraMainThmIDeligneY3AbU and x6CoarseModuli (GRX6AbPrint.x6ModuliWitness_of_coarse). Replaces elkiesX6StarFunctionField; equivalent to it given a witness and T5 (every_iff_functionField). -/
  elkiesX6StarEvery : _root_.HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:377 (HDec.HSyn.openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954`, copied from `TailZ69` with the coeff-field-tc edits. -/
theorem openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf (n : OpenResearchLeaves36EBCF) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26) : OpenResearchLeaves35EBCF where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar l.kleimanPicZeroProper954
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
  gonzalezRotgerThm512X6 := n.gonzalezRotgerThm512X6
  x6CoarseModuli := n.x6CoarseModuli
  elkiesX6StarEvery := n.elkiesX6StarEvery
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:171 (HDec.HSyn.OpenResearchLeaves34EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves34EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves34EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
  /-- Fontaine: the Tate module V_p(A) of an abelian variety over a finite extension of Q_p is de Rham, D_dR(V) = (B_dR (x) V)^{G_F} (printed form; Berger 2004 I.3 records it, wording read by h-leaves; Fontaine Ann. of Math. 115 (1982) / LNM 1016 (1983) numbers UNVERIFIED); Berger's B_dR = B_dR^+[1/t] matched by DeRhamPrint.TDict.bdREquivAwayT -/
  deRhamVpAbVarPrinted : _root_.DeRhamPrint.DeRhamVpAbVarPrinted
  /-- Fontaine: B_dR^{G_K} = K (Asterisque 223 (1994) Exp. II; Brinon-Conrad CMI notes 4.3-4.4), read as dim_{Q_p} B_dR^{G_F} = [F:Q_p] (printed form, dimension; locator UNVERIFIED) -/
  bdRInvariantsPrinted : _root_.DeRhamPrint.BdRInvariantsPrinted
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:298 (HDec.HSyn.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves34_of_OpenResearchLeaves35_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves34_of_OpenResearchLeaves35_eb_cf (n : OpenResearchLeaves35EBCF) (t : OpenTextbookLeaves16) : OpenResearchLeaves34EBCF where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := _root_.GRX6AbPrint.gonzalezRotgerX6Ab_of_print n.gonzalezRotgerThm512X6 n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli t.gagaMorphism t.mumfordTorsionAlgClosed
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := _root_.HDec.QMSplit.Moduli.ElkiesPrint.elkiesX6StarFunctionField_of_every n.elkiesX6StarEvery (_root_.GRX6AbPrint.x6ModuliWitness_of_coarse n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli)
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
  deRhamVpAbVarPrinted := n.deRhamVpAbVarPrinted
  bdRInvariantsPrinted := n.bdRInvariantsPrinted
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:98 (HDec.HSyn.OpenResearchLeaves33EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves33EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves33EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- Carayol 1986, Theoreme (A), at F = Q, weight 2, packaged printed form over K_{f,lambda} (r17-print): for a printed newform f (Tau Ceti Newform N 2) with number field K_f and a place lambda | l of K_f, there is a continuous, absolutely irreducible (Burnside form) rho : G_Q -> GL_2(K_{f,lambda}) (Mathlib adicCompletion), unramified at p not dividing N l with arithmetic-Frobenius trace a_p(f), whose Serre-Tate conductor exponent at every prime p != l is v_p(N). The passage to r17 (IsNewform = printed newform, extension of scalars to Qbar_l, absolute irreducibility gives semisimplicity, conductor invariance under scalar extension and isomorphism, Brauer-Nesbitt with Chebotarev) is proved in Lean. Replaces r17. -/
  carayolThmA : _root_.CarayolPrinted.CarayolThmA
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:221 (HDec.HSyn.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves33_of_OpenResearchLeaves34_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves33_of_OpenResearchLeaves34_eb_cf (n : OpenResearchLeaves34EBCF) (t : OpenTextbookLeaves16) : OpenResearchLeaves33EBCF where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := _root_.DeRhamPrint.deRhamH1AbVarT_of_leaves n.deRhamVpAbVarPrinted n.bdRInvariantsPrinted t.mumfordTorsionAlgClosed
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
  carayolThmA := n.carayolThmA
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:25 (HDec.HSyn.OpenResearchLeaves32EBCF)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves32EB` without `gamma1IntegralSpan`/`gamma1IntegralBasis` and `heckePrimeIntegralToRational` (coeff-field-tc: `eigenformCoeffFieldFinite` is proved outright). -/
structure OpenResearchLeaves32EBCF : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:145 (HDec.HSyn.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves32_of_OpenResearchLeaves33_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves32_of_OpenResearchLeaves33_eb_cf (n : OpenResearchLeaves33EBCF) : OpenResearchLeaves32EBCF where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := _root_.CarayolPrinted.carayolR17'_of_printed n.carayolThmA (_root_.eigenformCoeffFieldFinite_proof)
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  dsThm966Printed := n.dsThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2308 (HDec.HSyn.OpenResearchLeaves31EB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves30` with `mumfordGroupLawConn` replaced by `neronSchemeExtensionDedekind` (fold33-copy,
goodmodel-iso). -/
structure OpenResearchLeaves31EB : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS 9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:71 (HDec.HSyn.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf)
namespace HDec
namespace HSyn.GR9
/-- `openResearchLeaves31_of_OpenResearchLeaves32_eb`, copied from `EichlerBoundCopy` with the coeff-field-tc edits. -/
theorem openResearchLeaves31_of_OpenResearchLeaves32_eb_cf (n : OpenResearchLeaves32EBCF) : OpenResearchLeaves31EB where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  eigenformCoeffFieldFinite := _root_.eigenformCoeffFieldFinite_proof
  dsThm966Printed := n.dsThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1997 (HDec.HSyn.OpenResearchLeaves29GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves28GMEB` without `blr_7_2_1` (leaf-fold33). -/
structure OpenResearchLeaves29GMEB : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS 9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2362 (HDec.HSyn.openResearchLeaves29GM_of_OpenResearchLeaves31_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves29GMEB` (fold33-copy's copy of `OpenResearchLeaves29` with both folds) from
`OpenResearchLeaves31EB`, field by field. -/
theorem openResearchLeaves29GM_of_OpenResearchLeaves31_eb (n : OpenResearchLeaves31EB) : OpenResearchLeaves29GMEB where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1909 (HDec.HSyn.OpenResearchLeaves28GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves27GMEB` without `sga7_IX_3_3_SH`, `raynaudSemistableSH`, `mumfordGroupLaw`, `neronBaseChangeStrictHenselization`, `r7a`, `dsThm965Weak`, `dsThm966`, with the leaves `sga7_IX_3_3_SHpre`, `raynaudSemistableSHOr`, `mumfordGroupLawConn`, `blr_7_2_1`, `neronOggShafarevichSep`, `dsThm965Printed`, `eigenformCoeffFieldFinite`, `dsThm966Printed` (leaf-fold32-dict). -/
structure OpenResearchLeaves28GMEB : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form under either reading of 'semistable': Raynaud's criterion, SGA 7 I Exp. IX Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR, with the conclusion the disjunction of semistability over k(s) (general torus) and on the geometric special fibre. With geomConnOfRationalPoint (the k(s) -> kbar ascent is proved) replaces raynaudSemistableSH. -/
  raynaudSemistableSHOr : _root_.DictModels.RaynaudOr.RaynaudSemistableSHOr
  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR (GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). Replaces mumfordGroupLawConn. -/
  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind
  /-- dict-models, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 7.2 Thm 1 (numbers and hypotheses UNVERIFIED): Neron models commute with base change along an extension of DVRs of ramification index 1 with separable residue extension (here K'/K separable algebraic, A an abelian variety: specializations). The specialization to strictly henselian O1 is the old field, with no pinning of O^sh (EGA IV 18.8.8 not needed). Replaces neronBaseChangeStrictHenselization. -/
  blr_7_2_1 : _root_.DictModels.NeronBLR72.BLR_7_2_1
  /-- Serre-Tate, Ann. of Math. 88 (1968), Thm 1 (Neron-Ogg-Shafarevich criterion) over a separable closure K_s, inertia of a valuation ring of K_s acting on A(K_s)[m] (numbering UNVERIFIED) -/
  neronOggShafarevichSep : _root_.NOSSepDict.NeronOggShafarevichSep
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971; Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), printed form: for a normalized eigenform f in S_k(N, chi) (DS Def 5.8.1) with number field K_f and a prime lambda of O_{K_f} over l, a continuous rho_{f,lambda} : G_Q -> GL_2(K_{f,lambda}) (Mathlib's adicCompletion), unramified outside lN, with rho(Frob_p) having characteristic polynomial (or satisfying) x^2 - a_p x + chi(p) p^(k-1) over K_f. Either printed wording gives it by or-introduction; no coefficient dictionary (coeff-ext). -/
  dsThm965Printed : _root_.DSCoeffExt.DSThm965Printed
  /-- K_f = Q(a_n(f)) is a number field for a normalized eigenform f in S_k(N, chi), k >= 2 (DS Def 5.8.1): Diamond-Shurman Thm 6.5.1 for k = 2; Shimura 1971 Thm 3.52 with the Hecke stability of the rational structure for general k (numbers UNVERIFIED). Presupposed by DS 9.6.5 ('with number field K_f') (coeff-ext). -/
  eigenformCoeffFieldFinite : _root_.DSCoeffExt.EigenformCoeffFieldFinite
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), p. 514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2051 (HDec.HSyn.openResearchLeaves28_of_OpenResearchLeaves29_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves28GMEB` from `OpenResearchLeaves29GMEB`: `blr_7_2_1` by the contributions. -/
theorem openResearchLeaves28_of_OpenResearchLeaves29_gm_eb (n : OpenResearchLeaves29GMEB) : OpenResearchLeaves28GMEB where
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHOr := n.raynaudSemistableSHOr
  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind
  blr_7_2_1 := _root_.NeronSH.neronBaseChangeUnramifiedDVR_proof
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1814 (HDec.HSyn.OpenResearchLeaves27GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves26GMEB` without `sga3_VIB_3_10`, with the leaves `sga3_VIB_3_10_Nbhd` (leaf-fold32). -/
structure OpenResearchLeaves27GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971, Shimura 1971 Thm 7.14 for k = 2), in its weakest reading: rho_{f,lambda}(Frob_p) satisfies x^2 - a_p x + chi(p) p^(k-1) (numbering UNVERIFIED). Printed under every reading: it is the print if the print says 'satisfies', and a consequence of it (Cayley-Hamilton, DS965Weak.dsThm965Weak_of_dsThm965) if it says 'characteristic polynomial'. -/
  dsThm965Weak : _root_.DS965Weak.DSThm965Weak
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1965 (HDec.HSyn.openResearchLeaves27_of_OpenResearchLeaves28_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves27GMEB` from `OpenResearchLeaves28GMEB`: `sga7_IX_3_3_SH`, `raynaudSemistableSH`, `mumfordGroupLaw`, `neronBaseChangeStrictHenselization`, `r7a`, `dsThm965Weak`, `dsThm966` by the contributions. -/
theorem openResearchLeaves27_of_OpenResearchLeaves28_gm_eb (n : OpenResearchLeaves28GMEB) : OpenResearchLeaves27GMEB where
  r7a := _root_.NOSSepDict.neronOggShafarevich_of_sep n.neronOggShafarevichSep
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := _root_.DSThm966EV.dsThm966_of_printed n.dsThm966Printed
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := _root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := _root_.DictModels.RaynaudOr.raynaudSemistableSH_of_or n.raynaudSemistableSHOr _root_.geomConnOfRationalPoint_proof
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := _root_.DictModels.NeronBLR72.neronBaseChangeStrictHenselization_of_BLR72 n.blr_7_2_1
  sga7_IX_3_3_SH := _root_.SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre' n.sga7_IX_3_3_SHpre _root_.geomConnOfRationalPoint_proof
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  dsThm965Weak := _root_.DSCoeffExt.dsThm965Weak_of_printed n.dsThm965Printed n.eigenformCoeffFieldFinite
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1751 (HDec.HSyn.OpenResearchLeaves26GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves25GMEB` without `semistablePersistsSHcp` (persists-dvr). -/
structure OpenResearchLeaves26GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971, Shimura 1971 Thm 7.14 for k = 2), in its weakest reading: rho_{f,lambda}(Frob_p) satisfies x^2 - a_p x + chi(p) p^(k-1) (numbering UNVERIFIED). Printed under every reading: it is the print if the print says 'satisfies', and a consequence of it (Cayley-Hamilton, DS965Weak.dsThm965Weak_of_dsThm965) if it says 'characteristic polynomial'. -/
  dsThm965Weak : _root_.DS965Weak.DSThm965Weak
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1877 (HDec.HSyn.openResearchLeaves26_of_OpenResearchLeaves27_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves26GMEB` from `OpenResearchLeaves27GMEB`: `sga3_VIB_3_10` by the contributions. -/
theorem openResearchLeaves26_of_OpenResearchLeaves27_gm_eb (n : OpenResearchLeaves27GMEB) : OpenResearchLeaves26GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  dsThm965Weak := n.dsThm965Weak
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1650 (HDec.HSyn.OpenResearchLeaves25GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves24GMEB` without `dsThm965`, with the leaves `dsThm965Weak` (ds965-weak). -/
structure OpenResearchLeaves25GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- Diamond-Shurman, GTM 228 (2005), Thm 9.6.5 (k >= 2; Deligne 1971, Shimura 1971 Thm 7.14 for k = 2; numbering UNVERIFIED), per Frobenius in the form charpoly rho_{f,lambda}(Frob_p) = x^2 - a_p x + chi(p) p^(k-1) or rho_{f,lambda}(Frob_p) satisfies it: both printed wordings give it by or-introduction (DS965Weak.dsThm965Weak_of_dsThm965 is the converse direction from the charpoly form). The alpha clause rests on DS printing the theorem with the number field K_f (page check pending). -/
  dsThm965Weak : _root_.DS965Weak.DSThm965Weak
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2275 (HDec.HSyn.openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves25GMEB` from `OpenResearchLeaves26GMEB`: `semistablePersistsSHcp` by the contributions. -/
theorem openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb (n : OpenResearchLeaves26GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves25GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := _root_.SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
  dsThm965Weak := n.dsThm965Weak
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1583 (HDec.HSyn.OpenResearchLeaves24GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves23GMEB` without `babaGranathRationalAb` (leaf-fold29). -/
structure OpenResearchLeaves24GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1718 (HDec.HSyn.openResearchLeaves24_of_OpenResearchLeaves25_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves24GMEB` from `OpenResearchLeaves25GMEB`: `dsThm965` by the contributions. -/
theorem openResearchLeaves24_of_OpenResearchLeaves25_gm_eb (n : OpenResearchLeaves25GMEB) : OpenResearchLeaves24GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := _root_.DS965Weak.dsThm965_of_weak n.dsThm965Weak
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1477 (HDec.HSyn.OpenResearchLeaves23GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves22GMEB` without `elkiesX6StarPrinted`, with the leaves `elkiesX6StarFunctionField` (elkies-coord-fold). -/
structure OpenResearchLeaves23GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2226 (HDec.HSyn.openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves23GMEB` from `OpenResearchLeaves24GMEB`: `babaGranathRationalAb` by the contributions. -/
theorem openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb (n : OpenResearchLeaves24GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves23GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  babaGranathRationalAb := _root_.BGExplicit.babaGranathRationalAb_of_printed (_root_.HDec.QMSplit.Moduli.ElkiesCoord.elkiesX6StarPrinted_of_functionField n.elkiesX6StarFunctionField) t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
  elkiesX6StarFunctionField := n.elkiesX6StarFunctionField
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1405 (HDec.HSyn.OpenResearchLeaves22GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves21GMEB` without `r16`, with the leaves `r16CoreY` (r16-split). -/
structure OpenResearchLeaves22GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-elkies: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, printed form on the canonical witness: t is a coordinate on X6/W (fibres on Qbar-points = orbits of W = {1,w2,w3,w6}, defined by their moduli action), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesEquationsX6Ab (the moduli step orbit_iff_twist is proved). -/
  elkiesX6StarPrinted : _root_.HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1549 (HDec.HSyn.openResearchLeaves22_of_OpenResearchLeaves23_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves22GMEB` from `OpenResearchLeaves23GMEB`: `elkiesX6StarPrinted` by the contributions. -/
theorem openResearchLeaves22_of_OpenResearchLeaves23_gm_eb (n : OpenResearchLeaves23GMEB) : OpenResearchLeaves22GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := _root_.HDec.QMSplit.Moduli.ElkiesCoord.elkiesX6StarPrinted_of_functionField n.elkiesX6StarFunctionField
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
  r16CoreY := n.r16CoreY
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1334 (HDec.HSyn.OpenResearchLeaves21GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves20GMEB` without `rayClassCMAb`, `shimuraFamilyAb`, with the leaves `shimuraMainThmIDeligneY3AbU` (leaf-fold22). -/
structure OpenResearchLeaves21GMEB : Prop where
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-elkies: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, printed form on the canonical witness: t is a coordinate on X6/W (fibres on Qbar-points = orbits of W = {1,w2,w3,w6}, defined by their moduli action), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesEquationsX6Ab (the moduli step orbit_iff_twist is proved). -/
  elkiesX6StarPrinted : _root_.HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2192 (HDec.HSyn.openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves21GMEB` from `OpenResearchLeaves22GMEB`: `r16` by the contributions. -/
theorem openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb (n : OpenResearchLeaves22GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves21GMEB where
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := _root_.R16Split.r16_of_printed n.r16CoreY t.mumfordTorsionAlgClosed t.charPolyIndepOfEllAlgClosed
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := n.elkiesX6StarPrinted
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
  shimuraMainThmIDeligneY3AbU := n.shimuraMainThmIDeligneY3AbU
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1258 (HDec.HSyn.OpenResearchLeaves20GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves19GMEB` without `sga7_IX_3_3`, `semistableUnipotent`, with the leaves `sga7_IX_3_3_SH`, `sga7_IX_3_5_ForwardGeom` (leaf-fold20). -/
structure OpenResearchLeaves20GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-elkies: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, printed form on the canonical witness: t is a coordinate on X6/W (fibres on Qbar-points = orbits of W = {1,w2,w3,w6}, defined by their moduli action), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesEquationsX6Ab (the moduli step orbit_iff_twist is proved). -/
  elkiesX6StarPrinted : _root_.HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted
  /-- gt-sga7, printed form: SGA 7 I, Exp. IX, Cor. 3.3, second assertion (N0 x_S S' = N'0 for semistable reduction) over strictly henselian traits (number UNVERIFIED). With neronBaseChangeStrictHenselization, sga3_VIB_3_10 and geomConnOfRationalPoint replaces sga7_IX_3_3 (SGA7PersistsNF.sga7_IX_3_3_of_SH). -/
  sga7_IX_3_3_SH : _root_.SGA7PersistsNF.SGA7_IX_3_3_SH
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2157 (HDec.HSyn.openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves20GMEB` from `OpenResearchLeaves21GMEB`: `rayClassCMAb`, `shimuraFamilyAb` by the contributions. -/
theorem openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb (n : OpenResearchLeaves21GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves20GMEB where
  shimuraFamilyAb := _root_.RayClassCFT.shimuraFamilyAb_of_U n.shimuraMainThmIDeligneY3AbU
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  mumfordGroupLaw := n.mumfordGroupLaw
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  rayClassCMAb := _root_.RayClassCFT.rayClassCMAb_of_leaves n.shimuraMainThmIDeligneY3AbU t.uniformizationLeafAll t.gagaMorphism
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := n.elkiesX6StarPrinted
  sga7_IX_3_3_SH := n.sga7_IX_3_3_SH
  sga7_IX_3_5_ForwardGeom := n.sga7_IX_3_5_ForwardGeom
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1147 (HDec.HSyn.OpenResearchLeaves19GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves18GMEB` without `elkiesEquationsX6Ab`, with the leaves `elkiesX6StarPrinted` (leaf-fold18). -/
structure OpenResearchLeaves19GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
  /-- gt-elkies: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W, printed form on the canonical witness: t is a coordinate on X6/W (fibres on Qbar-points = orbits of W = {1,w2,w3,w6}, defined by their moduli action), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesEquationsX6Ab (the moduli step orbit_iff_twist is proved). -/
  elkiesX6StarPrinted : _root_.HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2122 (HDec.HSyn.openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves19GMEB` from `OpenResearchLeaves20GMEB`: `sga7_IX_3_3`, `semistableUnipotent` by the contributions. -/
theorem openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb (n : OpenResearchLeaves20GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves19GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := _root_.UnipotentForward.semistableUnipotent_of_forwardGeom n.sga7_IX_3_5_ForwardGeom _root_.ZInQ.Contrib.OneProof.MulEtale.mulEtaleAbelianScheme_proof n.neronBaseChangeStrictHenselization
  mumfordGroupLaw := n.mumfordGroupLaw
  sga7_IX_3_3 := _root_.SGA3Nbhd.NF.sga7_IX_3_3_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
  elkiesX6StarPrinted := n.elkiesX6StarPrinted
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1033 (HDec.HSyn.OpenResearchLeaves18GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves17GMEB` without `strictHenselizationPair`, with the leaves `neronBaseChangeStrictHenselization` (leaf-fold18). -/
structure OpenResearchLeaves18GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
  /-- gt-shpair, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.2 Prop. 2 (Neron models commute with strict henselization), for unramified strictly henselian extensions with separable residue extension, which pin the base to O^sh (locator UNVERIFIED). Replaces strictHenselizationPair; the commutative algebra (GapSHPair.shPair) is proved. -/
  neronBaseChangeStrictHenselization : _root_.GapSHPair.NeronBaseChangeStrictHenselization
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1223 (HDec.HSyn.openResearchLeaves18_of_OpenResearchLeaves19_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves18GMEB` from `OpenResearchLeaves19GMEB`: `elkiesEquationsX6Ab` by the contributions. -/
theorem openResearchLeaves18_of_OpenResearchLeaves19_gm_eb (n : OpenResearchLeaves19GMEB) : OpenResearchLeaves18GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := n.semistableUnipotent
  mumfordGroupLaw := n.mumfordGroupLaw
  sga7_IX_3_3 := n.sga7_IX_3_3
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  elkiesEquationsX6Ab := _root_.HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed n.elkiesX6StarPrinted
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
  neronBaseChangeStrictHenselization := n.neronBaseChangeStrictHenselization
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:918 (HDec.HSyn.OpenResearchLeaves17GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves16GMEB` without `gonzalezRotgerCountX6Ab`, with the leaves `gonzalezRotgerProp56X6` (gt-grcount-fold). -/
structure OpenResearchLeaves17GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED. -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerProp56X6 : _root_.GR56.R5fpCountLe
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:1112 (HDec.HSyn.openResearchLeaves17_of_OpenResearchLeaves18_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves17GMEB` from `OpenResearchLeaves18GMEB`: `strictHenselizationPair` by the contributions. -/
theorem openResearchLeaves17_of_OpenResearchLeaves18_gm_eb (n : OpenResearchLeaves18GMEB) : OpenResearchLeaves17GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := n.semistableUnipotent
  mumfordGroupLaw := n.mumfordGroupLaw
  sga7_IX_3_3 := n.sga7_IX_3_3
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  elkiesEquationsX6Ab := n.elkiesEquationsX6Ab
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  strictHenselizationPair := _root_.GapSHPair.strictHenselizationPair_of_neron n.neronBaseChangeStrictHenselization
  gonzalezRotgerProp56X6 := n.gonzalezRotgerProp56X6
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:800 (HDec.HSyn.OpenResearchLeaves16GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves15GMEB` without `blr_1_2_4`, `igusaPsi4`, `igusaChi10` (leaf-fold16). -/
structure OpenResearchLeaves16GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED. -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:998 (HDec.HSyn.openResearchLeaves16_of_OpenResearchLeaves17_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves16GMEB` from `OpenResearchLeaves17GMEB`: `gonzalezRotgerCountX6Ab` by the contributions. -/
theorem openResearchLeaves16_of_OpenResearchLeaves17_gm_eb (n : OpenResearchLeaves17GMEB) : OpenResearchLeaves16GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := n.semistableUnipotent
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerProp56X6
  mumfordGroupLaw := n.mumfordGroupLaw
  sga7_IX_3_3 := n.sga7_IX_3_3
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  elkiesEquationsX6Ab := n.elkiesEquationsX6Ab
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  strictHenselizationPair := n.strictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:675 (HDec.HSyn.OpenResearchLeaves15GMEB)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves14GMEB` without `egaIV_8_10_5_openImm` (gt-ega). -/
structure OpenResearchLeaves15GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED. -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:880 (HDec.HSyn.openResearchLeaves15_of_OpenResearchLeaves16_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves15GMEB` from `OpenResearchLeaves16GMEB`: `blr_1_2_4`, `igusaPsi4`, `igusaChi10` by the contributions. -/
theorem openResearchLeaves15_of_OpenResearchLeaves16_gm_eb (n : OpenResearchLeaves16GMEB) : OpenResearchLeaves15GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  igusaPsi4 := _root_.GapTheta.igusaPsi4_proof
  igusaChi10 := _root_.GapTheta.igusaChi10_proof
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := n.semistableUnipotent
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerCountX6Ab
  mumfordGroupLaw := n.mumfordGroupLaw
  blr_1_2_4 := _root_.GapBLR.blr_1_2_4
  sga7_IX_3_3 := n.sga7_IX_3_3
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  elkiesEquationsX6Ab := n.elkiesEquationsX6Ab
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  strictHenselizationPair := n.strictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:585 (HDec.HSyn.OpenResearchLeaves14GMEB)
namespace HDec
namespace HSyn.GR9
/-- **The research leaves still open** (leaf-fold14, reduct fold): x6-fold's `OpenResearchLeaves13` without
`semistableReductionDVR`, `raynaudSemistable` and `semistablePersistsDVR` (reduct-b), with
`raynaudSemistableSH`, `semistablePersistsSHcp` and `strictHenselizationPair` added. 35 fields. -/
structure OpenResearchLeaves14GMEB : Prop where
  /-- H-139, printed form: Shimura's family over the fine moduli scheme of abelian schemes. Replaces
  `shimuraFamily`. -/
  shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6Ab : _root_.GR56.R5fpCountLe
  /-- gt-rigidity, rigid-prune (leaf-fold23): **Mumford's GIT Thm 6.14 over a base** (on each connected component;
  numbers UNVERIFIED): a proper smooth geometrically connected family over a locally noetherian `S` with a section
  `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with
  identity `e`. Replaces `mumfordRigidityCore`, which also asked Cor. 6.4 (not needed: rigid-prune proves that each
  `ι(a)` is a homomorphism from the field points). -/
  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which
  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`
  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR
  /-- c-to-printed, printed form: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 4 (over a Dedekind
  domain, a smooth separated model of finite type is a Néron model iff its localizations at the closed points are;
  locator UNVERIFIED). Replaces `neronLocalizesDVR`. -/
  blr_1_2_4 : _root_.CToPrinted.BLR_1_2_4
  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)
  /-- c-to-printed, printed form: SGA 7 IX 3.3 (`N⁰ ⊗ R' ≅ N'⁰` for semistable reduction; locator UNVERIFIED). -/
  sga7_IX_3_3 : _root_.CToPrinted.SGA7_IX_3_3
  /-- c-to-printed, printed form: EGA IV 8.10.5, open immersions descend through limits (locator UNVERIFIED). -/
  egaIV_8_10_5_openImm : _root_.CToPrinted.EGAIV_8_10_5_openImm
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb
  /-- reduct-glue (reduct-b), printed form, strictly henselian base: Raynaud's criterion, SGA 7 I Exp. IX
  Prop. 4.7 (number UNVERIFIED) over a strictly henselian DVR `O`: if `m ≥ 3` is invertible in `O` and the points of
  order `m` are rational over `K`, then `A` has semistable Néron models at `O`. Unrestricted in `K` and the residue
  field (`r6` is stated over every field); reading risk: if the print assumes an algebraically closed residue field,
  this form is stronger than the print for imperfect residue fields. Replaces, with `strictHenselizationPair`,
  `raynaudSemistable` and (by K1) `semistableReductionDVR`. -/
  raynaudSemistableSH : _root_.ReductGlue.RaynaudSemistableSH
  /-- reduct-b, printed form, restricted: SGA 7 I Exp. IX Cor. 3.3, first assertion (number UNVERIFIED), over a
  strictly henselian DVR of a field of characteristic `0` with perfect, hence algebraically closed, residue field
  (a specialization of every reading of the print). With `strictHenselizationPair` replaces `semistablePersistsDVR`
  at its two uses, SS1 and SS3, which are over number fields. -/
  semistablePersistsSHcp : _root_.ReductB.SemistablePersistsSHcp
  /-- reduct-glue, composite (GLUE): strict henselization along a finite extension of DVRs (EGA IV₄ 18.8.10 and
  18.6.8, Stacks 05WR) with Néron models commuting with it (BLR §1.2 Prop. 2); numbers UNVERIFIED. -/
  strictHenselizationPair : _root_.ReductGlue.StrictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:761 (HDec.HSyn.openResearchLeaves14_of_OpenResearchLeaves15_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenResearchLeaves14GMEB` from `OpenResearchLeaves15GMEB`: `egaIV_8_10_5_openImm` by the contributions. -/
theorem openResearchLeaves14_of_OpenResearchLeaves15_gm_eb (n : OpenResearchLeaves15GMEB) : OpenResearchLeaves14GMEB where
  shimuraFamilyAb := n.shimuraFamilyAb
  igusaPsi4 := n.igusaPsi4
  igusaChi10 := n.igusaChi10
  r7a := n.r7a
  r9a := n.r9a
  r9b := n.r9b
  hodgeTateDecompAbVar := n.hodgeTateDecompAbVar
  deRhamH1AbVarT := n.deRhamH1AbVarT
  r11r12 := n.r11r12
  eigenformHTNew := n.eigenformHTNew
  dsThm965 := n.dsThm965
  dsThm966 := n.dsThm966
  r16 := n.r16
  r17 := n.r17
  bostLowerBound := n.bostLowerBound
  javanpeykarBound := n.javanpeykarBound
  pazukiCor13Upper := n.pazukiCor13Upper
  gaudronRemondThm14 := n.gaudronRemondThm14
  semistableUnipotent := n.semistableUnipotent
  gonzalezRotgerCountX6Ab := n.gonzalezRotgerCountX6Ab
  mumfordGroupLaw := n.mumfordGroupLaw
  blr_1_2_4 := n.blr_1_2_4
  sga7_IX_3_3 := n.sga7_IX_3_3
  egaIV_8_10_5_openImm := _root_.ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof
  babaGranathRationalAb := n.babaGranathRationalAb
  gonzalezRotgerX6Ab := n.gonzalezRotgerX6Ab
  elkiesEquationsX6Ab := n.elkiesEquationsX6Ab
  rayClassCMAb := n.rayClassCMAb
  raynaudSemistableSH := n.raynaudSemistableSH
  semistablePersistsSHcp := n.semistablePersistsSHcp
  strictHenselizationPair := n.strictHenselizationPair
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2261 (HDec.HSyn.SGRFold.research14_of_open29_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
namespace SGRFold
/-- The top bundles converted down to generation 14 (research), as the stack `sixContactMin_of_open29_hf_gm` …
`sixContactMin_of_open18_hf_gm` does. -/
theorem research14_of_open29_hf_gm_eb (r : OpenResearchLeaves22GMEB) (t : OpenTextbookLeaves11HF) : OpenResearchLeaves14GMEB :=
  openResearchLeaves14_of_OpenResearchLeaves15_gm_eb <| openResearchLeaves15_of_OpenResearchLeaves16_gm_eb <|
    openResearchLeaves16_of_OpenResearchLeaves17_gm_eb <| openResearchLeaves17_of_OpenResearchLeaves18_gm_eb <|
    openResearchLeaves18_of_OpenResearchLeaves19_gm_eb <| openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb
      (openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb (openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb r t) t) t
end SGRFold
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2938 (HDec.HSyn.x6Rows_of_open14_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **The two `X₆` rows from the new bundles** (the term of `x6Rows_of_open13`). pi0-fold: the weak row
`R1R2fpRepW` from `x6Rows_of_leavesW`, whose base witness is González–Rotger's (`GonzalezRotgerX6`); the added leaves
`deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` are no longer read. -/
theorem x6Rows_of_open14_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves12PZ) :
    LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw
  QMSplit.Moduli.x6Rows_of_leavesW
    { t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab_gl hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab_gl hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab_gl hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab_gl hR).mpr r.elkiesEquationsX6Ab }
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3214 (HDec.HSyn.SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
namespace SGRFold
/-- **`HeckeSqrtBranchAny` from the top bundles**: sgr-direct's `heckeSqrtBranchAny_of_elkies` with Elkies' printed
model (`elkiesX6StarPrinted`), `R1R2fp` (generation 14's `x6Rows_of_open14_hf_gm_pz_eb`) and T5. -/
theorem heckeSqrtBranchAny_of_open29_hf_gm_pz_eb (r : OpenResearchLeaves22GMEB) (t : OpenTextbookLeaves11HF)
    (l : OpenAddedLeaves17PZ) : SGRDirect.HeckeSqrtBranchAny :=
  SGRDirect.heckeSqrtBranchAny_of_elkies
    (LeafAdopt.R1R2fp_of_rep (x6Rows_of_open14_hf_gm_pz_eb (research14_of_open29_hf_gm_eb r t)
      (openTextbookLeaves10_of_OpenTextbookLeaves11_hf t) (_root_.HDec.HSyn.SGRFold.added12_of_open29_hf_pz t l)).1)
    (_root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed) r.elkiesX6StarPrinted
end SGRFold
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3229 (HDec.HSyn.openGlue7_of_OpenGlue8_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- `OpenGlue7` from `OpenGlue8`: `HeckeSqrtBranchAny` by the contribution (Elkies' printed model, through
generation 22 of the research bundle). -/
theorem openGlue7_of_OpenGlue8_hf_gm_pz_eb (r : OpenResearchLeaves25GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ)
    (g : OpenGlue8) : OpenGlue7 where
  nvLocalInertia := g.nvLocalInertia
  heckeSqrtBranchAny := SGRFold.heckeSqrtBranchAny_of_open29_hf_gm_pz_eb
    (openResearchLeaves22_of_OpenResearchLeaves23_gm_eb
      (openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb (openResearchLeaves24_of_OpenResearchLeaves25_gm_eb r) t)) t l
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2956 (HDec.HSyn.addedLeaves9_of_open14_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- leaf-fold10's added-leaf bundle from leaf-fold14's (the composite of `addedLeaves11_of_open12`,
`addedLeaves10_of_open11` and `addedLeaves9_of_open10`). -/
theorem addedLeaves9_of_open14_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves12PZ) :
    OpenAddedLeaves9PZ where
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := (x6Rows_of_open14_hf_gm_pz_eb r t l).2
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  valenceFormulaCocompactEq := l.valenceFormulaCocompactEq
  shimizuCovolumeO1 := l.shimizuCovolumeO1
  igusaCMValue24 := _root_.CM24.igusaCMValue24_field
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2084 (HDec.HSyn.raynaudSemistable_of14_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- **SGA 7 IX 4.7 over a DVR** (the old field `raynaudSemistable`) from the strictly henselian printed leaf, the
pair and the textbook field `mulEtaleAbelianScheme` (reduct-b, Route B). -/
theorem raynaudSemistable_of14_hf_gm_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) :
    _root_.ReductSplit.RaynaudSemistable :=
  _root_.ReductB.raynaudSemistable_of_SH_pair r.raynaudSemistableSH r.strictHenselizationPair
    t.mulEtaleAbelianScheme
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2096 (HDec.HSyn.semistableReductionDVR_of14_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- **SGA 7 IX 3.6 over a DVR** (the old field `semistableReductionDVR`) by reduct-b's K1 from 4.7, Mumford's torsion
count and `[m]` étale (textbook fields). -/
theorem semistableReductionDVR_of14_hf_gm_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) :
    _root_.ReductSplit.SemistableReductionDVR :=
  _root_.ReductB.semistableReductionDVR_of_raynaud (raynaudSemistable_of14_hf_gm_eb r t) t.mumfordTorsionAlgClosed
    t.mulEtaleAbelianScheme
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3065 (HDec.HSyn.ss1_ss3_of14NF_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **SS1 and SS3** (r6-nf; the reroute of `ss1_ss3_of14`, docs/research/neron-dvr.md §3.2): neron-dvr's
`GapNeron.ss1_ss3_of_cpNF`, with the Néron field at number fields from N1. -/
theorem ss1_ss3_of14NF_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves12PZ) :
    _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists :=
  _root_.GapNeron.ss1_ss3_of_cpNF r.semistablePersistsSHcp r.strictHenselizationPair (semistableReductionDVR_of14_hf_gm_eb r t)
    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists)
    (_root_.ReductGlue.semistableLocalGlobal_leaf (_root_.CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4))
    (semistableAlmostAll_of10_pz (addedLeaves9_of_open14_hf_gm_pz_eb r t l))
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2108 (HDec.HSyn.raynaudCriterionNF_of14_hf_gm_eb)
namespace HDec
namespace HSyn.GR9
/-- **r6 at number fields** (r6-nf) from leaf-fold14's bundles: neron-dvr's `GapNeron.raynaudCriterion_leavesNF`
with the Néron field at number fields proved from the textbook field N1 (`GapNeron.neronSchemeModelExistsNF`),
replacing `ReductGlue.raynaudCriterion_leaves … r.neronSchemeModelExistsDVR …` (BLR 1.4/3 over every DVR). -/
theorem raynaudCriterionNF_of14_hf_gm_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) :
    PkgI2.RaynaudCriterionNF.{0} :=
  _root_.GapNeron.raynaudCriterion_leavesNF (raynaudSemistable_of14_hf_gm_eb r t) r.semistableUnipotent
    (_root_.GapNeron.neronSchemeModelExistsNF t.neronSchemeExtensionExists) t.mumfordTorsionAlgClosed
    t.mulEtaleAbelianScheme
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:418 (HDec.HSyn.OpenResearchLeaves9EB)
namespace HDec
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits
/-- **The research leaves still open** (leaf-fold9): leaf-fold8's `OpenResearchLeaves8EB` without `r1rec`, `r5`
(proved from `r1r2`, `r1rec_of_rep`, `r5fp_of_rep`) and `r15` (proved from `dsThm966`, modular-split's
`deligneSerreConseq_of_ds`), and `r7b`, `r8` replaced by reduct-split's four published-form leaves
(`ReductSplit.serreTatePotentialGood_final`, `grothendieckMonodromy_final'`), and `r5count` replaced by shimura-split's
`GonzalezRotgerCountX6` (`ShimuraSplit.r5fpCount_of_points`). 30 fields. -/
structure OpenResearchLeaves9EB : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r6 : PkgI2.RaynaudCriterionNF.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  gonzalezRotgerCountX6 : _root_.GR56.R5fpCountLe
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2976 (HDec.HSyn.researchLeaves9_of_open14_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- leaf-fold9's research bundle from leaf-fold14's (the composite of `researchLeaves12_of_open13`,
`researchLeaves11_of_open12`, `researchLeaves10_of_open11` and `researchLeaves9_of_open10`, with the three reduct
fields replaced by reduct-b's theorems). r6-nf: r6 (at number fields) and SS1, SS3 are arguments, supplied in
`sixContactMin_of_open20_hf_gm_pz_eb` (TailZ26) by `raynaudCriterionNF_of14_hf_gm_eb` and `ss1_ss3_of14NF_hf_gm_pz_eb` from neron-dvr's
number-field Néron theorem (N1 alone), which replaced BLR 1.4/3 over every DVR. -/
theorem researchLeaves9_of_open14_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves12PZ)
    (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :
    OpenResearchLeaves9EB where
  r1r2 := (x6Rows_of_open14_hf_gm_pz_eb r t l).1
  shimuraFamily := (_root_.LeafQM.AV.R1UnivRigid.shimuraFamily_iff_ab_gl
      (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)).mpr
    r.shimuraFamilyAb
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r6 := h6
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := hSS.1
  semistableNeronBaseChange := _root_.SGA3Nbhd.semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 t.geomConnOfRationalPoint
  semistablePersists := hSS.2
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
  gonzalezRotgerCountX6 := r.gonzalezRotgerCountX6Ab
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:370 (HDec.HSyn.OpenResearchLeaves8EB)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The research leaves still open** (leaf-fold8): leaf-fold7's `OpenResearchLeaves7EB` with the six height rows
`r18`-`r22`, `h5fin` replaced by height-split's leaves over the published stable height. 31 fields. -/
structure OpenResearchLeaves8EB : Prop where
  r1r2 : LeafAdopt.R1R2fpRepW
  shimuraFamily : QMSplit.Moduli.ShimuraFamily
  r1rec : LeafQM.AV.R1rec
  igusaPsi4 : QMSplit.Theta.IgusaPsi4
  igusaChi10 : QMSplit.Theta.IgusaChi10
  r5 : LeafQM.AV.R5fp
  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only
  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's
  count field of the same name. -/
  r5count : _root_.GR56.R5fpCountLe
  r6 : PkgI2.RaynaudCriterionNF.{0}
  r7a : _root_.PkgI2.NeronOggShafarevich.{0}
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  dsThm965 : _root_.ZInQ.Contrib.HodgeSplit.DSThm965
  dsThm966 : _root_.ZInQ.Contrib.HodgeSplit.DSThm966
  r15 : DeligneSerreConseq
  r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, SS1: Grothendieck's semistable reduction theorem, global form (SGA 7 IX 3.6). -/
  semistableReductionThm : _root_.ZInQ.HeightSplit.SemistableReductionThm
  /-- height-split, SS2: base change of the identity component in the semistable case (SGA 7 IX 3.3). -/
  semistableNeronBaseChange : _root_.ZInQ.HeightSplit.SemistableNeronBaseChange
  /-- height-split, SS3: semistability persists under finite extension (SGA 7 IX 3.3). -/
  semistablePersists : _root_.ZInQ.HeightSplit.SemistablePersists
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.GRBostBound
  /-- height-split, H-14: Javanpeykar 2014 Thm 1.1.1 for curves over `K` with a `K`-rational Belyi function,
  replaces `r18`. -/
  javanpeykarBound : _root_.ZInQ.HeightSplit.JavanpeykarBound
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- height-split, H-15: Gaudron–Rémond 2014 Thm 1.4 over the published stable height, replaces `r19`. -/
  gaudronRemondThm14 : _root_.ZInQ.HeightSplit.GaudronRemondThm14
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:545 (HDec.HSyn.researchLeaves8_of_open9_hf_eb)
namespace HDec
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits
/-- leaf-fold8's research bundle from leaf-fold9's. -/
theorem researchLeaves8_of_open9_hf_eb (r : OpenResearchLeaves9EB) (t : OpenTextbookLeaves9HF) : OpenResearchLeaves8EB where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r1rec_of_rep r.r1r2
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r5fp_of_rep r.r1r2
  r5count := r.gonzalezRotgerCountX6
  r6 := r.r6
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := _root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966
  r16 := r.r16
  r17 := r.r17
  semistableReductionThm := r.semistableReductionThm
  semistableNeronBaseChange := r.semistableNeronBaseChange
  semistablePersists := r.semistablePersists
  bostLowerBound := r.bostLowerBound
  javanpeykarBound := r.javanpeykarBound
  pazukiCor13Upper := r.pazukiCor13Upper
  gaudronRemondThm14 := r.gaudronRemondThm14
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:496 (HDec.HSyn.r20Lower_of8_hf_eb)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The lower half of R20** (sem-prune) from the lower half of `faltingsLemma5BC` and the fields
`heightRows_of8` uses for R20 (N1 from `neronSchemeExtensionExists`, SS1, SS2, SS3). -/
theorem r20Lower_of8_hf_eb (r : OpenResearchLeaves8EB) (t : OpenTextbookLeaves8HF)
    (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) : G0Split.R20Lower :=
  _root_.ZInQ.HeightSplit.r20Lower_of_leaves' hF5
    (_root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists)
    r.semistableReductionThm r.semistableNeronBaseChange r.semistablePersists
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2445 (HDec.HSyn.addedLeaves7_of_open8_pz_eb)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold7's added bundle from leaf-fold8's. -/
theorem addedLeaves7_of_open8_pz_eb (r : OpenResearchLeaves8EB) (l : OpenAddedLeaves8PZ) : OpenAddedLeaves7PZ where
  qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves
    (QMSplit.Theta.thetaModularity_of r.igusaPsi4 r.igusaChi10) l.valenceFormulaCocompactEq l.shimizuCovolumeO1
    l.igusaCMValue24
  qmCentralizerCMC := l.qmCentralizerCMC
  tateTwistInvariants := l.tateTwistInvariants
  axSenTate := l.axSenTate
  t09SymmIsogenyExists := l.t09SymmIsogenyExists
  milneIsogenyQuasiInverse := l.milneIsogenyQuasiInverse
  x6ConicModel := l.x6ConicModel
  y3Connected := l.y3Connected
  zariskiConnectedness := _root_.ZariskiConn.ZariskiConnectedness_proof.{0}
  valenceFormulaGammaStar :=
    LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves l.valenceFormulaCocompactEq l.shimizuCovolumeO1
  egaIV_8_8_2_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof
  egaIV_8_10_5_xii := l.egaIV_8_10_5_xii
  egaIV_17_7_8_ii := _root_.ZInQ.Contrib.SpreadOut.EGAIV_17_7_8_ii_proof
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:468 (HDec.HSyn.heightRowsNo20_of8_hf_eb)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **The five height rows other than R20** (sem-prune), from the fields `heightRows_of8` reads except
`faltingsLemma5BC`: the proofs of `ZInQ.HeightSplit.heightRows_of`'s other components. -/
theorem heightRowsNo20_of8_hf_eb (r : OpenResearchLeaves8EB) (t : OpenTextbookLeaves8HF) :
    _root_.ZInQ.LeafPush2.R18_Javanpeykar ∧ _root_.ZInQ.DefFaltings.R19_GaudronRemond ∧
      _root_.ZInQ.DefFaltings.R21_Bost ∧ _root_.ZInQ.LeafPush2.R22_Pazuki ∧
      _root_.ZInQ.DefFaltings.StableHeightFinite :=
  have hN1 := _root_.ZInQ.Contrib.NeronC.neronModelExists_of_extension t.neronSchemeExtensionExists
  have gl := _root_.ZInQ.HeightGlue.heightGlue_of_t35
    (_root_.AvSplit.Final.h38 t.uniformizationLeafAll t.mumfordTorsionAlgClosed)
  have hMet := _root_.ZInQ.HeightSplit.neronMetrizable_of gl.an3Exists gl.unifDim gl.metrize
  ⟨_root_.ZInQ.HeightSplit.r18_of_leaves r.javanpeykarBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange hMet,
    _root_.ZInQ.HeightSplit.r19_of_leaves r.gaudronRemondThm14 hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.BostGR9.r21_of_grBost' r.bostLowerBound hN1 r.semistableReductionThm
      r.semistableNeronBaseChange gl.an3Unique,
    _root_.ZInQ.HeightSplit.r22_of_upper r.pazukiCor13Upper hN1 r.semistableReductionThm
      r.semistableNeronBaseChange,
    _root_.ZInQ.HeightSplit.stableHeightFinite_of' hN1 r.semistableReductionThm r.semistableNeronBaseChange
      hMet gl.an3Unique⟩
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:511 (HDec.HSyn.researchLeaves7_of_open8_hf_eb)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- leaf-fold7's research bundle from leaf-fold8's. -/
theorem researchLeaves7_of_open8_hf_eb (r : OpenResearchLeaves8EB) (t : OpenTextbookLeaves8HF) : OpenResearchLeaves7EB where
  r1r2 := r.r1r2
  shimuraFamily := r.shimuraFamily
  r1rec := r.r1rec
  igusaPsi4 := r.igusaPsi4
  igusaChi10 := r.igusaChi10
  r5 := r.r5
  r5count := r.r5count
  r6 := r.r6
  r7a := r.r7a
  r9a := r.r9a
  r9b := r.r9b
  hodgeTateDecompAbVar := r.hodgeTateDecompAbVar
  deRhamH1AbVarT := r.deRhamH1AbVarT
  r11r12 := r.r11r12
  eigenformHTNew := r.eigenformHTNew
  dsThm965 := r.dsThm965
  dsThm966 := r.dsThm966
  r15 := r.r15
  r16 := r.r16
  r17 := r.r17
  r18 := r18_lf8 (heightRowsNo20_of8_hf_eb r t).1
  r19 := (heightRowsNo20_of8_hf_eb r t).2.1
  r21 := (heightRowsNo20_of8_hf_eb r t).2.2.1
  r22 := r22_lf8 (heightRowsNo20_of8_hf_eb r t).2.2.2.1
  h5fin := (heightRowsNo20_of8_hf_eb r t).2.2.2.2
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2879 (HDec.HSyn.sixContactMin_of_open8_hf_pz_eb)
namespace HDec
set_option maxHeartbeats 1000000
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
/-- **G0 with only the open leaves and the open glue** (leaf-fold8; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves8EB` (31), `OpenTextbookLeaves8HF` (20), `OpenAddedLeaves8PZ` (14)
and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold8.md` §2. -/
theorem sixContactMin_of_open8_hf_pz_eb (r : OpenResearchLeaves8EB) (t : OpenTextbookLeaves8HF) (l : OpenAddedLeaves8PZ)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open7_hf_pz_eb (researchLeaves7_of_open8_hf_eb r t) (textbookLeaves7_of_open8_hf t) (addedLeaves7_of_open8_pz_eb r l) g
    (r20Lower_of8_hf_eb r t hF5) hYu hθ
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2895 (HDec.HSyn.sixContactMin_of_open9_hf_pz_eb)
namespace HDec
namespace HSyn.GR9
open CategoryTheory AlgebraicGeometry Limits
/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9EB` (30), `OpenTextbookLeaves9HF` (18), leaf-fold8's
`OpenAddedLeaves8PZ` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9_hf_pz_eb (r : OpenResearchLeaves9EB) (t : OpenTextbookLeaves9HF) (l : OpenAddedLeaves8PZ)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open8_hf_pz_eb (researchLeaves8_of_open9_hf_eb r t) (textbookLeaves8_of_open9_hf t) l g hF5 hYu hθ
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2909 (HDec.HSyn.sixContactMin_of_open10_hf_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9EB` (30), `OpenTextbookLeaves10HF` (17),
leaf-fold8's `OpenAddedLeaves8PZ` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every
field is `docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open10_hf_pz_eb (r : OpenResearchLeaves9EB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves8PZ)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open9_hf_pz_eb r (textbookLeaves9_of_open10_hf t) l g hF5 hYu hθ
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:2923 (HDec.HSyn.sixContactMin_of_open11_hf_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold10; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from leaf-fold9's `OpenResearchLeaves9EB` (30), `OpenTextbookLeaves10HF` (17),
`OpenAddedLeaves9PZ` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold10.md` §2. -/
theorem sixContactMin_of_open11_hf_pz_eb (r : OpenResearchLeaves9EB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves9PZ)
    (g : OpenGlue7) (hF5 : _root_.ZInQ.HeightSplit.FaltingsLemma5BCLower) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open10_hf_pz_eb r t (addedLeaves8_of_open9_pz l hY3) g hF5 hYu hθ
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3017 (HDec.HSyn.sixContactMin_of_open17_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold14, reduct fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14GMEB` (35), `OpenTextbookLeaves10HF` (15), `OpenAddedLeaves12PZ` (14) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open17_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves12PZ)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open11_hf_pz_eb (researchLeaves9_of_open14_hf_gm_pz_eb r t l h6 hSS) t (addedLeaves9_of_open14_hf_gm_pz_eb r t l) g
    (_root_.ReductSplit.faltingsLemma5BCLower_final _root_.GapHeight.faltingsLemma5Lower) hYu hY3 hθ
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3036 (HDec.HSyn.sixContactMin_of_open18_hf_gm_pz_eb)
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold14; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves14GMEB` (35), `OpenTextbookLeaves10HF` (15), `OpenAddedLeaves13PZ` (17) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open18_hf_gm_pz_eb (r : OpenResearchLeaves14GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves13PZ)
    (g : OpenGlue7) (hYu : QMLattice.YuB6Alg) (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)
    (hY3 : TSHecke.Y3Connected)
    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=
  sixContactMin_of_open17_hf_gm_pz_eb r t (addedLeaves12_of_open13_pz l) g hYu h6 hSS hY3 hθ
end HSyn.GR9
end HDec
end

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3052 (HDec.HSyn.sixContactMin_of_open19_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (gt-ega; generated). -/
theorem sixContactMin_of_open19_hf_gm_pz_eb (r : OpenResearchLeaves15GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves13PZ) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (h6 : PkgI2.RaynaudCriterionNF.{0})
    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open18_hf_gm_pz_eb (openResearchLeaves14_of_OpenResearchLeaves15_gm_eb r) t l g hYu h6 hSS hY3
    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3079 (HDec.HSyn.sixContactMin_of_open20_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold16; generated; r6-nf: supplies r6 at number fields
and SS1/SS3 to `sixContactMin_of_open19_hf_gm_pz_eb`). -/
theorem sixContactMin_of_open20_hf_gm_pz_eb (r : OpenResearchLeaves16GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves14PZ) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open19_hf_gm_pz_eb (openResearchLeaves15_of_OpenResearchLeaves16_gm_eb r) t (openAddedLeaves13_of_OpenAddedLeaves14_pz l) g hYu
    (raynaudCriterionNF_of14_hf_gm_eb
      (openResearchLeaves14_of_OpenResearchLeaves15_gm_eb (openResearchLeaves15_of_OpenResearchLeaves16_gm_eb r)) t)
    (ss1_ss3_of14NF_hf_gm_pz_eb (openResearchLeaves14_of_OpenResearchLeaves15_gm_eb (openResearchLeaves15_of_OpenResearchLeaves16_gm_eb r)) t
      (addedLeaves12_of_open13_pz (openAddedLeaves13_of_OpenAddedLeaves14_pz l))) hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3094 (HDec.HSyn.sixContactMin_of_open21_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (gt-grcount-fold; generated). -/
theorem sixContactMin_of_open21_hf_gm_pz_eb (r : OpenResearchLeaves17GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves14PZ) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open20_hf_gm_pz_eb (openResearchLeaves16_of_OpenResearchLeaves17_gm_eb r) t l g hYu hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3104 (HDec.HSyn.sixContactMin_of_open22_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open22_hf_gm_pz_eb (r : OpenResearchLeaves18GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves14PZ) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open21_hf_gm_pz_eb (openResearchLeaves17_of_OpenResearchLeaves18_gm_eb r) t l g hYu hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3114 (HDec.HSyn.sixContactMin_of_open23_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open23_hf_gm_pz_eb (r : OpenResearchLeaves19GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves14PZ) (g : OpenGlue7) (hYu : QMLattice.YuB6Alg)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open22_hf_gm_pz_eb (openResearchLeaves18_of_OpenResearchLeaves19_gm_eb r) t l g hYu hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3124 (HDec.HSyn.sixContactMin_of_open24_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open24_hf_gm_pz_eb (r : OpenResearchLeaves19GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves15PZ) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open23_hf_gm_pz_eb r t (openAddedLeaves14_of_OpenAddedLeaves15_hf_pz l t) g
    (QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed) hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3135 (HDec.HSyn.sixContactMin_of_open25_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold18; generated). -/
theorem sixContactMin_of_open25_hf_gm_pz_eb (r : OpenResearchLeaves19GMEB) (t : OpenTextbookLeaves10HF) (l : OpenAddedLeaves16PZ) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open24_hf_gm_pz_eb r t (openAddedLeaves15_of_OpenAddedLeaves16_pz l) g hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3145 (HDec.HSyn.sixContactMin_of_open26_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold19; generated). -/
theorem sixContactMin_of_open26_hf_gm_pz_eb (r : OpenResearchLeaves19GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves16PZ) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open25_hf_gm_pz_eb r (openTextbookLeaves10_of_OpenTextbookLeaves11_hf t) l g hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3155 (HDec.HSyn.sixContactMin_of_open27_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold20; generated). -/
theorem sixContactMin_of_open27_hf_gm_pz_eb (r : OpenResearchLeaves20GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves16PZ) (g : OpenGlue7)
    (hY3 : TSHecke.Y3Connected) : ZInQ.SixContactMin :=
  sixContactMin_of_open26_hf_gm_pz_eb (openResearchLeaves19_of_OpenResearchLeaves20_hf_gm_eb r t) t l g hY3
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3165 (HDec.HSyn.sixContactMin_of_open28_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold22; generated). dcy3-fold: supplies `TSHecke.Y3Connected`
(threaded down to `addedLeaves8_of_open9_pz`) by `DCY3Used.y3Connected_of_leaves` from two research fields. -/
theorem sixContactMin_of_open28_hf_gm_pz_eb (r : OpenResearchLeaves21GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open27_hf_gm_pz_eb (openResearchLeaves20_of_OpenResearchLeaves21_hf_gm_eb r t) t (openAddedLeaves16_of_OpenAddedLeaves17_pz l) g
    (_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)
      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3177 (HDec.HSyn.sixContactMin_of_open29_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (r16-split; generated). -/
theorem sixContactMin_of_open29_hf_gm_pz_eb (r : OpenResearchLeaves22GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open28_hf_gm_pz_eb (openResearchLeaves21_of_OpenResearchLeaves22_hf_gm_eb r t) t l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3186 (HDec.HSyn.sixContactMin_of_open30_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (elkies-coord-fold; generated). -/
theorem sixContactMin_of_open30_hf_gm_pz_eb (r : OpenResearchLeaves23GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29_hf_gm_pz_eb (openResearchLeaves22_of_OpenResearchLeaves23_gm_eb r) t l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3195 (HDec.HSyn.sixContactMin_of_open31_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold29; generated). -/
theorem sixContactMin_of_open31_hf_gm_pz_eb (r : OpenResearchLeaves24GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open30_hf_gm_pz_eb (openResearchLeaves23_of_OpenResearchLeaves24_hf_gm_eb r t) t l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3204 (HDec.HSyn.sixContactMin_of_open32_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (ds965-weak; generated). -/
theorem sixContactMin_of_open32_hf_gm_pz_eb (r : OpenResearchLeaves25GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open31_hf_gm_pz_eb (openResearchLeaves24_of_OpenResearchLeaves25_gm_eb r) t l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3243 (HDec.HSyn.sixContactMin_of_open33_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (sgr-fold, leaf-fold30). -/
theorem sixContactMin_of_open33_hf_gm_pz_eb (r : OpenResearchLeaves25GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ)
    (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open32_hf_gm_pz_eb r t l (openGlue7_of_OpenGlue8_hf_gm_pz_eb r t l g)
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3253 (HDec.HSyn.sixContactMin_of_open34_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (persists-dvr; generated). -/
theorem sixContactMin_of_open34_hf_gm_pz_eb (r : OpenResearchLeaves26GMEB) (t : OpenTextbookLeaves11HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open33_hf_gm_pz_eb (openResearchLeaves25_of_OpenResearchLeaves26_hf_gm_eb r t) t l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3262 (HDec.HSyn.sixContactMin_of_open35_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold31; generated). -/
theorem sixContactMin_of_open35_hf_gm_pz_eb (r : OpenResearchLeaves26GMEB) (t : OpenTextbookLeaves12HF) (l : OpenAddedLeaves17PZ) (g : OpenGlue8) : ZInQ.SixContactMin :=
  sixContactMin_of_open34_hf_gm_pz_eb r (openTextbookLeaves11_of_OpenTextbookLeaves12_hf t) l g
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3271 (HDec.HSyn.sixContactMin_of_open36_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves** (abhyankar-fold, leaf-fold32): no glue bundle. -/
theorem sixContactMin_of_open36_hf_gm_pz_eb (r : OpenResearchLeaves26GMEB) (t : OpenTextbookLeaves12HF) (l : OpenAddedLeaves17PZ) : ZInQ.SixContactMin :=
  sixContactMin_of_open35_hf_gm_pz_eb r t l openGlue8_proof
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3280 (HDec.HSyn.sixContactMin_of_open37_hf_gm_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (leaf-fold32; generated). -/
theorem sixContactMin_of_open37_hf_gm_pz_eb (r : OpenResearchLeaves27GMEB) (t : OpenTextbookLeaves13HF) (l : OpenAddedLeaves18PZ) : ZInQ.SixContactMin :=
  sixContactMin_of_open36_hf_gm_pz_eb (openResearchLeaves26_of_OpenResearchLeaves27_gm_eb r) (openTextbookLeaves12_of_OpenTextbookLeaves13_hf t) (openAddedLeaves17_of_OpenAddedLeaves18_pz l)
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/EichlerBoundCopy.lean:3289 (HDec.HSyn.sixContactMin_of_open45_pz_eb)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves** (fold33-pic, phisurj; `mumfordPhiSurjectiveAC` rerouted, `weilPairingMumford`
proved). -/
theorem sixContactMin_of_open45_pz_eb (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves22PZ) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open37_hf_gm_pz_eb
    (openResearchLeaves27_of_OpenResearchLeaves28_gm_eb
      (openResearchLeaves28_of_OpenResearchLeaves29_gm_eb (openResearchLeaves29GM_of_OpenResearchLeaves31_eb r)))
    (openTextbookLeaves13HF_of_open16_22_pz t r.neronSchemeExtensionDedekind l)
    (openAddedLeaves18_of_OpenAddedLeaves22_pz t l)
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ69.lean:73 (HDec.HSyn.sixContactMin_of_open48_eb_k954)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (piclft; generated).  Copy (fold-kleiman2): added bundle `OpenAddedLeaves26`, `kleimanPicZeroProper` replaced by `kleimanPicZeroProper954` (Kleiman 9.5.4 as printed). -/
theorem sixContactMin_of_open48_eb_k954 (r : OpenResearchLeaves31EB) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26) : ZInQ.SixContactMin :=
  sixContactMin_of_open45_pz_eb r t (openAddedLeaves22PZ_of_OpenAddedLeaves26 l)
end HSyn.GR9
end HDec

-- copied from ZInQKernel/OneProof/H/TailZ74.lean:1371 (HDec.HSyn.sixContactMin_of_open67)
namespace HDec
namespace HSyn.GR9
/-- **G0 with only the open leaves and the open glue** (coeff-field-tc, fold-b100): `sixContactMin_of_open66` without the fields
`gamma1IntegralBasis` and `heckePrimeIntegralToRational`, through the copied chain (`eigenformCoeffFieldFinite_proof`). -/
theorem sixContactMin_of_open67 (r : OpenResearchLeaves48) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) : ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  let l26 := openAddedLeaves26_of_OpenAddedLeaves27 l
  sixContactMin_of_open48_eb_k954 (openResearchLeaves31_of_OpenResearchLeaves32_eb_cf (openResearchLeaves32_of_OpenResearchLeaves33_eb_cf (openResearchLeaves33_of_OpenResearchLeaves34_eb_cf (openResearchLeaves34_of_OpenResearchLeaves35_eb_cf (openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf (openResearchLeaves36_of_OpenResearchLeaves37_eb_cf (openResearchLeaves37_of_OpenResearchLeaves38_eb_cf (openResearchLeaves38EB_of_OpenResearchLeaves39_cf (openResearchLeaves39_of_OpenResearchLeaves40_cf (openResearchLeaves40_of_OpenResearchLeaves41_cf (openResearchLeaves41_of_OpenResearchLeaves42_cf (openResearchLeaves42_of_OpenResearchLeaves43_cf (openResearchLeaves43_of_OpenResearchLeaves44_cf (openResearchLeaves44_of_OpenResearchLeaves45_cf (openResearchLeaves45_of_OpenResearchLeaves46_cf (openResearchLeaves46_of_OpenResearchLeaves47_cf r)))))))) t16) t16) t16) t16 l26) t16) t16))) t16 l26
end HSyn.GR9
end HDec

/-- **The top theorem with the GR §9 leaf in place of `bostLowerBoundAn`.** -/
theorem HDec.HSyn.sixContactMin_of_open67_gr9 (r : HDec.HSyn.GR9.OpenResearchLeaves48)
    (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27) : ZInQ.SixContactMin :=
  HDec.HSyn.GR9.sixContactMin_of_open67 r t l

#print axioms HDec.HSyn.sixContactMin_of_open67_gr9

/-! Field check (scratch): the copied top bundle has the original's fields minus `bostLowerBoundAn`, plus
`gaudronRemondSec9LowerAn`, each other field with the same type. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let o := `HDec.HSyn.OpenResearchLeaves48
  let n := `HDec.HSyn.GR9.OpenResearchLeaves48
  let fo := getStructureFields env o
  let fn := getStructureFields env n
  logInfo m!"original fields: {fo.size}, copy fields: {fn.size}"
  logInfo m!"only in original: {fo.filter (!fn.contains ·)}; only in copy: {fn.filter (!fo.contains ·)}"
  for f in fo do
    if fn.contains f then
      let tyO := (env.find? (o ++ f)).get!.type.bindingBody!
      let tn := (env.find? (n ++ f)).get!.type.bindingBody!
      unless tyO == tn do logInfo m!"type differs: {f}"
