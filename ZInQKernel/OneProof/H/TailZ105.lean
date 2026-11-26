import ZInQKernel.OneProof.H.TailZ104
import ZInQKernel.Contrib.OneProof.DS965Reroute.Chain5

/-! # OneProof H, ds965-reroute-fold: `sixContactMin_of_open98`

Field removed (rerouted, not proved): `dsThm965AtPrimes`. Its readers on the live route are served by
`modularHTCoeff` (weight at least 2) and `dsThm966Printed` (weight 1) through the copy chain
`Contrib/OneProof/DS965Reroute/Chain1`-`Chain5` (#197), whose top is `sixContactMin_of_open96_ds`; the
determinant clause of `R14Det`, which the live route does not read, is dropped there.
Fields added (new leaves): none. -/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves77` without `dsThm965AtPrimes` (ds965-reroute-fold). -/
structure OpenResearchLeaves78 : Prop where
  /-- height-split, H-18: the upper half of Pazuki 2012 Cor. 1.3(2), replaces `r22`. -/
  pazukiCor13Upper : _root_.ZInQ.HeightSplit.PazukiCor13Upper
  /-- Deligne-Serre, Formes modulaires de poids 1, Ann. Sci. ENS (4) 7 (1974), Thm 4.1 with (4.1.1), pp. 513-514, as printed: for f != 0 a (cusp) form of type (1, eps) with eps(-1) = -1 that is an eigenvector of the T_p, p not dividing N, with eigenvalues a_p (Tau Ceti EigenformAwayFromLevel N 1, no normalization a_1 = 1), a continuous rho : G_Q -> GL_2(C) with finite image, unramified outside N, with tr rho(Frob_p) = a_p (the T_p-eigenvalue F.eigenvalue p) and det rho(Frob_p) = eps(p). The coefficient form a_p = coeff g p (from a_1 = 1) and eps(-1) = -1 (parity lemma, TauCeti Parity.lean:113) are glue in DSThm966EV.dsThm966_of_printed (coeff-fix). -/
  dsThm966Printed : _root_.DSThm966EV.DSThm966Printed
  /-- r16-det: Diamond-Shurman Thm 9.6.5 at k = 2 for the Section 9.5 realization on A_f, over K_{f,lambda}, universal over A_f. For every (A, pi, theta) that is DS's A_f (afShimura's characterization, for any X, generators, P0, Jacobian and Hecke operators as in heckeJ1DS), every prime l and every place lambda | l of K_f: for p not dividing N l every arithmetic Frobenius sigma at p acting on V_lambda = K_lambda (x)_{Q_l (x) K_f} V_l(A) (rho_{f,lambda}, DS Exercise 9.5.2(a)) has characteristic polynomial X^2 - a_p X + chi(p) p over K_lambda. Statement = aftate-fix2's AfTateLam.AfTateDSLambda verbatim (AfTateLam.afCharpolyDS965_iff, Iff.rfl); it implies r16-close's glue AfDetLambda (AfTateLam.afDetLambda_of_ds965). -/
  afCharpolyDS965 : _root_.AfTateLam.AfCharpolyDS965
  /-- R13, printed existence form over a finite coefficient field (htnew-assembly): for a prime l, embeddings iota_C, iota_L and a Tau Ceti newform f of weight k >= 2 and level N (every level, l | N included), there are a finite extension E of Q_l inside Qbar_l (the print's K_{f,lambda} / Kato's F_lambda, embedded) and a continuous rho : G_Q -> GL_2(E), unramified outside N l, with either (arithmetic Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight +1) or (geometric Frobenius trace a_p and Hodge-Tate weights {0, k-1}, cyclotomic weight -1), the multiplicity of w being dim_E (V tensor_{Q_l} C_l(-+w))^{G_{Q_l}} (Mathlib tensor product, the print's definition). Replaces modularHTPrinted: the assembly lemma dim_E (V tensor C_l(w))^G = htMult(rho dual, -w) (trace-form isomorphism V tensor C_l = Hom(E^n, C_l)), HTDual and the coefficient extension E in Qbar_l are proved in Lean (ModularHTCoeff.lean). -/
  modularHTCoeff : _root_.HTNewAssembly.ModularHTCoeff
  /-- Shimura 1967 Main Theorem I in Deligne's form (Sem. Bourbaki 389, sections 4-5, a seminar report: under Jack's 11-23 ruling (D2) it is a source only if it proves the statement, which is not checked; background reading only, not a source: Milne, Introduction to Shimura varieties (2005), sections 5-8 and 12-14) for Y3 = Sh_K3(B^x, H^pm), B = (2,-3|Q) (locators unverified; composite (GLUE)), for every witness (Y, Phi) of the printed fine-moduli clause list Y3Fix.R1fpPropsAbP: Psi : H^pm x (B (x) A_f)^x -> Y(C) onto with fibres exactly the print's double cosets B^x \ (H^pm x G(A_f) / K3) (DCRelPM); holomorphic in tau in H for every g; at [tau, u], u in O-hat^x (L_u = O), the abelian surface A with (H_1(A, Z), iota_*, h_A) = (O, left multiplication, h_tau) in genuine form (IsHodgeH1Print: H_1 = pi_1(A(C), 0)^ab for the classical topology, O acting by functoriality, the complex structure of Lie A through a holomorphic homomorphism e = exp_A o L, right multiplication by J_tau); Shimura's reciprocity law at CM points of H (conventions existential). Equivalent to the old field deligneCanonicalModelY3EveryH (Y3Hodge.print_iff_deligneH, both directions proved: restriction to H by exists_upper and dcRelPM_iff, retraction H^pm -> H by mu = 1+i, H_1 dictionary print_iff_hodge). Consequence form: bijective and holomorphic in place of the biholomorphism, moduli clause at O-hat^x without polarization (exists and is unique: Y3Hodge.lemmaP_H1, Lemma P on the genuine H_1) and level structure, reciprocity at CM points of H -/
  deligneCanonicalModelY3EveryPrint : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint
  /-- bost-gr9 (fold-b112), over the printed semistability: the weaker form of Gaudron-Remond,
  Theoreme des periodes et degres minimaux d'isogenies, Comment. Math. Helv. 89 (2014), Cor. 8.4,
  p. 400 (GR1; attribution: Bost), h(A) >= -(g/2) log(2 pi), with the normalization
  h_F(A) = h(A) - (g/2) log pi on p. 352 (two-lens statement check 2026-11-24). Duke 163 p. 2098:
  citation only (Gaudron-Remond, Polarisations et isogenies, Duke Math. J. 163 (2014), section 9,
  proof of Lemme 9.1, citing GR1 Cor. 8.4; cited by the manuscript at diophantine_zq.tex L894-895,
  step E4): h_F(A) >= -(3/2) dim A for every abelian variety over a number field, Faltings'
  original normalization, over ZInQ.SemistabAssembly.IsAnStableHeightSS (semistable reduction as
  printed, as gaudronRemondThm14AnSS). Replaces bostLowerBoundAnSS (strictly stronger:
  -(g/2) log(2 pi^2), BostGR9.sec9_bound_lt_bost; it implies the leaf,
  BostGR9.gaudronRemondSec9LowerAnSS_of_bostLowerBoundAnSS); consumed through
  BostGR9.gaudronRemondSec9LowerAn_of_ss, BostGR9.sec9Printed_of_an,
  BostGR9.grBostBound_of_sec9Printed and BostGR9.r21_of_grBost' (R21). -/
  gaudronRemondSec9LowerAnSS : _root_.ZInQ.BostGR9.GaudronRemondSec9LowerAnSS
  /-- Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (p. 2060; kappa p. 2058; read by the audit), over the stable height with the metric on A_tau(C)^an (r3-residual) and semistable reduction as printed (identity component of the special fibre semi-abelian over k(p) and over k(p)bar; semistab-assembly). GaudronRemondThm14An verbatim with IsSemistableRes replaced by IsSemistablePrinted; it implies GaudronRemondThm14An (gaudronRemondThm14An_of_ss). -/
  gaudronRemondThm14AnSS : _root_.ZInQ.SemistabAssembly.GaudronRemondThm14AnSS
  /-- jp-an-retype: Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 (h_Fal(X) <= 13*10^6 * g * deg_B(X)^5 for a smooth projective connected curve X/Qbar of genus g >= 1) composed with Section 2.3 (h_Fal(X) = stable Faltings height of Jac X), as the manuscript cites it at diophantine_zq.tex L870 (applied to J = J_1(N)). JavanpeykarDirect.JavanpeykarThm111 verbatim with IsStableHeightBar replaced by IsStableHeightBarAn: the stable height of a model over a number field L of the Jacobian W, read as IsAnStableHeightSS (archimedean metric (i/2)^g int eta~ wedge eta~-bar on the complex manifold A_tau(C)^an, densities in every holomorphic chart, r3-residual; semistability: semi-abelian reduction of the Jacobian's Neron model, IsSemistablePrinted, semistab-assembly; not the print's curve-model semistability, Def. 2.2.1). Replaces javanpeykarThm111 (JavanpeykarAnRetype.javanpeykarThm111_of_an, with mumfordTorsionAlgClosed and uniformizationLeafAll_proof for T35); the converse javanpeykarThm111An_of_thm111 holds given T35, so the leaf is not stronger than the row it replaces. -/
  javanpeykarThm111An : _root_.JavanpeykarAnRetype.JavanpeykarThm111An
  /-- y3-route-a, the manuscript's own conclusion (diophantine_zq.tex L473-477; one object: the integral model X35/G5 of Y3 with its universal family): the moduli problem of abelian surfaces with an action of the maximal order O of B = (2,-3|Q) and full O-linear level-3 structure (QMAbSchemeP: at every geometric point eta : O/3O = A_s[3], i.e. a section of Isom_O(O/3O, A[3])) is represented on locally noetherian Z[1/30]-schemes by a proper smooth curve over Z[1/30] with a universal QMAbSchemeP; its generic fibre is Y3 (proved: Y3RouteA.y3RepresentableQ_of_z30 gives Y3Audit.Y3RepresentableQ). Manuscript derivation: Buzzard, Duke Math. J. 87 (1997) Thm 2.1 and Cor. 2.3 at V1(5) over Z[1/30] (L443-446); full five-marking (L447-449); the finite etale sheaf Isom_O(O/3O, A[3]), nonempty on geometric fibres since the Tate lattice is free of rank one over O_3 (L449-462); free action of G5 = (O/5O)^x by torsion-freeness of 1 + 3M4(Z3) (L465-472); quotient X35/G5 and descent of the universal abelian scheme with polarization, O-action and three-marking (L472-477). Weaker than the manuscript: proper for projective, locally noetherian universe-0 bases, no polarization (equivalent through the canonical principal polarization, relative Lemma P: ON THE SPOT, not proved in the tree). Implies Y3Fix.Y3FineModuliAbP (Y3RouteA.y3FineModuliAbP_of_z30). -/
  y3FullThreeRepZ30 : _root_.Y3RouteA.Y3FullThreeRepZ30
  /-- carirr-refold, consequence of Darmon-Diamond-Taylor 1997 Thm 3.1 (proved: CarayolRefold.frob_of_DDT31 from carirr-odd's transcription CarayolDDT.CarayolDDT31), with the Frobenius clause in the normalization the manuscript reads off Carayol 1986 Theoreme (A) (diophantine_zq.tex L9784-9796): for a printed newform f (Tau Ceti Newform N 2, psi = f.chi) with number field K_f and a place lambda | l, a continuous rho : G_Q -> GL_2(K_{f,lambda}) that is irreducible (Ribet 1977), unramified at p not dividing N l with arithmetic Frobenius of trace a_p and determinant p psi(p) (polynomial X^2 - a_p X + p psi(p)), and with codim V^{I_p} + integral_0^infty codim V^{G_p^u} du = v_p(N) at every p != l (Carayol Thm A + conductor of local Langlands + Casselman 1973 Thm 1; packaged in DDT 3.1). Oddness is proved from the Frobenius determinant (CarayolRefold.odd_of_frobDet, one Chebotarev element). Carayol's own form (sigma_lambda(pi)|G_{Q_p} <-> pi_p under local Langlands) has no Lean form (no pi_{f,p}, Weil-Deligne representations or local Langlands in Lean). Replaces carayolThmAIrr. -/
  carayolThmAFrob : _root_.CarayolRefold.CarayolThmAFrob
  /-- r16-thm1b: Shimura 1973 Thm 1 in consequence form (GLUE, pending review), one row. For a newform f in S_2(Gamma_1(N)) with nebentypus chi, the kernel's model X of X_1(N), Jacobian J, Hecke operators T_p = xi_p, <d>: K_f finite over Q, and there is a triple (A, nu, theta) with Shimura's clauses (i) nu surjective with connected kernel, (ii) nu o xi_n = theta(a_n) o nu at n = p and n = p^2 (xi_{p^2} = T_p^2 - p<p>), (iii) dim A = [K_f : Q], and IsAfQuotient (ker nu = I_f J: nu kills I_f J and is universal for that), unique up to a nu-compatible isomorphism over Q among triples with (i)-(iii). Printed (AI page read): C = Ker(nu) (p. 525), C from the ideal annihilating f intersected with End(J) (p. 526), uniqueness up to isomorphisms over Q (p. 526), dimension and tangent space from m = 1 via q-expansions (p. 527). ON THE SPOT steps: C = I_f J (the ideal is ker rho, saturation, Hecke relations in both directions); (ii) for all n from p and p^2 via xi_{p^2} = T_p^2 - p<p> (a theorem step, the Hecke relation); nu-compatible isomorphisms. Euler clause and (iv) not in this row. -/
  shimuraThm1Af : _root_.R16Thm1b.ShimuraThm1Af
  /-- cm-branch (leaf, consequence form; GLUE: rating refuted 11-17, reported formula):
  Barquero-Sanchez et al., Res. Number Theory 3 (2017), Eq. (6.2) (L600-605). -/
  cmHeight62 : _root_.HDec.CMBranch.CMHeight62
  /-- Fowler, Proposition 2·7: for an imaginary quadratic order discriminant Δ < 0 congruent to 0 or 1 modulo 4 and positive n, h(Δ) ≤ n implies √|Δ| ≤ 2n² exp(21000n²), with h(Δ) the proper ideal class number of the unique order of discriminant Δ. -/
  fowlerProp27PrintCanonical : HDec.CMBranch.FowlerBridges.FowlerProp27PrintCanonical
  /-- Fowler (2026), section 2·1, p. 613: a singular modulus of primitive equation discriminant Δ has degree h(Δ) over ℚ, with h(Δ) the proper ideal class number. -/
  cmjDegreePrint : HDec.CMBranch.CMjBridges.CMjDegreePrint
  /-- Grothendieck's semistable reduction theorem as stated in Silverberg-Zarhin, Ann. Inst. Fourier 45 (1995), Theorem 3.4, pp. 405-406 (proof: SGA 7 I, Exp. IX, Th. 3.6, p. 351): for an abelian variety A over a field K with a discrete valuation ring O, one finite Galois extension E of K inside an algebraic closure such that A_E has semistable reduction (HasSemistableReductionSZ, which also asserts a Neron model) at every prolongation of O to E. Replaces silverbergZarhinThm35 (Raynaud's criterion), which SZRaynaud.silverbergZarhinThm35_of_sz34 proves from it with the proved Theorem 3.3. -/
  silverbergZarhinThm34 : _root_.SZRaynaud.SilverbergZarhinThm34
  /-- Berger's p-adic monodromy theorem, Invent. Math. 148 (2002), 219-284, as cited by the manuscript (bibitem berger2002; theorem number to be checked against the print, Théorème 0.6 or 0.7): every de Rham representation of G_{Q_p} is potentially semistable, here in Fontaine's dimension form over BstFOf (Astérisque 223 (1994), Exp. III, 1.8.5 and 5.6.1; Exp. II, 4.2.4-4.2.5). Colmez, Astérisque 319 (2008), Théorème 0.1, prints the basis form, which implies this field (PanBergerRefereed.bergerSurveyF_of_colmez); the converse needs the G_K-regularity of B_st, which is not proved, so ColmezThm01 is not a replacement at the same count. -/
  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF
  /-- Pan, The Fontaine-Mazur conjecture in the residually reducible case, Theorem 1.0.4 with Conjecture 1.0.1, read in arXiv:1901.07166v2 (pp. 5 and 2), the version the manuscript cites; published in J. Amer. Math. Soc. 35 (2022), whose numbering is unchecked. Here p >= 5, with potential semistability in Fontaine's sense (Astérisque 223 (1994), Exp. III, 5.6.1, in the equivalent form of 1.8.5). Same statement as the replaced panPrintedF, token for token; only the source of the definitions changes from Brinon-Conrad's notes to Fontaine's exposés; panPrintedF_of_thm104F. -/
  panThm104F : _root_.HDec.PkgI4.PanBergerRefereed.PanThm104F

/-- `OpenResearchLeaves77DS` (the bundle of the copy chain of #197) from `OpenResearchLeaves78`, field by field. -/
theorem openResearchLeaves77DS_of_OpenResearchLeaves78 (n : OpenResearchLeaves78) : OpenResearchLeaves77DS where
  pazukiCor13Upper := n.pazukiCor13Upper
  dsThm966Printed := n.dsThm966Printed
  afCharpolyDS965 := n.afCharpolyDS965
  modularHTCoeff := n.modularHTCoeff
  deligneCanonicalModelY3EveryPrint := n.deligneCanonicalModelY3EveryPrint
  gaudronRemondSec9LowerAnSS := n.gaudronRemondSec9LowerAnSS
  gaudronRemondThm14AnSS := n.gaudronRemondThm14AnSS
  javanpeykarThm111An := n.javanpeykarThm111An
  y3FullThreeRepZ30 := n.y3FullThreeRepZ30
  carayolThmAFrob := n.carayolThmAFrob
  shimuraThm1Af := n.shimuraThm1Af
  cmHeight62 := n.cmHeight62
  fowlerProp27PrintCanonical := n.fowlerProp27PrintCanonical
  cmjDegreePrint := n.cmjDegreePrint
  silverbergZarhinThm34 := n.silverbergZarhinThm34
  bergerSurveyF := n.bergerSurveyF
  panThm104F := n.panThm104F

/-- **G0 with only the open leaves and the open glue** (ds965-reroute-fold). -/
theorem sixContactMin_of_open98 (r : OpenResearchLeaves78) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves29) : ZInQ.SixContactMin :=
  sixContactMin_of_open96_ds (openResearchLeaves77DS_of_OpenResearchLeaves78 r) t (openAddedLeaves28_of_OpenAddedLeaves29 l)

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open98
