import ZInQKernel.OneProof.H.TailZ45
import ZInQKernel.Contrib.OneProof.RaynaudNarrowChain
import ZInQKernel.Contrib.OneProof.RaynaudSemistableSHcpOr

/-! raynaud-narrow: compile check of the fold = proposed TailZ46 (hand step) + autofold.json dry run (TailZ47), concatenated. -/

/-! # OneProof H, raynaud-narrow (hand fold): `sixContactMin_of_open39`

The research field `raynaudSemistableSHOr` (TailZ45) is read by the chain only at number fields, through
`raynaudSemistable_of14` (TailZ23); raynaud-narrow re-versioned every declaration from `sixContactMin_of_open17`
to `sixContactMin_of_open38` that carries it (`ZInQKernel/Contrib/OneProof/RaynaudNarrowChain.lean`, namespace
`HDec.HSyn.RNarrow`) so that the chain reads `ReductB.RaynaudSemistableSHcp` instead (characteristic `0`,
algebraically closed residue field). This module is the next generation over that chain: `OpenResearchLeaves29`
is `OpenResearchLeaves28` with `raynaudSemistableSHOr` replaced by `raynaudSemistableSHcp`. The field is then
discharged by autofold (`scratch/raynaud-narrow/autofold.json`) from the printed leaf
`RaynaudNarrow.RaynaudSemistableSHcpOr`. -/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves28` with `raynaudSemistableSHOr` replaced by `raynaudSemistableSHcp`, the generality the
chain reads (raynaud-narrow). -/
structure OpenResearchLeaves29 : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
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
  /-- gt-grcount, printed form: Gonzalez-Rotger 2006 Prop. 5.6 at (D,N) = (6,1) on X0(6,1), for every witness of the moduli description (no existence claim; the model comes from gonzalezRotgerX6Ab). Replaces gonzalezRotgerCountX6Ab. -/
  gonzalezRotgerProp56X6 : _root_.GRCountX6.GonzalezRotgerProp56X6
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- gt-sga3, narrowed: SGA 3 VI_B 3.10 in neighbourhood form: for a smooth group scheme G over any S and every s in S, some open neighbourhood of e(s) lies in the identity component G^0 (numbers UNVERIFIED). With GeomConnOfRationalPoint (proved) gives SGA3_VIB_3_10 (SGA3IdComp.sga3_VIB_3_10_of_nbhd). -/
  sga3_VIB_3_10_Nbhd : _root_.SGA3IdComp.SGA3_VIB_3_10_Nbhd
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With sga3_VIB_3_10 and geomConnOfRationalPoint (idComp_baseChange, SGA 3 VI_B 3.3 proved) replaces sga7_IX_3_3_SH. -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- raynaud-narrow: Raynaud's criterion (SGA 7 I, Exp. IX, Prop. 4.7; number UNVERIFIED) over a strictly
  henselian DVR of a field of characteristic `0` with perfect (hence algebraically closed) residue field
  (`ReductB.RaynaudSemistableSHcp`, TailZ23), the only generality the chain reads; replaces
  `raynaudSemistableSH` (generation 28: `raynaudSemistableSHOr`). -/
  raynaudSemistableSHcp : _root_.ReductB.RaynaudSemistableSHcp
  /-- dict-models, printed form: Mumford-Fogarty-Kirwan, GIT, Thm 6.14 over a connected locally noetherian base (numbers UNVERIFIED): the group law on a proper smooth family with a section all of whose fibres are abelian varieties. The gluing over connected components is proved (mumfordGroupLaw_of_conn). Replaces mumfordGroupLaw. -/
  mumfordGroupLawConn : _root_.DictModels.MumfordConn.MumfordGroupLawConn
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

/-- raynaud-narrow's chain bundle `RNarrow.OpenResearchLeaves28` from `OpenResearchLeaves29` (field for field). -/
theorem rNarrowLeaves28_of_OpenResearchLeaves29 (n : OpenResearchLeaves29) : RNarrow.OpenResearchLeaves28 where
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
  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHcp := n.raynaudSemistableSHcp
  mumfordGroupLawConn := n.mumfordGroupLawConn
  blr_7_2_1 := n.blr_7_2_1
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed

/-- **G0 with only the open leaves and the open glue** (raynaud-narrow; hand fold over the re-versioned chain). -/
theorem sixContactMin_of_open39 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19) : ZInQ.SixContactMin :=
  RNarrow.sixContactMin_of_open38 (rNarrowLeaves28_of_OpenResearchLeaves29 r) t l

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open39

/-! # OneProof H, raynaud-narrow: `sixContactMin_of_open40` (generated by scripts/one_proof/autofold.py)

Fields removed (each proved by a contribution): `raynaudSemistableSHcp`.
Fields added (new leaves): `raynaudSemistableSHcpOr`. -/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves29` without `raynaudSemistableSHcp`, with the leaves `raynaudSemistableSHcpOr` (raynaud-narrow). -/
structure OpenResearchLeaves30 : Prop where
  r9a : _root_.PkgI3.FaltingsSemisimple
  r9b : _root_.PkgI3.FaltingsTate
  hodgeTateDecompAbVar : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar
  deRhamH1AbVarT : _root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT
  r11r12 : PkgI4.PanBerger
  eigenformHTNew : _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew
  r17 : _root_.LadicCond.CarayolR17'
  /-- height-split, H-17: Bost's lower bound `h_D(A) ≥ −(g/2) log 2π` (Sém. Bourbaki 795), replaces `r21`. -/
  bostLowerBound : _root_.ZInQ.HeightSplit.BostLowerBound
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
  /-- gt-grcount, printed form: Gonzalez-Rotger 2006 Prop. 5.6 at (D,N) = (6,1) on X0(6,1), for every witness of the moduli description (no existence claim; the model comes from gonzalezRotgerX6Ab). Replaces gonzalezRotgerCountX6Ab. -/
  gonzalezRotgerProp56X6 : _root_.GRCountX6.GonzalezRotgerProp56X6
  /-- gt-unip, printed form, strictly henselian base: SGA 7 I Exp. IX Prop. 3.5, direction semistable => (sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time (the print gives (sigma-1)(tau-1) = 0 and the converse); number UNVERIFIED. Semistability read on the geometric special fibre; reading risk: if the print reads it over k(s), this form exceeds the print by UnipotentForward.SemiAbelianDescendsSepClosed for imperfect residue fields only (the reading-robust variant is UnipotentForward.semistableUnipotent_of_forward). Replaces semistableUnipotent; StrictHenselizationInside and the K^s axis are proved. -/
  sga7_IX_3_5_ForwardGeom : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom
  /-- gt-rayclass (shimura-cft, rayclass-cft), composite of printed theorems: Shimura's Main Theorem I for the level-3 group K3 of B = (2,-3|Q) in Deligne's adelic form on the fine moduli scheme Y3 of QM abelian surfaces (R1fpPropsAb): the uniformization B^x_+ \ (H x (B (x) A_f)^x) / K3 = Y3(C), holomorphy in tau, the moduli clause at every u in O-hat^x (the object at Psi(tau,u) is C^2/iota(O)(tau,1)^T) and Shimura's reciprocity law at CM points. Replaces rayClassCMAb and shimuraFamilyAb. -/
  shimuraMainThmIDeligneY3AbU : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU
  /-- r16-split: R16_EichlerShimuraJ1' with its rank-two clause deleted (a consequence of r16; R16Split.coreY_of_r16). For a newform f in S_2(Gamma_1(N)) with nebentypus chi and J = J_1(N): [K_f:Q] < infinity, and one Q-quotient pi : J ->> A with theta : K_f -> End^0(A), dim A = [K_f:Q], and arithmetic Frobenius at p not dividing N*l acting on every iota-component of V_l(A) with trace iota(a_p) and determinant iota(chi(p)) p. The rank-two clause is proved from dim A = [K_f:Q], mumfordTorsionAlgClosed and charPolyIndepOfEllAlgClosed (Mumford 19 Thm 4): R16Split.r16_of_printed. Still a composite of two printed theorems about Shimura's A_f, which has no Lean definition (no Hecke correspondences on X_1(N), no S_2 <-> H^0(X_1(N), Omega^1) comparison). -/
  r16CoreY : _root_.R16Split.R16CoreY
  /-- elkies-coord: Elkies, Shimura curve computations (ANTS-III 1998) section 3 on X*(6) = X6/W in his function-field form on the canonical witness: Q(X6)^W = Q(t) whenever X6 is integral and t regular at its generic point (both proved from the charts) (t generates the function field of X6/W; W = {1,w2,w3,w6} by its moduli action, acting by pullback on Mathlib's function field), t = 0, 1, infinity at the CM points of discriminant -24, -4, -3, and the charts s^2 = -t, r^2 = 3(t-1) (section, display and 0/infinity orientation UNVERIFIED). Replaces elkiesX6StarPrinted (its Qbar-point fibre clause is proved: elkiesX6StarPrinted_of_functionField). -/
  elkiesX6StarFunctionField : _root_.HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField
  /-- gt-sga3, narrowed: SGA 3 VI_B 3.10 in neighbourhood form: for a smooth group scheme G over any S and every s in S, some open neighbourhood of e(s) lies in the identity component G^0 (numbers UNVERIFIED). With GeomConnOfRationalPoint (proved) gives SGA3_VIB_3_10 (SGA3IdComp.sga3_VIB_3_10_of_nbhd). -/
  sga3_VIB_3_10_Nbhd : _root_.SGA3IdComp.SGA3_VIB_3_10_Nbhd
  /-- dict-models, printed form: SGA 7 I, Exp. IX, Prop. 3.3, second assertion, over strictly henselian traits, with U the print's N0 x_S S' (the preimage of N0 under the projection N x_O O' -> N), not the identity component of N x_O O' (number UNVERIFIED). With sga3_VIB_3_10 and geomConnOfRationalPoint (idComp_baseChange, SGA 3 VI_B 3.3 proved) replaces sga7_IX_3_3_SH. -/
  sga7_IX_3_3_SHpre : _root_.DictModels.SGA7Pre.SGA7_IX_3_3_SHpre
  /-- dict-models, printed form: Mumford-Fogarty-Kirwan, GIT, Thm 6.14 over a connected locally noetherian base (numbers UNVERIFIED): the group law on a proper smooth family with a section all of whose fibres are abelian varieties. The gluing over connected components is proved (mumfordGroupLaw_of_conn). Replaces mumfordGroupLaw. -/
  mumfordGroupLawConn : _root_.DictModels.MumfordConn.MumfordGroupLawConn
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
  /-- raynaud-narrow, printed form (restricted): Raynaud's criterion, SGA 7 I (LNM 288) Exp. IX Prop. 4.7 (number UNVERIFIED), over a strictly henselian DVR of a field of characteristic 0 with perfect (hence algebraically closed) residue field: m >= 3 invertible and A[m] rational over K imply semistable reduction, read over k(s) (general torus) or on the geometric special fibre (disjunction, either reading by or-introduction). dict-models' raynaudSemistableSHOr restricted to the only generality the chain reads (r6 and SS1/SS3 at number fields, through the strict henselization); the ascent to the geometric form is proved (raynaudSemistableSHcp_of_cpOr', Stacks 04KV). -/
  raynaudSemistableSHcpOr : _root_.RaynaudNarrow.RaynaudSemistableSHcpOr

/-- `OpenResearchLeaves29` from `OpenResearchLeaves30`: `raynaudSemistableSHcp` by the contributions. -/
theorem openResearchLeaves29_of_OpenResearchLeaves30 (n : OpenResearchLeaves30) : OpenResearchLeaves29 where
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
  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd
  sga7_IX_3_3_SHpre := n.sga7_IX_3_3_SHpre
  raynaudSemistableSHcp := _root_.RaynaudNarrow.raynaudSemistableSHcp_of_cpOr' n.raynaudSemistableSHcpOr
  mumfordGroupLawConn := n.mumfordGroupLawConn
  blr_7_2_1 := n.blr_7_2_1
  neronOggShafarevichSep := n.neronOggShafarevichSep
  dsThm965Printed := n.dsThm965Printed
  eigenformCoeffFieldFinite := n.eigenformCoeffFieldFinite
  dsThm966Printed := n.dsThm966Printed

/-- **G0 with only the open leaves and the open glue** (raynaud-narrow; generated). -/
theorem sixContactMin_of_open40 (r : OpenResearchLeaves30) (t : OpenTextbookLeaves13) (l : OpenAddedLeaves19) : ZInQ.SixContactMin :=
  sixContactMin_of_open39 (openResearchLeaves29_of_OpenResearchLeaves30 r) t l

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open40

