#!/usr/bin/env python3
"""Generate triage.tsv (one row per statement) from the table below.

Columns: id, field, bundle, constant, def (file:line at e38375b3), row (frontier r5), issue, form,
consumers, use (a/b), weakest sufficient statement, kind of the specialized statement, library coverage,
missing infrastructure, tier, strategy, status/owner, rank, marks.
Marks: V = VERIFIED (read or compiled), S = SPECULATIVE; see docs/research/gap-triage.md and log.md.
"""
import csv, os, sys

H = ["id", "field", "bundle", "constant", "def", "row", "issue", "form", "consumers", "use",
     "weakest_sufficient", "spec_kind", "library", "missing", "tier", "strategy", "status_owner", "rank", "marks"]

D = "ZInQKernel/OneProof/H/"
R = []
def row(*a):
    assert len(a) == len(H), (a[1], len(a))
    R.append(a)

# ---------------- research bundle (OpenResearchLeaves10, TailZ15) ----------------
row("R01", "r1r2", "research", "HDec.LeafAdopt.R1R2fpRep", D+"LPrefix.lean:5218", "H-1 (F split H-142, H-149..H-152)", "—", "composite",
    "R1R2fp_of_rep (LPrefix:5228) → glueOutputs_of_leaves3 (TailD:209), gluePieces_of_open4 (TailK:297-325: NoCM, period map, propTSAll), heckeVertWitness_of_leaves5 (TailN:38), shimuraGoodReduction_of_noGuard (TailW:743)",
    "b: one Y3, X6 for O ⊂ (2,−3|ℚ); all points of Y3 and fibres over J(u), u ∈ ℚ",
    "R1R2fpRep without the last clause R1pi0Props (discarded by R1R2fp_of_rep) and probably without R1recProps (only reader feeds the unused field r1rec)",
    "still deep (moduli theorem, Baba–Granath, González–Rotger)",
    "x6-glue r1r2_of_published (6 printed leaves + RayClassCM; compiled on its branch); TailZ12 deligneComponentsX6_of_printed; w63 R1fpPropsAb, MumfordRigidityCore, QMAbScheme",
    "integral PEL moduli of QM surfaces, Baba–Granath π6, GR Thm 5.12, adelic uniformization (RayClassCM)",
    "T4", "keep cited (x6-glue split); prune unused clauses", "in flight: route A (folded in w63 as r1r2Ab), x6-glue/x6-fold", "—",
    "V: R1pi0Props discarded (agent A, LPrefix:5228 read); S: R1recProps unused")
row("R02", "shimuraFamily", "research", "HDec.QMSplit.Moduli.ShimuraFamily", D+"TailU.lean:1952", "H-139 (F split H-154)", "—", "consequence of one theorem",
    "researchLeaves5_of_open7 (TailX:198) r1b_of' → fibreQMPeriod_main_rep (TailC:8450) via gluePieces_of_open4 (TailK:317)",
    "b: only R1bFamily at the own triple of r1r2's witness",
    "∀ h : R1R2fpRep, R1bFamily (ownY (R1R2fp_of_rep h)) (ownΦ …) (ownπ …) (= old field r1b)",
    "still deep (Shimura Main Thm I)",
    "shimura-cft ShimuraMainThmIDeligneY3Ab → shimuraFamily(Ab) (branch, Parts A/B compile); shimura-split holP1_of_isHolFamily",
    "analytification of Y3 and its family, Riemann algebraization, holomorphic moduli map",
    "T4", "keep cited (shimura-cft printed leaf)", "in flight: c-to-printed (brief), shimura-cft branch; w63 shimuraFamilyAb", "—", "V (agent A; TailX:198 read by me)")
row("R03", "igusaPsi4", "research", "HDec.QMSplit.Theta.IgusaPsi4", D+"TailU.lean:1797", "H-131", "—", "published form",
    "thetaModularity_of (TailU:1812) → g8Auto_of_sp (TailJ:4020) via g8Auto_g4/g6 → s8WeightExact_of → qmDenZeroCM3_of_leaves4 (TailK:99), base2_of_base3 (TailO:2461), auto8 (TailZ2)",
    "b: only M ∈ {M4, M6} (TailJ:4116ff), Ω = Omega z, z ∈ ℍ",
    "∀ M ∈ {M4, M6}, ∀ z, 0 < z.im → thetaSum8 (spAct M (Omega z)) = spFactor M (Omega z) ^ 4 * thetaSum8 (Omega z)",
    "finite computation + Poisson summation (theta inversion)",
    "Mathlib jacobiTheta₂_functional_equation (probe), jacobiTheta_S_smul/T_sq_smul; cm24-value pi0 (genus-2 partial inversion, branch); theta-glue summability on 𝔥₂; chain M4_symp, M6_symp, omegaSiegel_proof",
    "theta transformation under translation, rotation, partial inversion; words for M4, M6; phase bookkeeping",
    "T1-T2 (specialized); T2 general (+ generation of Sp4(ℤ))", "specialize and compute", "free", "A4",
    "V: only M4/M6 (grep of all hT uses, TailJ/TailO/TailZ2)")
row("R04", "igusaChi10", "research", "HDec.QMSplit.Theta.IgusaChi10", D+"TailU.lean:1807", "H-132", "—", "published form",
    "thetaModularity_of → g20Auto_of_sp (TailO:2038) via g20Auto_g4/g6 → s20WeightExact_of, base2_of_base3, auto20/autoHc (TailZ2)",
    "b: only M4, M6 at Omega z",
    "∀ M ∈ {M4, M6}, ∀ z, 0 < z.im → thetaProd2 (spAct M (Omega z)) = spFactor M (Omega z) ^ 10 * thetaProd2 (Omega z)",
    "finite computation + theta inversion", "as igusaPsi4", "as igusaPsi4 (phases: product of ten 4th roots of unity)",
    "T1-T2 (specialized)", "specialize and compute", "free", "A4", "V (as igusaPsi4)")
row("R05", "r7a", "research", "PkgI2.NeronOggShafarevich", "ZInQKernel/HDecomp/Objects.lean:861", "H-5", "—", "published form",
    "kernelFieldExists_of_split'' → good_of_QML3 (via gluePieces_of_open4)", "b: .2.mpr, QM surfaces, m = 3^k",
    "inertia trivial on A[3^k] ⇒ good reduction, QM surfaces only", "still deep (Néron models)",
    "CloudW03 (FLT) Néron models over henselian DVR only", "Néron models over a DVR of a number field", "T4", "keep cited", "blocked (brief: H-5)", "—", "S (agent CD)")
row("R06", "r9a", "research", "PkgI3.FaltingsSemisimple", "ZInQKernel/Contrib/G9/I3Layer.lean:882", "H-6", "—", "published form",
    "g8_g12 / afterG7_of3 / newformLeaves_of3 / hom_of_common3 (TailD) → E1_exists_hom_ne_zero", "b: QM surface (ℓ = 3, 5), J1(N), A_f",
    "Faltings semisimplicity for those objects", "still deep", "none", "Faltings 1983", "T4", "keep cited", "free", "—", "S (agent CD)")
row("R07", "r9b", "research", "PkgI3.FaltingsTate", "ZInQKernel/Contrib/G9/I3Layer.lean:889", "H-7", "—", "published form",
    "as r9a, plus h10g in g8_g11", "b: (A, J1(N)_L), (A, A), (A_f, J1(N))", "Tate conjecture for those pairs", "still deep", "none", "Faltings 1983", "T4", "keep cited", "free", "—", "S (agent CD)")
row("R08", "hodgeTateDecompAbVar", "research", "ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar", D+"TailS.lean:347", "H-122", "—", "published form (specialization)",
    "r10 → G9Glue (g9Glue_of_fieldEmb) → G9Out r5 → g12 (TailA:2195), G12Weight", "b: p = 5, abelian surfaces (base changes of QM A)",
    "HT decomposition at p = 5, g = 2", "still deep", "tree: hodge-split Ysp coordinates, TailT", "Tate 1967 / Faltings HT for abelian varieties", "T4", "keep cited", "free", "—", "S (agent EF)")
row("R09", "deRhamH1AbVarT", "research", "ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT", D+"TailS.lean:1992", "H-123", "—", "published form (transported)",
    "r10 → hdR in g9Glue_of_fieldEmb → Pan's de Rham hypothesis (TailA:2195)", "b: p = 5, same A'", "de Rham at p = 5 for these A'", "still deep", "pkg-I4 B_dR material", "Faltings/Tsuji comparison", "T4", "keep cited", "free", "—", "S (agent EF)")
row("R10", "r11r12", "research", "PkgI4.PanBerger", "ZInQKernel/Contrib/G9/I4Layer.lean:1412", "H-9", "—", "composite",
    "g12 hPB 5 … (TailA:2195)", "b: p = 5, ρ = r5", "Pan∘Berger at p = 5 for r5", "still deep", "none (no B_st)", "B_st, Pan 2022", "T4", "keep cited", "free", "—", "S (agent EF)")
row("R11", "eigenformHTNew", "research", "ZInQ.Contrib.HodgeSplit.EigenformHTNew", D+"TailS.lean:1275", "H-127 (F split H-158, H-159)", "—", "consequence of one theorem",
    "r13 → g12 / g12Weight_of hHT 5 (TailB:5023)", "b: ℓ = 5, k ≥ 2", "Kato HT weights at ℓ = 5", "still deep",
    "c-to-printed2: eigenformHTNew_of_printedSS (KatoRealizationCohSS + Tate leaves), htDual_proof (branch)", "Kato's V_f", "T4", "fold c-to-printed2, keep cited", "in flight: c-to-printed2 (done on branch, w63 §5)", "—", "V: c-to-printed2 fleet note read")
row("R12", "dsThm965", "research", "ZInQ.Contrib.HodgeSplit.DSThm965", D+"TailS.lean:1110", "H-125", "—", "published form",
    "r14Det_of_printed → G12Det, G12Weight, iso_R14; eigenformHT_of_new", "b: ℓ ∈ {3, 5}; k = 2 at ℓ = 3", "Deligne/Shimura ρ_f at ℓ = 3, 5", "still deep", "none (no Hecke operators/modular curves over ℚ in Mathlib)", "Eichler–Shimura/Deligne construction", "T4", "keep cited", "free", "—", "S (agent EF)")
row("R13", "dsThm966", "research", "ZInQ.Contrib.HodgeSplit.DSThm966", D+"TailS.lean:1128", "H-126", "—", "published form",
    "R14DetWt1, r15 → k = 1 branch of g12Weight_of (TailB:5007)", "b: ℓ = 5, k = 1 only (to exclude k = 1)", "drop if Pan's output is read as k ≥ 2 (reviewer call on r11r12's reading)", "reading decision", "—", "Deligne–Serre", "T4 (T1 to remove after a reading decision)", "remove (owner/reviewer decision)", "free", "—", "S (agent EF)")
row("R14", "r16", "research", "LeafModCurves.R16_EichlerShimuraJ1'", "ZInQKernel/HDecomp/ModCurves/Leaves.lean:179", "H-13", "—", "composite",
    "commonConstituent_of_attached (TailA:3418) via g13", "b: ℓ = 5, weight 2; dim/det clauses unused", "trace and rank clauses at ℓ = 5", "still deep", "none", "Hecke algebra, J1(N) quotients, Eichler–Shimura", "T4", "keep cited", "free", "—", "S (agent EF)")
row("R15", "r17", "research", "LadicCond.CarayolR17'", "ZInQKernel/HDecomp/Conductor/LadicCond.lean:456", "H-21 (F split H-157)", "—", "consequence of one theorem",
    "g15 (TailA:3551), factorization_eq_condAt", "b: weight 2, ℓ = 5 (p ≠ 5) / 3 (p = 5), only v_p(N) ≤ condExp", "inequality form", "still deep",
    "c-to-printed2 carayolR17'_of_realization (branch)", "local Langlands / Carayol", "T4", "fold c-to-printed2, keep cited", "in flight: c-to-printed2", "—", "V: fleet note read")
row("R16", "semistableNeronBaseChange", "research", "ZInQ.HeightSplit.SemistableNeronBaseChange", D+"TailY.lean:145", "H-107 (F split H-165, H-166)", "—", "consequence of one theorem",
    "identification → all six height rows", "b: A in the height rows", "—", "—", "w63: replaced by blr_1_2_4, sga3_VIB_3_10, sga7_IX_3_3, egaIV_8_10_5_openImm (+ geomConnOfRationalPoint)", "—", "—", "superseded", "done in w63 (c-to-printed)", "—", "V: leaf-fold11 §1 read")
row("R17", "bostLowerBound", "research", "ZInQ.HeightSplit.BostLowerBound", D+"TailY.lean:442", "H-112", "—", "published form",
    "r21_of_leaves' → transfer_core (LPrefix:12153)", "b: Poincaré complement Z ⊂ J1(N)_L", "h_F(Z) ≥ −(3/2) dim Z", "still deep", "kernel stableFaltingsHeight", "slope theory", "T4", "keep cited", "free", "—", "V: transfer_core read")
row("R18", "javanpeykarBound", "research", "ZInQ.HeightSplit.JavanpeykarBound", D+"TailY.lean:521", "H-109", "—", "published form (specialization)",
    "r18_of_leaves → javanpeykarJ1", "b: J1(N)/ℚ", "Javanpeykar for J1(N)", "still deep", "—", "Arakelov theory of curves", "T4", "keep cited", "free", "—", "S (agent CD)")
row("R19", "faltingsLemma5BC", "research", "ZInQ.HeightSplit.FaltingsLemma5BC", D+"TailY.lean:609", "H-111 (F split H-167)", "—", "consequence of one theorem",
    "r20_of_leaves' → transfer_core: only (abs_le.mp hvar).1", "b, one-sided", "upper half only", "—", "w63: faltingsLemma5Printed + raynaudKernelBound", "—", "—", "superseded", "done in w63 (c-to-printed)", "—", "V: transfer_core read")
row("R20", "pazukiCor13Upper", "research", "ZInQ.HeightSplit.PazukiCor13Upper", D+"TailY.lean:730", "H-113", "—", "published form (half)",
    "r22_of_upper → thetaPazuki", "b: fibre QM surface A (dim 2)", "for that A", "still deep", "—", "theta heights", "T4", "keep cited (settle log 4 reading)", "free", "—", "S (agent CD)")
row("R21", "gaudronRemondThm14", "research", "ZInQ.HeightSplit.GaudronRemondThm14", D+"TailY.lean:786", "H-110", "—", "published form",
    "r19_of_leaves → transfer_core (degree bound); reverseIsogeny_of_leaves3 (existence)", "b: (J1(N)_L, P)", "isogeny degree bound", "still deep", "—", "Gaudron–Rémond", "T4", "keep cited", "free", "—", "V: transfer_core read")
row("R22", "semistableReductionDVR", "research", "ReductSplit.SemistableReductionDVR", D+"TailZ7.lean:278", "H-146", "—", "published form (pending base review)",
    "SS1 (semistableReductionThm_final) (+ dead r8)", "b: DVRs of number fields", "—", "—", "sh-route strict-henselization pieces (branch)", "—", "T4", "not ranked", "under review (reduct-b, sh-route)", "—", "S (agent CD)")
row("R23", "semistableUnipotent", "research", "ReductSplit.SemistableUnipotent", D+"TailZ7.lean:253", "H-147", "—", "published form (pending base review)",
    "r6 (raynaudCriterion_leaves) (+ dead r8)", "b", "—", "—", "sh-route", "—", "T3/T4", "not ranked", "under review (reduct-b)", "—", "S (agent CD)")
row("R24", "neronSchemeModelExistsDVR", "research", "ReductSplit.NeronSchemeModelExistsDVR", D+"TailZ7.lean:238", "H-148", "—", "published form (pending base review)",
    "r6 (raynaudCriterion_leaves), SS1, SS3 (TailZ15:98-116); r8 dead", "b: DVRs of number fields (agent CD)",
    "∀ L number field, O DVR of L, A/L: Néron scheme model over O (number-field form)", "consequence of N1 + BLR 1.2/4",
    "w63 BLR_1_2_4 (.mp), N1 = neronSchemeExtensionExists, pattern neronLocalizesDVR_of_printed (w63 TailZ19)", "r6 restated for number fields or Raynaud ∃-form (touches a field under review)",
    "T1-T2 (number-field form)", "reduce to N1 + blr_1_2_4", "free (consumers under review)", "A9", "S (agent CD; consumers not re-read)")
row("R25", "gonzalezRotgerCountX6", "research", "ShimuraSplit.GonzalezRotgerCountX6", D+"TailZ8.lean:44", "H-145", "—", "published form (specialization); fork ruling: candidate/composite",
    "r5fpCount_of_points (TailZ8:57) → nocm_on_witness (TailC:1403)", "b: orders R with 2^b·h(R) = 2; upper bound only",
    "GonzalezRotgerCountX6Used (≤ 3 points with CM by R when 2^b h = 2)", "computation + class-number facts",
    "Mathlib CommRing.Pic; kernel cmConductorCoprime6_of", "class number formula for orders, genus theory", "T3 (specialized) / T4", "keep cited", "free (w63 …Ab form)", "—", "S (agent A)")
row("R26", "raynaudSemistable", "research", "ReductSplit.RaynaudSemistable", D+"TailZ7.lean:265", "H-160", "—", "published form (pending base review)",
    "r6 (raynaudCriterion_leaves)", "b", "—", "—", "sh-route", "—", "T4", "not ranked", "under review (reduct-b)", "—", "S")
row("R27", "semistablePersistsDVR", "research", "ReductSplit.SemistablePersistsDVR", D+"TailZ7.lean:710", "H-162", "—", "published form (pending base review)",
    "SS1, SS3", "b", "—", "—", "sh-route", "—", "T3/T4", "not ranked", "under review (reduct-b)", "—", "S")
row("R28", "neronLocalizesDVR", "research", "ReductGlue.NeronLocalizesDVR", D+"TailZ14.lean:882", "— (leaf-fold10; ex H-163)", "—", "consequence of one theorem",
    "semistableLocalGlobal_of10 → SS1, SS3", "b", "—", "—", "w63: neronLocalizesDVR_of_printed from blr_1_2_4", "—", "—", "superseded", "done in w63 (c-to-printed)", "—", "V: leaf-fold11 read")

# ---------------- textbook bundle (OpenTextbookLeaves10, TailZ11) ----------------
row("T01", "mulEtaleAbelianScheme", "textbook", "AvSplit.T4.MulEtaleAbelianScheme", D+"TailQ.lean:1681", "H-101", "—", "published form",
    "h24 / reductionTorsionBijective_of_mulEtale (TailQ:2349) → T4 → linkedTateLocal; fixedTorsionRationalImperfect_of_mulEtale (TailZ14:236) → r6",
    "b: DVRs of number fields, m = ℓ^n (ℓ = 3, 5); the r6 use is for imperfect fields only",
    "[m] unramified/étale on abelian schemes over DVRs O of number fields, m = ℓ^n invertible", "still needs fibre lemma",
    "Contrib/AbVarBC/Tangent.lean eq_one_of_comp_intCast ([CharZero K], probe); ReductGlue.exists_rational_of_fixed_etale (probe); Mathlib formally unramified API",
    "generalize the tangent lemma to (n:K) ≠ 0; [m] unramified over O; counting (needs Mumford at κ(w))", "T3 as stated; T2 to eliminate", "eliminate (conflicts with mumfordTorsion route)", "free", "—", "V: decls #check; S: route")
row("T02", "mumfordTorsionAlgClosed", "textbook", "AvSplit.MumfordTorsionAlgClosed", D+"TailQ.lean:1257", "H-102", "—", "published form",
    "h25 (T5, T26, ~12 sites), h38 (ℂ, n = 2), raynaudCriterion_final, grothendieckMonodromy_final'", "b in substance (char 0, ℂ-embeddable, mostly g = 2)",
    "T5 over ℂ-embeddable fields (already T5Torsion.torsionStructureC_of_uniformization)", "restatement of consumers",
    "T5Torsion.torsionStructureC_of_uniformization, AvSplit.Final.h38 (probe)", "restate T5/T26/r6/r8 over ℂ-embeddable fields; g = dim A in uniformization",
    "T2 restricted; T3 full", "reduce", "free", "—", "V: decls #check; S: route")
row("T03", "homFreeFiniteAlgClosed", "textbook", "ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed", "ZInQKernel/Contrib/AVB1/AlgClosed.lean:38", "H-70", "#81? (S)", "published form",
    "t6_of_algClosed5 → T6", "b", "—", "—", "—", "—", "T3", "in flight", "in flight: cloud worker (H-70)", "—", "S")
row("T04", "charPolyIndepOfEllAlgClosed", "textbook", "ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed", "ZInQKernel/Contrib/AVB1/AlgClosed.lean:51", "H-71", "#81? (S)", "published form (specialization)",
    "t7_of_algClosed5 → T7 → linkedTateData_of_local", "b", "—", "—", "—", "—", "T3", "in flight", "in flight: cloud worker (H-71)", "—", "S")
row("T05", "poincareComplement", "textbook", "ZInQ.Contrib.AVB1.PoincareComplement", "ZInQKernel/Contrib/AVB1/Poincare.lean:42", "H-72", "#81 (V: CloudW06 NOTICE)", "published form",
    "poincareReducibility_of_published' → T8", "b", "—", "—", "CloudW06PoincareRigidity", "—", "T3", "in flight", "in flight: cloud worker (H-72)", "—", "V: NOTICE read")
row("T06", "cartierSmooth", "textbook", "AVGlue.CartierSmooth", D+"TailP.lean:305", "H-98", "—", "published form",
    "→ T8", "b", "—", "—", "Mathlib smooth_of_grpObj (agent B; not checked)", "—", "T2", "in flight", "in flight: cloud worker", "—", "S")
row("T07", "geomConnOfRationalPoint", "textbook", "AVGlue.GeomConnOfRationalPoint", D+"TailP.lean:910", "H-99", "—", "published form (specialization)",
    "→ T8; w63 also SS2 (IdentityComponentGroupModel)", "b", "—", "—", "—", "—", "T2", "in flight", "in flight: cloud worker", "—", "S")
row("T08", "groupSchemeEquidim", "textbook", "AVGlue.GroupSchemeEquidim", D+"TailP.lean:921", "H-100", "—", "published form (specialization)",
    "→ T8", "b", "—", "—", "—", "—", "T2", "in flight", "in flight: cloud worker", "—", "S")
row("T09", "uniformizationLeafAll", "textbook", "BPAnalytic.Uniformization.UniformizationLeafAll", "ZInQKernel/HDecomp/Analytic/Uniformization.lean:91", "H-103", "—", "published form (coordinate form)",
    "AvSplit.Final.h38 (T35: heights, period map), h69 (HomLatticeCorr) (TailX:233, 241)", "b weakly (base changes from number fields; any dim incl. J1(N))",
    "as stated", "deep", "Mathlib ZLattice; no exponential map for group schemes", "analytic uniformization of abelian varieties", "T4", "keep cited (add g = dim A clause)", "free", "—", "V: TailX:233,241 read; h38/h69 #check")
row("T10", "gagaMorphism", "textbook", "ZInQ.HomLattice.GAGAMorphism", D+"TailQ.lean:875", "H-105", "—", "published form (coordinate form)",
    "h69 → HomLatticeCorr → T11aRiemannHom, T11a_RiemannEnd", "b: complex abelian surfaces with QM", "dim 2 restatement", "deep", "no GAGA in Mathlib", "GAGA", "T3-T4", "keep cited", "free", "—", "S (agent B)")
row("T11", "bdRInvariants", "textbook", "∀ p, ZInQ.Contrib.HodgeSplit.BdRInvariants p", D+"TailT.lean:1571", "H-124", "—", "published form",
    "t23_all_of_bdrInvariants (TailX:235) → t23 → g8_g11/g8_g12 hT23 (TailA:2203-2250, TailD:138/172) → G9Glue's 2nd argument, unused by g9Glue_of_fieldEmb (Contrib/G9/Reduction.lean:128, binder _hT23)",
    "UNUSED in substance (syntactic projection only)", "nothing: delete by plumbing", "plumbing",
    "ZInQ.Contrib.G9.g9Glue_of_fieldEmb (probe)", "copies of g8_g11, g8_g12, afterG7_of3 … with G9Glue minus its T23 argument, up to a bundle without bdRInvariants",
    "T1", "remove by plumbing", "free", "A1", "V: read + ClosureProbe (only g8_g11, g8_g12, g8_g12_of_leaves3, afterG7_of3 consume t23; G9Glue proof in closure = TailC L14082 copy, _hT23 unused)")
row("T12", "yuThm11", "textbook", "HDec.QMSplit.Yu.YuThm11", D+"TailU.lean:443", "H-128", "—", "published form",
    "qmDichotomyYu_of_yu (TailX:237, drops the splitting clause) → t27: TailC:1700 (NoCM), kernelFieldExists, qmEndRank_of (TailF:4082)",
    "b: (a,b) = (2,−3), k algebraic over ℚ, A with an O-action; splitting clause unused",
    "YuB6Alg: ∀ k alg. closed char 0 algebraic over ℚ, A dim 2 with injective O →+* End A, End0 A ≅ B or M2(ℚ(√d)), d < 0", "theorem with an in-tree route",
    "qmComplexUnif_of_textbook, qmSkolemNoetherC_proof, qmClassNumberOne_proof (probe); T11b_Rigidity field", "lattice set-up as qmCentralizerCMC + double centralizer End0 = B·com0 + transport by T11b",
    "T2", "specialize, then prove (after qmCentralizerCMC)", "free", "A10", "V: decls #check; S: route")
row("T13", "genusX1Field", "textbook", "ZInQ.Contrib.CurvesG.GenusX1Field", "ZInQKernel/Contrib/CurvesG/GenusSplit.lean:59", "H-79", "—", "composite",
    "t34_of_split5 → T34 (TailD's two uses)", "b", "dim J1(N) ≤ N² suffices", "—", "genus-route OneProof/Genus/* (w63)", "—", "—", "done", "done in w63 (genus-fold)", "—", "V: leaf-fold11 read")
row("T14", "regularSmoothPerfect", "textbook", "CurveSplit.RegularSmoothPerfect", D+"TailR.lean:1471", "H-118", "—", "published form (half)",
    "normalCurveSmoothQ_of_regularSmooth → T38 (via TextbookLeaves.belyiX1)", "b: curves over ℚ", "—", "—", "—", "—", "T2", "in flight", "in flight: cloud worker", "—", "S")
row("T15", "igusaGL2", "textbook", "ZInQ.RLeaf.IgusaGL2", "ZInQKernel/Contrib/RLeaf/IgusaSL2.lean:120", "H-117", "—", "published form",
    "x0Transitive_of_igusaGL2 → T40 (via belyiX1)", "b", "X0Transitive", "—", "—", "—", "T2-T3", "in flight", "in flight: cloud worker (X0Transitive)", "—", "S")
row("T16", "neronSchemeExtensionExists", "textbook", "ZInQ.Contrib.NeronC.NeronSchemeExtensionExists", "ZInQKernel/Contrib/NeronC/NeronGroup.lean:82", "H-77", "—", "published form (weakened)",
    "N1 → all height rows; t41 → heightAdditivity_of_h5neron", "a (all AVs over number fields)", "—", "—", "CloudW03 Néron over henselian DVR", "global Néron models", "T4 (T3 via gluing)", "keep cited", "blocked (brief: H-77)", "—", "S")

# ---------------- added bundle (OpenAddedLeaves9, TailZ13) ----------------
row("L01", "thetaRatiosAlgebraic", "added", "HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic", D+"TailA.lean:4386", "H-44 (F split H-133, H-134)", "—", "composite",
    "thetaPointOfFibre_of_qm_ratios (TailA:5010)", "b: non-CM Ω(τ) on the QM curve, j_θ ∈ ℚ∖{0}", "theta-split ThetaRatiosAtQM", "—",
    "theta-split (in tree), theta-glue ThetaEightSquare proved (branch)", "LinYangThetaCurve, IgusaAlg 5..9", "T2", "in flight", "in flight: theta-split / theta-glue (integrator)", "—", "V: theta-glue fleet read")
row("L02", "qmCentralizerCMC", "added", "HDec.QMSplit.Aut.QMCentralizerCMC", D+"TailU.lean:1484", "H-129", "—", "published form",
    "rows_of_C (TailU:1526, TailX:252) → QMAutCard, ALFixedPoints (propTSAll, TailK:323), CMOptimalEmbedding (NoCM, TailK:299)",
    "a for O (all QM surfaces by the fixed O, via ℂ)", "as stated", "theorem with an in-tree route",
    "qmComplexUnif_of_textbook (T35, T11aRiemannEnd, QMLatticeAlgebra → QMComplexUnif), qmSkolemNoetherC_proof, qmClassNumberOne_proof, h38, h69 (all probe)",
    "QMStr version of the uniformization; commutant of ι(O) in M2(ℂ) = ℂ; com q ≅ O ∩ C(τ); C(τ) = ℚ or imaginary quadratic", "T2", "prove directly", "free", "A5", "V: decls #check; S: route")
row("L03", "tateTwistInvariants", "added", "ZInQ.Contrib.HodgeSplit.TateTwistInvariants", D+"TailS.lean:69", "H-120", "—", "published form",
    "deRhamComparisonHT_of_leavesT, senTwist_of_tate, finiteImageHT_of_tate (TailX:208, 261, 263)", "b: p = 5", "—", "—", "—", "—", "T2-T3", "in flight", "in flight: cloud worker", "—", "S")
row("L04", "axSenTate", "added", "ZInQ.Contrib.HodgeSplit.AxSenTate", D+"TailS.lean:79", "H-121", "—", "published form",
    "as tateTwistInvariants", "b: p = 5", "—", "—", "—", "—", "T2", "in flight", "in flight: cloud worker", "—", "S")
row("L05", "t09SymmIsogenyExists", "added", "WeilPairing.T09_SymmIsogenyExists", D+"TailB.lean:3752", "H-53", "—", "consequence of one theorem",
    "tatePairingZl_of_leaves4 → detTate_of_leaves4 → g12Det_of (ℓ = 5, g = 2); t9 route formal", "b: ℓ = 5, dim 2, G7 model", "DetTate at ℓ = 5, g = 2", "still deep",
    "CloudW07 Picard (Pic, Pic0 of curves); c-to-printed2 T09Roadmap", "Pic0 of an abelian variety, φ_L, Weil pairing e_n", "T3", "keep cited / Pic route later", "queued: c-to-printed2 (unchanged), t09-pic (empty)", "—", "V: c-to-printed2 fleet read")
row("L06", "milneIsogenyQuasiInverse", "added", "AvSplit.MilneIsogenyQuasiInverse", D+"TailQ.lean:1207", "H-104", "—", "published form (weakened)",
    "h54 → IsogenyQuasiInverse → T8, tatePairingZl_of_leaves4", "b: char 0 only",
    "MilneIsogenyQuasiInverse restricted to [CharZero K]", "theorem (char 0)",
    "coarse-factor factorThroughSurj (scratch/coarse-factor/Factor.lean, curves over ℚ; agent B)", "factorization through surjective isogenies for abelian varieties in char 0; ker f(K̄) finite of order d",
    "T2", "prove directly (char-0 restatement)", "free", "A12", "S (agent B)")
row("L07", "x6ConicModel", "added", "X6Kummer.X6ConicModel", D+"TailE.lean:901", "H-43 (F split H-153)", "—", "consequence of one theorem",
    "x6KummerFibre_of_conic (TailE:993) → nocm_on_witness (TailC:1386)", "b: fibres over J(u), u ∈ ℚ", "residue field ℚ(i) + four points", "—",
    "x6-glue ElkiesEquationsX6, x6ConicModel_of_published (branch)", "Elkies' function field", "T4", "keep cited (x6-glue)", "in flight: x6-glue / x6-fold", "—", "V: x6-glue fleet read")
row("L08", "shimuraTaniyamaQbar", "added", "HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar", D+"TailU.lean:1603", "H-130", "—", "published form (specialization)",
    "stQM_lf7 (TailX:271) → cmDescends_of (TailO:1302) → periodMapGlue_of_leaves4 (TailK:73)", "b: QM surfaces with CM by ℤ[i], ℤ[ζ3], ℤ[√−6] (six classes)",
    "STQM / CMDescends (six objects)", "computation + deep", "descend_main (TailO:1177); T11b_Rigidity", "converse of ALFixedPoints (fixed-point route)", "T3", "specialize", "free", "—", "S (agent A)")
row("L09", "egaIV_8_10_5_xii", "added", "ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii", "ZInQKernel/Contrib/SpreadOut/Spread.lean:49", "H-65", "#80? (S)", "published form",
    "abVarSpreadsOut_of_ega4 → linkedTateLocal, SS1", "b", "—", "—", "CloudW01 spreading out", "—", "T2", "in flight", "in flight: cloud worker (H-65)", "—", "S")
row("L10", "shimuraGoodReductionNoGuard", "added", "CurveSplitGR.ShimuraGoodReductionNoGuard", D+"TailW.lean:739", "H-119", "—", "composite",
    "shimuraGoodReduction_of_noGuard (TailX:277) → heckeVertWitness_of_leaves5 (TailO:3001) → HeckeVertWitness → TailK:325", "b: Y3, every p > 324",
    "HeckeVertWitness / HeckeNoVertRam", "still deep", "w63 QMAbScheme", "integral moduli of Y3 over ℤ_(p)", "T4", "keep cited", "in flight: cloud worker", "—", "S (agent A)")
row("L11", "valenceFormulaCocompactEq", "added", "HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq", D+"TailZ2.lean:76", "H-135", "—", "published form",
    "qmHauptmodulBase3_of_leaves (TailZ3:1211), valenceFormulaGammaStar_of_leaves (TailZ3:1196) → val_le/val_eq/val_ex (TailZ2), base2_of_base3, qmDenZeroCM3_of''",
    "b: Γ* only; F ∈ ℂ[G8, G20] of exact automorphy", "ValenceFormulaGammaStarEq (Σ ord/e = m/12 for Γ*; replaces this field and shimizuCovolumeO1)", "computation + valence formula for one group",
    "Mathlib invariant measure on ℍ, IsFundamentalDomain.measure_eq, Jensen MeromorphicOn.circleAverage_log_norm (probe); no argument principle", "explicit (2,4,6) polygon; analytic engine (Jensen route)", "T3 (general) / T2-T3 (Γ*)", "specialize", "free", "—", "V: Mathlib decls #check; S: route")
row("L12", "shimizuCovolumeO1", "added", "HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1", D+"TailZ2.lean:1018", "H-136", "—", "published form",
    "gammaStarFromO1_proof' (TailZ3:1188) → GammaStarCocompactArea (TailZ2:93) → hA of the valence uses", "b: Γ1 of O, only to get vol(Γ*) = π/6",
    "GammaStarCocompactArea (TailZ2:93)", "computation (explicit polygon)",
    "chain: gammaStarGen_proof, gs_fuchsian, fix_null, index-4 transfer; Mathlib invariant measure, properly discontinuous SL2 subgroups", "Dirichlet polygon for Γ*, a.e. disjointness, area π/6", "T2", "prove directly", "free", "A7", "V: defs read; S: route")
row("L13", "igusaCMValue24", "added", "HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24", D+"TailZ3.lean:1093", "H-144", "—", "published form",
    "thetaQuotientValue24_of_igusa → G20_tau24_ne, −16/27 clause", "b: one point", "—", "—", "cm24-value CM24.igusaCMValue24_field (w63 TailZ18)", "—", "—", "done", "done (cm24-value, w63)", "—", "V: leaf-fold11 read")
row("L14", "deligneComponentsY3Printed", "added", "ShimuraGlue.DeligneComponentsY3Printed", D+"TailZ12.lean:1324", "— (leaf-fold10; ex H-59, H-155)", "—", "published form (specialization); fork ruling: candidate",
    "addedLeaves8_of_open9 (TailZ13:55) → y3Connected → heckeIrreducible_of_connected / heckeNormalization_of (TailG:8380, 8753) via propTSAll_of_pieces3 (TailK:323); also gives mcr-quot's ModelYIrreducible (GlueProbe)",
    "b: only 'Y3 connected over ℚ'", "TSHecke.Y3Connected", "still arithmetic (π0 reciprocity)", "TailZ12 pi0K3Equiv, y3Connected_of_deligne", "Deligne's π0 theorem", "T4", "keep cited", "free (w63 …Ab form)", "—", "V: TailZ13:55, GlueProbe")

# ---------------- glue ----------------
row("G01", "quotientP1Coordinate", "glue", "MCRGlue.QuotientP1Coordinate", D+"TailW.lean:202", "H-84 successor (F: H-89..H-97)", "—", "project glue",
    "modelCoordinateResidue_of_quotient' (TailX:282) → ModelCoordinateResidue → HeckeVertWitness route",
    "b: the smooth model of the canonical triple over ℤ_(p), p > 324, coordinate normalized at 0, ∞, −16/27",
    "mcr-quot: ModelCoordinateResidue from L1-L6, T5, CurveBijIso, P1SchemeQ, CMStabObj (CoverModelOfHeckeN NOT needed: ModelYIrreducible from deligneComponentsY3Printed)", "glue + leaves",
    "mcr-quot MCRQuot.lean (compiled on its scratch); CloudW07 projectiveLine/ProjectiveSpace API (probe); Mathlib Scheme.Cover.glueMorphisms",
    "P1SchemeQ (T1), CMStabObj (T2), L1 ProperCurveAF, L3, L5, L6 (T3), L2 in flight", "T3 overall (T1 for P1SchemeQ + NV removal)", "reduce (mcr-quot) and prove the glue Props", "queued per leaf-fold11 §5 (another project task); L2/L3 in flight (cloud)", "A3",
    "V: GlueProbe, MCRQuotNV (final10 without CoverModelOfHeckeN) compile; mcr-quot hCov uses read")

# ---------------- top statements ----------------
row("Z01", "h11", "top", "ZInQ.Contrib.TYZDecomp.TYZThm11Integral", "ZInQKernel/Contrib/TYZDecomp/Leaves.lean:259", "T-1", "—", "published form",
    "tyzThm35ReadingA_of_leaves (Main.lean) → lcalChoice, lcalOne_of_leaves", "a (all squarefree m ≡ 1, 3 mod 8)", "—", "deep", "—", "Waldspurger/Tunnell-type", "T4", "keep cited", "in flight: cloud worker (T-1)", "—", "S (agent TOP)")
row("Z02", "h29", "top", "ZInQ.Contrib.TYZDecomp.TYZLemma29Mod2", "ZInQKernel/Contrib/TYZDecomp/Leaves.lean:273", "T-3", "—", "composite (GLUE)",
    "lemmaN1, ell_three_mul_ell_one_odd, lemma29Mod2_iff", "a", "—", "not finite (parities of infinitely many central values)", "—", "—", "T4", "keep cited", "in flight: cloud worker (T-3)", "—", "S (agent TOP)")
row("Z03", "hS", "top", "Shimura.ShimuraReciprocityModFn", "ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean:76", "T-13 + T-14 (ex T-5)", "—", "composite (GLUE)",
    "shimuraReciprocityPic_of (ShimuraModFn.lean:122), cmValueRingClass_of_modFn (ShimuraMain.lean:131)", "b: N = 32, g ∈ {xC, yC}, D = −64n (n ≡ 5, f = 4), D = −n (n ≡ 7, f = 1), all classes J",
    "t5-glue tip: ShimuraMainCM + X0ModuliGalois (printed) + RingClassLattice (glue, no CM)", "glue + 2 printed leaves",
    "Tau Ceti ringClassField, ringClassIdeleQuotient, rayClassQuotient, exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup (named in t5-glue docstring)", "RingClassLattice (idelic vs congruence Pic O)",
    "T2 (RingClassLattice); leaves T4", "reduce to printed leaves + prove RingClassLattice", "free (t5-glue finished; its tip 39bb3cd2 NOT merged in base or w63)", "A8", "V: merge-base; RingClassLattice def read")
row("Z04", "h33", "top", "ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33", "ZInQKernel/OneProof/TYZSplit.lean:157", "T-12", "—", "published form",
    "tyzThm33Pinned_of_tyzThm33 → thm35First_of_lcal_thm33 (Thm35.lean:718)", "a (all squarefree d ≡ 5, 7)", "TYZ 3.5(1)", "deep (Yuan–Zhang–Zhang)", "—", "—", "T4", "keep cited", "free", "—", "S (agent TOP)")
row("Z05", "hL2", "top", "ZInQ.GZDecomp.FHNonvanishing", "ZInQKernel/Contrib/GZDecomp/Decomp.lean:109", "Z-1", "—", "composite (GLUE)",
    "grossZagierCd_of_leaves (Decomp.lean:279), one call hL2 N f hχ hw 4", "b: newform of C_d, level 32d², d ≡ 5 mod 8",
    "ZInQ.GZStatements.FHNonvanishingCd (Weak.lean:46, in tree)", "still deep", "GZStatements/Weak.lean (read)", "Friedberg–Hoffstein", "T4 (swap T1)", "specialize (owner swap) + keep cited", "free", "—", "V: Weak.lean read")
row("Z06", "hL3", "top", "ZInQ.GZDecomp.GrossZagierHeegner", "ZInQKernel/Contrib/GZDecomp/Decomp.lean:131", "Z-2", "—", "composite (GLUE)",
    "grossZagierCd_of_leaves (Decomp.lean:279)", "b: E = C_d, N = 32d²", "GrossZagierHeegnerCd / GrossZagierRankCd (Weak.lean:64, 83)", "still deep", "GZStatements/Weak.lean", "Gross–Zagier", "T4 (swap T1)", "specialize (owner swap) + keep cited", "free", "—", "V: Weak.lean read")

# ---------------- new in w63 (not on base; listed for the attack list) ----------------
W = "w63:"+D+"TailZ19.lean"
row("W01", "blr_1_2_4", "research (w63)", "CToPrinted.BLR_1_2_4", W+":63", "—", "—", "published form",
    "neronLocalizesDVR_of_printed (.mp only) → SemistableLocalGlobal, SS2", "b: .mp only, R = 𝓞_L", "only-if direction over 𝓞_L", "theorem",
    "CloudW01 spreading out (Stacks 01ZM/0C0C, agent CD)", "spread out, extend, glue by uniqueness", "T2", "prove the direction used", "free (w63)", "A11", "S (agent CD)")
row("W02", "faltingsLemma5Printed", "research (w63)", "CToPrinted.FaltingsLemma5Printed", W+":387", "—", "—", "published form",
    "faltingsLemma5_of_printed (TailZ19:432) → R20 → transfer_core", "b, one-sided", "isogeny upper bound for group models", "theorem (bypass)", "HeightAntitone, torusMetricSq_comap (agent CD)", "GroupModelIsogenyUpper", "T4 / T2 bypass", "keep cited", "free (w63)", "—", "S (agent CD)")
row("W03", "raynaudKernelBound", "research (w63)", "CToPrinted.RaynaudKernelBound", W+":399", "—", "—", "published form",
    "faltingsLemma5_of_printed (gives only the half transfer_core never uses)", "UNUSED in substance", "nothing: make R20 one-sided", "plumbing",
    "kerOmegaLog_nonneg (w63 TailZ19:368)", "one-sided R20 through every bundle generation", "T1", "remove by plumbing", "free (w63)", "A2", "V: transfer_core + faltingsLemma5_of_printed read")
row("W04", "sga3_VIB_3_10", "research (w63)", "CToPrinted.SGA3_VIB_3_10", W+":199", "—", "—", "published form",
    "idComp_baseChange, identityComponentOLRange_of, …DVRRange_of → SS2", "b: bases Spec 𝓞_L / DVR, connected generic fibre", "DVR / Dedekind form", "theorem", "—", "openness of G0 over a DVR", "T2 (DVR T1) / T3", "specialize + prove", "free (w63)", "—", "S (agent CD)")
row("W05", "sga7_IX_3_3", "research (w63)", "CToPrinted.SGA7_IX_3_3", W+":249", "—", "—", "published form",
    "identityComponentBaseChangeDVRRange_of → SS2", "b", "—", "deep", "—", "semi-abelian extension theory", "T4", "keep cited", "free (w63)", "—", "S (agent CD)")
row("W06", "egaIV_8_10_5_openImm", "research (w63)", "CToPrinted.EGAIV_8_10_5_openImm", W+":281", "—", "—", "published form",
    "exists_away_of_dvr → openImmersionLocalization → SS2", "b: Spec O = lim Spec 𝓞_L[1/a]", "as stated", "theorem",
    "Mathlib AlgebraicGeometry.exists_preimage_eq; CloudW01 exists_isIso_baseChange_of_isIso_limitBaseChange, baseChangeConeIsLimit (probe)", "open immersion descends along the limit (Stacks 081E-type)", "T1", "prove directly", "free (w63)", "A6", "V: decls #check; S: route")
row("W07", "mumfordRigidityCore", "research (w63)", "LeafQM.AV.R1UnivRigid.MumfordRigidityCore", "w63:"+D+"TailZ16.lean:463", "—", "—", "published form",
    "researchLeaves10_of_open11, addedLeaves9_of_open10 (TailZ17) only, to convert the …Ab fields", "b", "—", "deep (rigidity)", "CloudW06 rigidity", "—", "T3", "keep cited", "route-a-fold (w63)", "—", "S (agent A)")

out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "triage.tsv")
with open(out, "w", newline="") as fh:
    w = csv.writer(fh, delimiter="\t", lineterminator="\n")
    w.writerow(H)
    for r in R:
        w.writerow([c.replace("\t", " ") for c in r])
ids = [r[0] for r in R]
assert len(ids) == len(set(ids))
from collections import Counter
base = [r for r in R if not r[0].startswith("W")]
print(len(R), "rows;", len(base), "on base (59 fields + 6 tops expected 65)")
print("tiers (base):", Counter(r[14].split(" ")[0] for r in base))
print("status (base):", Counter(r[16].split(":")[0].split(" (")[0] for r in base))
