"""chain.py: follow the hypotheses of the chain to ZInQ.FrozenTarget and list what stays open.

Usage: python3 scratch/frontier/chain.py [A|F]   (default: both)

Scenario A ("compiled"): only theorems that compose in one Lean world today, i.e. the top chain
(scratch/frontier/TYZChain.lean, compiled) and leaf-fold4's compiled H assembly
`HDec.HSyn.sixContactMin_of_open4` (refresh r2; before it, assemble-port's `sixContactMin_of_leaves5`).
Its open set is the hypothesis list of that composite.

Scenario F ("frontier"): A plus every proof or reduction of an open Prop found on today's branches.
Each edge is a compiled theorem on its branch (per the branch's own log), but the edges live in different
Lean files ("worlds"), so their composition is NOT compiled; only the def texts are compared (check 3).

Checks (all textual, read with `git show REV:PATH`):
 1. for every edge, the theorem's explicit hypotheses (binders and arrow antecedents) have exactly the
    listed head constants, and its conclusion has the listed head;
 2. for every bundle structure, its fields are read from the source and expanded;
 3. for edges whose conclusion is a bundle field proved in another file, the `def` text of the Prop in the
    proving file is compared with the def text in the bundle's file (whitespace- and comment-normalized).
The traversal starts at ZInQ.FrozenTarget and prints the open set, which must equal the CLASS table
(the list in docs/research/frontier.md); missing or extra entries are reported.
"""
import re
import sys
import chainlib as c

MAIN = "HEAD"
G3 = ("357f5d9e", "scratch/g0-assemble3/G0Assemble3.lean")
B5 = ("93a1e33c", "scratch/cpts-transport/Bundle5.lean")
AP = ("92a27877", "scratch/assemble-port/AssemblePort.lean")  # assemble-port final flat check (27 glue fields, 1126 s)
LF4 = ("9dcf1ca8", "scratch/leaf-fold4/Leaves4.lean")  # leaf-fold4 final flat file (md5 6bbeb639, 1048 s, 26+19+20+1 fields)
LF5 = ("5a7e03d1", "scratch/leaf-fold5/Leaves5.lean")  # leaf-fold5 final flat file (md5 5999e1db, flat run 2: 1570 s, 26+21+21+2)

# ---------------------------------------------------------------- edges
# (concl, short theorem name, rev, file, [hyp heads], scenario set, note)
E = []


def edge(concl, thm, rev, path, hyps, sc="AF", note="", deffile=None):
    E.append(dict(concl=concl, thm=thm, rev=rev, file=path, hyps=hyps, sc=sc, note=note, deffile=deffile))


# --- top (compiled here): scratch/frontier/TYZChain.lean, which contains tyz-cm's and cm-bridge's
# reductions verbatim; both scenarios use it.  (TopChain.lean is the fork-main-only variant.)
# r3: the top is two kernel modules on main: atkin-li's C2 (GZ through FHNonvanishing, GrossZagierHeegner, with
# HeckeThetaNewform proved) and tyz-chain's reading A from four TYZ Props (everything else on the TYZ side proved).
edge("FrozenTarget", "frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner", MAIN,
     "ZInQKernel/Contrib/GZTheta/NewCMFinal.lean",
     ["SixContactMin", "TYZThm35ReadingA", "FHNonvanishing", "GrossZagierHeegner"])
edge("TYZThm35ReadingA", "tyzThm35ReadingA_of_leaves", MAIN, "ZInQKernel/Contrib/TYZChain/Main.lean",
     ["TYZThm11Integral", "TYZLemma29Mod2", "ShimuraReciprocityModFn", "TYZThm33Pinned"])
# (r1-r2: the top was this task's frozenTarget_of_open in scratch/frontier/TYZChain.lean, with the 7 TYZ Props of
#  cm-bridge's B1; it stays compiled there but is off the route)

# --- H
edge("SixContactMin", "sixContactMin_of_open5", *LF5,
     ["OpenResearchLeaves5", "OpenTextbookLeaves5", "OpenAddedLeaves5", "OpenGlue5"])
# (r2: leaf-fold4's sixContactMin_of_open4 at LF4, bundles OpenResearchLeaves2, OpenTextbookLeaves4, OpenAddedLeaves4,
#  OpenGlue4; leaf-fold5 compiles r2's H edges except the split of av-b1's SimpleImageIsogeny)
# (until r2 the H base was assemble-port's C4: sixContactMin_of_leaves5 at AP, bundles OpenResearchLeaves2,
#  OpenTextbookLeaves5, GluePieces5; leaf-fold4 compiles most of the F edges below into its assembly)
# textbook fields proved in Contrib (kernel world) -- F only (in W0 they are bundle fields)
KDEF = {"AbhyankarDVR": "Objects.lean", "BrauerHasse2C": "Conductor/I6Base.lean",
        "BrauerReciprocity2C": "Conductor/I6Base.lean", "LocalH2CardC": "Conductor/I6Base.lean",
        "LocalKroneckerWeber": "Conductor/I6Base.lean", "ChebotarevExists": "Conductor/I6Base.lean",
        "KroneckerWeberCyclic": "Textbook/KroneckerWeberUse.lean", "HilbertDifferentFormula": "Conductor/Breaks.lean",
        "SerreDifferentBound": "Conductor/Breaks.lean", "NewformOfEigenform": "ModCurves/C9.lean",
        "IgusaClebschSeparation": "Textbook/Igusa/Forward.lean", "LeafUnramified": "Descent/B2Glue.lean"}
for fld, thm, path in [
    ("AbhyankarDVR", "abhyankarDVR", "scratch/t-brauer-purity/T2Kernel.lean"),
    ("BrauerHasse2C", "brauerHasse2C", "ZInQKernel/Contrib/T14/Main.lean"),
    ("BrauerReciprocity2C", "brauerReciprocity2C", "ZInQKernel/Contrib/T14/Main.lean"),
    ("LocalH2CardC", "localH2CardC", "ZInQKernel/Contrib/BrauerT14T15/T15.lean"),
    ("LocalKroneckerWeber", "localKroneckerWeber", "ZInQKernel/Contrib/LocalKW/LocalKW.lean"),
    ("KroneckerWeberCyclic", "kroneckerWeberCyclic", "ZInQKernel/Contrib/KroneckerWeber/Leaves.lean"),
    ("ChebotarevExists", "chebotarevExists", "ZInQKernel/Contrib/Chebotarev/Exists.lean"),
    ("HilbertDifferentFormula", "hilbertDifferentFormula", "ZInQKernel/Contrib/Different/Bridge.lean"),
    ("SerreDifferentBound", "serreDifferentBound", "ZInQKernel/Contrib/Different/Global.lean"),
    ("NewformOfEigenform", "newformOfEigenform_leaf", "ZInQKernel/Contrib/T25/NewformOfEigenform.lean"),
    ("IgusaClebschSeparation", "igusaClebschSeparation_proved", "ZInQKernel/Contrib/T28/Assemble.lean"),
    ("LeafUnramified", "leafUnramified", "ZInQKernel/Contrib/T31/Main.lean"),
]:
    edge(fld, thm, MAIN, path, ["ℕ"] if fld == "LocalKroneckerWeber" else [], "F", "kernel-world proof of a TextbookLeaves field",
         deffile="ZInQKernel/HDecomp/" + KDEF[fld])
# x1 (T36-T40) in F: split as assemble-port does; T36, T37 proved, T39 <= T40, T40 <= IgusaTransitive
edge("X1Leaves", None, None, None, ["CurveOfFunctionFieldQ", "X1RationalCusp"], "F",
     "T36 (`ZInQ.RLeaf.t36_torsionStructure`), T37 (`ZInQ.RLeaf.T37.t37_goodReductionUnramified`) proved on main; "
     "T39 from T40 (`ZInQ.RLeaf.x1ConstantField_of_x1RationalCusp`, main). Not a single theorem: textual split.")
edge("X1RationalCusp", "x1RationalCusp_of_x0_tateMuN", "e9b071d6", "ZInQKernel/Contrib/RLeaf/T40.lean",
     ["X0Transitive", "TateMuN"], "F", deffile="ZInQKernel/HDecomp/ModCurves/X1Belyi.lean")
edge("TateMuN", "_root_.ZInQ.RLeaf.tateMuN", "7ed2ca99", "ZInQKernel/Contrib/RLeaf/TateCuspMuN.lean", [], "F")
# GluePieces5 fields, F
HBC = ("116dc2f2", "scratch/hodge-bc2/OmegaBC.lean")
edge("HodgeBCInjective", "hodgeBCInjective", "116dc2f2", "scratch/hodge-bc2/HodgeBCInjective.lean", [], "F")
edge("OmegaBaseChange", "omegaBaseChange", "116dc2f2", "scratch/hodge-bc2/IntegrationBC.lean", [], "F")
PM = "scratch/period-map/DevHeavy.lean"
edge("S8Nonzero", "s8Nonzero_proof", "cbe9fe4c", "scratch/period-glue/S8.lean", [], "F", deffile=PM)
edge("SphereFactorAffine", "sphereFactorAffine_proof", "7e1531df", "scratch/period-glue/SFA.lean", [], "F",
     "period-glue final", deffile="scratch/period-map/DevHeavy.lean")
edge("PiTwistC", "piTwistC_of", "cbe9fe4c", "scratch/period-glue/PiTwist.lean",
     ["Over", "PtEquiv", "ToP1", "R1fpProps", "R2fpProps", "TwistOrbitFinite", "FibreTransferC"], "F",
     "instantiated at the triple chosen from R1R2fpRep (r1r2): Y, Φ, π, R1fpProps, R2fpProps come from r1r2", deffile=PM)
for d in ["Over", "PtEquiv", "ToP1", "R1fpProps", "R2fpProps", "R1heckeProps", "R1R2fp"]:
    edge(d, None, None, None, ["R1R2fpRep"], "F", "data/clauses extracted from the research leaf r1r2 (R1R2fp_of_rep, Classical.choice)")
edge("QMTwistLattice", "qmTwistLattice_of'", "7e1531df", "scratch/period-glue/QMTwist.lean",
     ["T11aRiemannHom", "LeafSkolemNoether"], "F", deffile=PM)
edge("LeafSkolemNoether", "leafSkolemNoether", MAIN, "ZInQKernel/HDecomp/Textbook/SkolemNoether.lean", [], "F")
edge("TwistOrbitFinite", "twistOrbitFinite_of'", "7e1531df", "scratch/period-glue/PiTwist.lean",
     ["Over", "PtEquiv", "R1heckeProps", "TorsionStructure", "AutOInnerFinite"], "F")
edge("FibreTransferC", "fibreTransferC_proof", "7e1531df", "scratch/period-glue/PiTwist.lean", ["Over", "ToP1"], "F")
edge("AutOInnerFinite", "autOInnerFinite", MAIN, "scratch/aut-o-finite/AutOFinite.lean", [], "F")
edge("S8WeightExact", "s8WeightExact_of", "cbe9fe4c", "scratch/period-glue/W8.lean",
     ["ThetaModularity", "GammaStarGen"], "F", deffile=PM)
PTS = ("3d41b3d5", "scratch/prop-ts-glue/PropTSGlue.lean")
edge("VerticalResidueSeparable", "verticalResidueSeparable", "1b8a3b3d", "scratch/ts-sn/TSSN.lean", [], "F")
edge("SNSpecialize", "snSpecialize", "1b8a3b3d", "scratch/ts-sn/TSSN.lean", [], "F")
TSK = ("1bbe3543", "scratch/ts-kummer/KummerTS.lean")  # d9c06585 is not on the fork; 1bbe3543 is ts-kummer final
for p, t in [("KummerAbhyankarFinGlue", "kummerAbhyankarFinGlue"), ("KummerOtherBranchFin", "kummerOtherBranchFin"),
             ("KummerVerticalFin", "kummerVerticalFin"), ("KummerAbhyankarInfGlue", "kummerAbhyankarInfGlue"),
             ("KummerOtherBranchInf", "kummerOtherBranchInf"), ("KummerVerticalInf", "kummerVerticalInf")]:
    edge(p, t, *TSK, [], "F")
edge("KummerCompositum", "kummerCompositum", "1bbe3543", "scratch/ts-kummer/KummerTS.lean", [], "F")
HR = ("6c2c1d76", "scratch/hecke-rest/HeckeRestAll.lean")
edge("CurveNormChart", "curveNormChart", *HR, [], "F")
edge("CurveChartInf", "curveChartInf", *HR, [], "F")
edge("HeckeFibreSizes", "heckeFibreSizes_of", *HR, ["TorsionStructure", "QMAutCard", "SerreRigidity3", "ALFixedPoints"], "F")
TSH = ("ff8e6731", "scratch/ts-hecke/TSHecke.lean")
edge("HeckeDegree", "heckeDegree_of_torsion", *TSH, ["TorsionStructure"], "F")
edge("HeckeIrreducible", "heckeIrreducible_of_connected", *TSH, ["Y3Connected"], "F")
edge("HeckeNormalizationIrr", "heckeNormalizationIrr_of", *TSH, ["CurveGaloisChart", "TorsionStructure"], "F")
edge("CurveGaloisChart", "curveGaloisChart_of", *TSH, ["CurveNormChart"], "F")
edge("HeckeBranch", "heckeBranch_of'", *TSH, ["R1R2fp", "CurveChartInf", "HeckeFibreSizes", "TorsionStructure"], "F")
edge("HomLinearLift", "homLinearLift_of_holoHomLift", "110ae272", "scratch/conj-pieces/Holo.lean", ["HoloHomLift"], "F")
GR = ("53ba766f", "scratch/lt-goodred/GoodRed.lean")
edge("GoodRedTorsion", "goodRedTorsion", *GR, [], "F")
edge("QMEndRank", "qmEndRank_of_leaves", *GR, ["HomFreeFinite", "QMDichotomyYu"], "F")
# route T for the linked-Tate block: LinkedTateLocal replaces fields linkedFrob, kernelFieldBreaks, tateRamAtThree
edge("UpperBreakBound+BetaSignAtTwo", "linkedTateLocal_of_tateBridge35", "3d1b90b5",
     "scratch/lt-local/LtLocal4.lean",
     ["RaynaudCriterion", "TorsionStructure", "UnramRoots", "UnramRoots", "TateBridge35", "FibreSimple", "QMEndRank"],
     "F", "route T: proves g0-assemble2's `LinkedTateLocal`, which g0-assemble3 rebuilt from the three fields; "
          "FibreSimple is derived inside g0-assemble3's assembly")
edge("UnramRoots", "unramRoots", "b066d686", "scratch/unram-roots/UnramRoots.lean", [], "F")
edge("TateBridge35", "tateBridge35_of_neron_nmp", "60340bed", "scratch/frob-pieces/FrobPiecesFull.lean",
     ["TateModuleFree", "AbVarSpreadsOut", "ProperSmoothGenConnected", "ReductionTorsionBijective",
      "NeronMappingAbelianScheme"], "F")
edge("ProperSmoothGenConnected", "properSmoothGenConnected_of_zariskiConnectedness", "3802f2bc",
     "ZInQKernel/Contrib/ZariskiConn/Basic.lean", ["ZariskiConnectedness"], "F", deffile="scratch/frob-pieces/FrobPiecesFull.lean")
edge("AbVarSpreadsOut", "frobPiecesNeron_abVarSpreadsOut", "aa304ed7", "scratch/spread-out/SpreadOutFull.lean",
     ["EGAIV_8_8_2_ii", "EGAIV_8_10_5_xii", "EGAIV_17_7_8_ii"], "F")
edge("FibreSimple", None, None, None, [], "F", "derived inside g0-assemble3's `gluePieces_of_gluePieces4` (not an open Prop)")
edge("TwistDescent", "twistDescent", "fdd133f1", "scratch/twist-descent/Dev.lean", [], "F")
edge("TateModuleFree", "tateModuleFree_of_torsionStructure", "58ac8d0b", "scratch/t5-torsion/Tate.lean",
     ["TorsionStructure"], "F", deffile="ZInQKernel/HDecomp/Objects.lean")
# field 3 bypassed by T35 in the HDec world (leaf-fold2)
edge("AnalyticUniformizationOfDim", "productMetrizationOfProductUnif_of_t35", "b38ee0c4",
     "scratch/leaf-fold2/parts/b20_fold.lean", ["UniformizationExists"], "F",
     "bypass, not a proof: in the HDec world ProductMetrizationOfProductUnif (the field's only consumer) follows from T35")

# --- r2 (w48-w51 and smooth-fibre): reductions of leaf-fold4 fields. Kernel-world files (Contrib/AVB1, CurvesG,
# NeronC, SmoothFibre) prove the kernel's Prop; deffile is the kernel definition compared with leaf-fold4's copy.
OBJ = "ZInQKernel/HDecomp/Objects.lean"
edge("HomFreeFinite", "homFreeFinite_of_algClosed", MAIN, "ZInQKernel/Contrib/AVB1/AlgClosed.lean",
     ["HomFreeFiniteAlgClosed"], "F", "av-b1", deffile=OBJ)
edge("CharPolyIndepOfEll", "charPolyIndepOfEll_of_algClosed", MAIN, "ZInQKernel/Contrib/AVB1/AlgClosed.lean",
     ["CharPolyIndepOfEllAlgClosed"], "F", "av-b1", deffile=OBJ)
edge("PoincareReducibility", "poincareReducibility_of_pieces", MAIN, "ZInQKernel/Contrib/AVB1/Poincare.lean",
     ["PoincareComplement", "ImageFactorization", "SimpleSurjIsogeny"], "F",
     "av-b1 (also from PoincareComplement + SimpleImageIsogeny, which follows from the other two)", deffile=OBJ)
AVB2 = (MAIN, "scratch/av-b2/olean/AVB2Main.lean")  # on leaf-fold3's olean chain (import TailI)
L3 = "scratch/leaf-fold3/Leaves3.lean"
edge("T09_WeilPairing", "t9_of_leaves3", *AVB2, ["T09_SymmIsogenyExists", "IsogenyQuasiInverse"], "F",
     "av-b2: glue proved from two fields already open", deffile=L3)
edge("SerreRigidity3", "serreRigidity3_of_T35", *AVB2, ["UniformizationExists", "HomLatticeCorr"], "F",
     "av-b2: glue proved from two fields already open", deffile=L3)
edge("T11b_Rigidity", "t11b_of_exists", *AVB2, ["T11bExists"], "F", "av-b2: uniqueness half proved", deffile=L3)
edge("CurveOfFunctionFieldQ", "curveOfFunctionFieldQ_of_split", MAIN, "ZInQKernel/Contrib/CurvesG/CurveSplit.lean",
     ["NormalModelOfFunctionFieldQ", "NormalCurveSmoothQ", "GeomConnectedOfConstantFieldQ"], "F",
     "curves-g: the rational-point clause is proved", deffile="ZInQKernel/HDecomp/ModCurves/X1Belyi.lean")
edge("DimJ1Genus", "dimJ1Genus_of_split", MAIN, "ZInQKernel/Contrib/CurvesG/GenusSplit.lean",
     ["DimJacobianEqGenus", "GenusX1Field"], "F", "curves-g", deffile="ZInQKernel/HDecomp/ModCurves/Leaves.lean")
edge("NeronMappingAbelianScheme", "neronMappingAbelianScheme_of_surj", MAIN,
     "ZInQKernel/Contrib/NeronC/NMPInjective.lean", ["NeronMappingAbelianSchemeSurj"], "F",
     "neron-c: injective half proved", deffile=OBJ)
edge("NeronModelExists", "neronModelExists_of_extension", MAIN, "ZInQKernel/Contrib/NeronC/NeronGroup.lean",
     ["NeronSchemeExtensionExists"], "F", "neron-c: group law and uniqueness proved",
     deffile="ZInQKernel/HDecomp/Faltings/H5Neron.lean")
edge("HeckeVertWitness", "heckeVertWitness_of_leaves", MAIN, "scratch/vert-witness/VertWitness.lean",
     ["ShimuraGoodReduction", "R1R2fp", "SmoothFibreReduced", "ModelCoordinate", "ModelComparison"], "F",
     "vert-witness; R1R2fp comes from the research leaf r1r2", deffile="scratch/vert-witness/VertWitness.lean")
edge("SmoothFibreReduced", "smoothFibreReduced", "82abd02c", "ZInQKernel/Contrib/SmoothFibre/Basic.lean", [], "F",
     "smoothFibreReduced, Mathlib only", deffile="ZInQKernel/Contrib/SmoothFibre/Statement.lean")
MG = ("c6231df7", "scratch/model-glue/ModelGlue6.lean")  # vert-witness's file verbatim + six parts (compiled)
edge("ModelCoordinate", "modelCoordinate_of_residue", *MG, ["ModelCoordinateResidue"], "F", "model-glue")
edge("ModelComparison", "modelComparison_of_curveBijIso", *MG, ["TorsionStructure", "CurveBijIso"], "F",
     "model-glue; TorsionStructure is the open field t5 (T5)")
# --- r2, TYZ side (each file restates the TYZ Props verbatim; pairwise def texts are compared below)
edge("TYZLcalOne", "tyzLcalOne_of_leaves", "61d0b14e", "scratch/tyz-lcal/TYZLcal.lean",
     ["TYZThm11Integral", "TYZLemma29Mod2"], "F", "tyz-lcal: proved from the other two L-leaves")
edge("Lemma321Five", "lemma321Five_of_shimuraModFn'", "521eacc0", "scratch/tyz-321/L321.lean",
     ["ShimuraReciprocityModFn"], "F", "tyz-321: proved from the CM leaf")
edge("Thm35First", "thm35First_of_lcal_thm33", "a8101726", "scratch/tyz-35/Thm35.lean",
     ["TYZThm33Pinned"], "F", "tyz-35: from TYZ Thm 3.3 with Lemma 3.14 for the pinned points")
# --- r3 (w53-w54): av-b1's glue SimpleImageIsogeny (a field of leaf-fold5's OpenGlue5) from its two pieces, and
# leafq-check's results on leaf-fold4's LEAF? fields
edge("SimpleImageIsogeny", "simpleImageIsogeny_of_pieces", MAIN, "ZInQKernel/Contrib/AVB1/Poincare.lean",
     ["ImageFactorization", "SimpleSurjIsogeny"], "F", "av-b1", deffile="ZInQKernel/Contrib/AVB1/Poincare.lean")
LQ = (MAIN, "scratch/leafq-check/Fold.lean")  # imports leaf-fold4's chain (TailK): its Props are the chain's own constants,
# which leaf-fold5 keeps, so there is no copied def text to compare
edge("GammaStarGen", "gammaStarGen_proof", *LQ, [], "F", "leafq-check: a finite descent, Mathlib only")
edge("ValenceBoundGammaStar", "valenceBound_of_formula", *LQ, ["ValenceFormulaGammaStar"], "F", "leafq-check")
edge("QMHauptmodul", "qmHauptmodul_of_base2", *LQ, ["QMHauptmodulBase2"], "F", "leafq-check")
edge("QMHauptmodulBase2", "base2_of_base3", *LQ,
     ["ThetaModularity", "GammaStarGen", "ValenceBoundGammaStar", "QMHauptmodulBase3"], "F", "leafq-check")
LQC = (MAIN, "scratch/leafq-check/CMDescendsGlue.lean")
edge("CMDescends", "cmDescends_of", *LQC, ["STQM", "T11b_Rigidity", "TorsionDescends", "R1R2fpRep"], "F",
     "leafq-check; T11b_Rigidity from leaf-fold5's T11bExists through av-b2's edge")
edge("TorsionDescends", "torsionDescends_of_t5", *LQC, ["TorsionStructure"], "F", "leafq-check")
# Not folded (variants, recorded in the report): tyz-318's lemma318Literal_HHprime_of_sqrtTwoNotIn
# (94b05c87, scratch/tyz-318/Lemma318.lean) trades the LEAF Lemma318Literal for the GLUE SqrtTwoNotInHHprime;
# shimura-modfn's shimuraReciprocityModFn_of_split (6bc73469) splits the CM leaf into MainTheoremCMj, RatX0Rep and the
# leaf restricted to singular points, and its report recommends keeping the CM leaf.

# ---------------------------------------------------------------- bundles
STRUCTS = {
    "OpenResearchLeaves5": (LF5, "OpenResearchLeaves5"),
    "OpenTextbookLeaves5": (LF5, "OpenTextbookLeaves5"),
    "OpenAddedLeaves5": (LF5, "OpenAddedLeaves5"),
    "OpenGlue5": (LF5, "OpenGlue5"),
}
# fields never projected on the route (h-leaves agent, grep of the flat file; g0-assemble3 §6)
UNUSED = {"r1rec", "r3", "r5", "r7b", "r8", "t10"}  # never projected in g0-assemble3; assemble-port, leaf-fold4 and leaf-fold5 have the same consumers
# (r2: in leaf-fold4's flat file r1rec, r7b, r8 occur only as `f := r.f` in three structure literals, t10 only there
#  and in T10_groupIso_of_tateDuality)
# fields that become used on route F (an F edge takes them as hypotheses)
USED_IN_F = set()

# ---------------------------------------------------------------- classification of open nodes (the report's list)
# label -> (premise, strict class)
CLASS = {}
for k in ["FHNonvanishing", "GrossZagierHeegner"]:
    CLASS[k] = ("GZ", "GLUE")
for k, v in [("TYZThm11Integral", "LEAF"), ("TYZLcalOne", "LEAF"), ("TYZLemma29Mod2", "GLUE"),
             ("Lemma318Literal", "LEAF"), ("ShimuraReciprocityModFn", "GLUE"), ("EtaModelInvariant", "GLUE"),
             ("EtaCuspGrowth", "GLUE"), ("EtaModelFricke", "GLUE"), ("Thm35First", "GLUE"), ("Lemma321Five", "GLUE"),
             ("TYZThm36Seven", "GLUE"), ("BetaOnGenus7", "GLUE")]:
    CLASS[k] = ("TYZ", v)
# TYZ, scenario A extra
for k in ["CMFieldOfDefinition", "TYZSigmaFixesZn", "GenusPointLeafCM"]:
    CLASS.setdefault(k, ("TYZ", "GLUE"))
CLASS["TYZThm33Pinned"] = ("TYZ", "GLUE")  # r2 (tyz-35)


def head_of_type(ty):
    t = ty.strip()
    t = re.sub(r"\.\{[^}]*\}", "", t)
    # strip leading ∀ binders and take the last arrow component
    while t.startswith("∀"):
        depth = 0
        for i, ch in enumerate(t):
            if ch in "([{⟨":
                depth += 1
            elif ch in ")]}⟩":
                depth -= 1
            elif ch == "," and depth == 0:
                t = t[i + 1:].strip()
                break
        else:
            break
    parts, depth, cur = [], 0, ""
    for ch in t:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "→" and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    return c.short_of(c.head(parts[-1].strip().lstrip("(")))


def check_edges(sc):
    bad = 0
    for e in E:
        if sc not in e["sc"] or e["thm"] is None:
            continue
        try:
            txt = c.show(e["rev"], e["file"])
        except FileNotFoundError as ex:
            print("MISSING FILE", ex)
            bad += 1
            continue
        sig = c.signature(txt, e["thm"])
        if sig is None:
            print(f"MISSING THEOREM {e['thm']} in {e['rev']}:{e['file']}")
            bad += 1
            continue
        hyps, concl = c.split_binders(sig, e["thm"])
        hh = sorted(head_of_type(h) for h in hyps)
        want = sorted(e["hyps"])
        ch = head_of_type(concl)
        ok_h = hh == want
        ok_c = ch == c.short_of(e["concl"]) or "+" in e["concl"] or e["concl"] in ("AnalyticUniformizationOfDim",)
        if not (ok_h and ok_c):
            bad += 1
            print(f"MISMATCH {e['thm']} ({e['rev']}:{e['file']}): hyps {hh} vs listed {want}; concl {ch} vs {e['concl']}")
    return bad


def expand(sc):
    """Traverse from FrozenTarget. Returns (open nodes with provenance, bundle field rows)."""
    by = {}
    for e in E:
        if sc in e["sc"]:
            by.setdefault(e["concl"], e)
    fields = {}
    for sname, ((rev, path), short) in STRUCTS.items():
        fl = c.structure_fields(c.show(rev, path), short)
        fields[sname] = [(f, head_of_type(t)) for f, t in fl]
    # F: the three linked-Tate fields are replaced together by route T
    route_T = {"UpperBreakBound", "BetaSignAtTwo"}
    global REACHED
    seen, open_, rows = set(), [], []
    REACHED = seen
    stack = [("FrozenTarget", "root")]
    while stack:
        node, src = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node in fields:
            for f, h in fields[node]:
                rows.append((node, f, h))
                if sc == "F" and h in route_T:
                    stack.append(("UpperBreakBound+BetaSignAtTwo", f"{node}.{f}"))
                    continue
                stack.append((h, f"{node}.{f}"))
            continue
        e = by.get(node)
        if e is None:
            if node not in ("ℕ",):
                open_.append((node, src))
            continue
        for h in e["hyps"]:
            stack.append((h, f"{e['thm']}"))
    return open_, rows


REACHED = set()


def defcheck():
    """Compare def texts of bundle-field Props proved in another file (check 3)."""
    g3 = c.show(*LF5)
    out = []
    for e in E:
        if "F" not in e["sc"] or e["thm"] is None or "+" in e["concl"]:
            continue
        if e["concl"] not in REACHED:
            continue  # edge not on the scenario-F route
        if e["rev"] == MAIN and not e["deffile"]:
            continue
        name = c.short_of(e["concl"])
        A = c.def_texts_all(g3, name)
        if not A:
            continue  # not a Prop of g0-assemble3's world (TYZ/GZ side, or an intermediate)
        B = c.def_texts_all(c.show(e["rev"], e["deffile"] or e["file"]), name)
        a = A[0]
        b = B[0] if B else None
        if B and any(x in B for x in A):
            a = b = next(x for x in A if x in B)
        if a is None or b is None:
            out.append((name, "def not found in " + ("g0-assemble3" if a is None else e["file"])))
        else:
            out.append((name, "identical" if a == b else "DIFFERENT"))
    return out


def main():
    scs = sys.argv[1:] or ["A", "F"]
    for sc in scs:
        print(f"===== scenario {sc}")
        print("edge check mismatches:", check_edges(sc))
        open_, rows = expand(sc)
        fieldset = {}
        for s, f, h in rows:
            fieldset.setdefault(h, []).append(f"{s}.{f}")
        lst = sorted(set(n for n, _ in open_))
        print(f"open nodes: {len(lst)}")
        for n in lst:
            where = ", ".join(fieldset.get(n, [])) or "-"
            fl = [x.split('.')[-1] for x in fieldset.get(n, [])]
            tag = ""
            if fl and all(f in UNUSED for f in fl) and not (sc == "F" and any(f in USED_IN_F for f in fl)):
                tag = "  [never projected]"
            print(f"  {n:45s} {where}{tag}")
        if sc == "F":
            print("def-text comparison (proved/reduced Prop vs leaf-fold5's def; edges on the F route only):")
            for name, r in defcheck():
                print(f"  {name:35s} {r}")
            print("route T inputs and kernel leaf copies (def text vs g0-assemble3, and pairwise):")
            extra_defcheck()




EXTRA_DEFS = [("3d1b90b5", "scratch/lt-local/LtLocal4.lean", ["LinkedTateLocal", "G7Data", "FibreSimple", "QMEndRank"]),
              # kernel copies of the leaves that W-kern files (route T, ts-hecke, frob-pieces) take as hypotheses
              ("HEAD", "ZInQKernel/HDecomp/Objects.lean",
               ["TateModuleFree", "ReductionTorsionBijective", "NeronMappingAbelianScheme", "RaynaudCriterion",
                "TorsionStructure", "HomFreeFinite", "QMDichotomyYu", "CharPolyIndepOfEll"])]
# cross-world identities among the route-T files (both sides outside W0)
PAIR_DEFS = [(("60340bed", "scratch/frob-pieces/FrobPiecesFull.lean"), ("3d1b90b5", "scratch/lt-local/LtLocal4.lean"),
              ["TateBridge35"]),
             (("b066d686", "scratch/unram-roots/UnramRoots.lean"), ("3d1b90b5", "scratch/lt-local/LtLocal4.lean"),
              ["UnramRoots"]),
             # r2: smooth-fibre's kernel statement vs vert-witness's (same body, other namespace)
             (("82abd02c", "ZInQKernel/Contrib/SmoothFibre/Statement.lean"), ("HEAD", "scratch/vert-witness/VertWitness.lean"),
              ["SmoothFibreReduced"]),
             # r2: model-glue's copies of vert-witness's glue Props
             (("c6231df7", "scratch/model-glue/ModelGlue6.lean"), ("HEAD", "scratch/vert-witness/VertWitness.lean"),
              ["ModelCoordinate", "ModelComparison", "ShimuraGoodReduction"]),
             # r2: the TYZ Props in the proving files vs scratch/frontier/TYZChain.lean (the compiled top of the chain)
             # (TYZLcalOne, TYZThm11Integral, TYZLemma29Mod2: tyz-lcal and TYZChain.lean both import them from the kernel's
             #  ZInQKernel/Contrib/TYZDecomp/Leaves.lean, so they are the same constants; nothing to compare)
             (("521eacc0", "scratch/tyz-321/L321.lean"), ("HEAD", "scratch/frontier/TYZChain.lean"),
              ["Lemma321Five"]),
             # tyz-321 imports the kernel's CM leaf; TYZChain.lean carries tyz-cm's copy
             (("HEAD", "ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean"), ("HEAD", "scratch/frontier/TYZChain.lean"),
              ["ShimuraReciprocityModFn"]),
             (("a8101726", "scratch/tyz-35/Thm35.lean"), ("HEAD", "scratch/frontier/TYZChain.lean"),
              ["Thm35First"])]


def extra_defcheck():
    g3 = c.show(*LF5)
    for rev, path, names in EXTRA_DEFS:
        t = c.show(rev, path)
        for n in names:
            A, B = c.def_texts_all(g3, n), c.def_texts_all(t, n)
            print(f"  {n:20s} {rev}:{path}: {'identical' if A and B and any(x in B for x in A) else 'DIFFERENT or missing'}")
    for (ra, pa), (rb, pb), names in PAIR_DEFS:
        ta, tb = c.show(ra, pa), c.show(rb, pb)
        for n in names:
            A, B = c.def_texts_all(ta, n), c.def_texts_all(tb, n)
            print(f"  {n:20s} {ra}:{pa} vs {rb}:{pb}: {'identical' if A and B and any(x in B for x in A) else 'DIFFERENT or missing'}")


def doc_check(path="docs/research/frontier.md"):
    """Compare the list in frontier.md (rows | Z-n | , | T-n | , | H-n | ) with the scenario-F open set."""
    doc = open(path).read()
    names = {}
    for m in re.finditer(r"^\| ([ZTH])-(\d+) \| `([^`]*)`", doc, re.M):
        cell = m.group(3)
        if " : " in cell:
            cell = cell.split(" : ", 1)[1]
        names[f"{m.group(1)}-{m.group(2)}"] = head_of_type(cell)
    open_, rows = expand("F")
    fieldof = {}
    for s, f, h in rows:
        fieldof.setdefault(h, []).append(f)
    never = {h for h, fl in fieldof.items() if all(f in UNUSED and f not in USED_IN_F for f in fl)}
    want = {n for n, _ in open_} - never
    have = set(names.values())
    print(f"doc rows: {len(names)} ({len(have)} distinct heads); F open minus never-projected: {len(want)}")
    print("  in chain, not in doc:", sorted(want - have))
    print("  in doc, not in chain:", sorted(have - want))


if __name__ == "__main__" and "doc" in sys.argv:
    doc_check()


if __name__ == "__main__" and "doc" not in sys.argv:
    main()
