"""chain.py: follow the hypotheses of the chain to ZInQ.FrozenTarget and list what stays open.

Usage: python3 scratch/frontier/chain.py [A|F]   (default: both); `doc` compares frontier.md with scenario F; `onep`
compares the library theorem ZInQ.OneProof.frozenTarget with scenario A

Scenario A ("compiled"): only theorems that compose in one Lean world today, i.e. the top chain (r3: atkin-li's
C2 and tyz-chain's T0, kernel modules) and the compiled H assembly: leaf-fold6's `HDec.HSyn.sixContactMin_of_open6`
(refresh r4; r3 leaf-fold5's `sixContactMin_of_open5`, r2 leaf-fold4's `sixContactMin_of_open4`, before that
assemble-port's `sixContactMin_of_leaves5`). Its open set is the hypothesis list of that composite.

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
import functools
import re
import sys
import chainlib as c

MAIN = "HEAD"
G3 = ("357f5d9e", "scratch/g0-assemble3/G0Assemble3.lean")
B5 = ("93a1e33c", "scratch/cpts-transport/Bundle5.lean")
AP = ("92a27877", "scratch/assemble-port/AssemblePort.lean")  # assemble-port final flat check (27 glue fields, 1126 s)
LF4 = ("9dcf1ca8", "scratch/leaf-fold4/Leaves4.lean")  # leaf-fold4 final flat file (md5 6bbeb639, 1048 s, 26+19+20+1 fields)
LF5 = ("5a7e03d1", "scratch/leaf-fold5/Leaves5.lean")  # leaf-fold5 final flat file (md5 5999e1db, flat run 2: 1570 s, 26+21+21+2)
# r4: the H base is leaf-fold8 inside the library (ZInQKernel/OneProof/H/, kernel modules on main since w59). "OPH" is
# read as the text of all those modules (three bundles are in TailZ4.lean, the glue bundle OpenGlue7 in TailX.lean;
# defcheck looks for the chain's copies anywhere in them).
OPX = (MAIN, "ZInQKernel/OneProof/H/TailZ4.lean")
OPX7 = (MAIN, "ZInQKernel/OneProof/H/TailX.lean")
OPH = ("OPH", "ZInQKernel/OneProof/H/")
# qm-split's and qm-glue's files `import TailK`: leaf-fold4's chain, whose sources are in scratch/leaf-fold4/olean/.
# "LF4C" is read as the files in TailK's import closure there.
LF4C = ("LF4C", "scratch/leaf-fold4/olean/")
_show = c.show


def _git(*args):
    return c.subprocess.run(["git", "-C", c.ROOT, *args], capture_output=True, text=True).stdout.split("\n")


@functools.lru_cache(maxsize=None)
def _files(rev, path):
    return frozenset(f for f in _git("ls-tree", "-r", "--name-only", rev, path) if f.endswith(".lean"))


def _closure(roots, resolve):
    """Files in the import closure of `roots` (at MAIN); resolve(module) gives a path, or None to stop there."""
    seen, todo = set(roots), list(roots)
    while todo:
        for m in re.finditer(r"^import\s+(.+)$", _show(MAIN, todo.pop()), re.M):
            for mod in m.group(1).split():
                p = resolve(mod)
                if p and p not in seen:
                    seen.add(p)
                    todo.append(p)
    return sorted(seen)


@functools.lru_cache(maxsize=None)
def oph_kernel_imports():
    """Kernel files (outside OneProof/H) in the import closure of OneProof/H."""
    kern = _files(MAIN, "ZInQKernel/")
    res = lambda mod: (lambda p: p if p in kern else None)(mod.replace(".", "/") + ".lean")
    return frozenset(f for f in _closure(sorted(_files(MAIN, OPH[1])), res) if not f.startswith(OPH[1]))


@functools.lru_cache(maxsize=None)
def _show_virtual(rev, path):
    if rev == "OPH":
        return "\n".join(_show(MAIN, f) for f in sorted(_files(MAIN, path)) if f.count("/") == path.count("/"))
    if rev == "LF4C":
        d = _files(MAIN, path)
        fs = _closure([path + "TailK.lean"], lambda mod: (lambda p: p if p in d else None)(path + mod + ".lean"))
        return "\n".join(_show(MAIN, f) for f in fs)
    return _show(rev, path)


c.show = _show_virtual
# Revisions read here that are not on main (keep these branches): 1bbe3543 wip/ts-kummer, 7ed2ca99 wip/t40-tate,
# 92a27877 and 93a1e33c wip/assemble-port, 5a7e03d1 wip/leaf-fold5 (all on off-route edges since r4). fdd133f1
# (twist-descent) is on no branch of the fork; its edge is off the route.

# ---------------------------------------------------------------- edges
# (concl, short theorem name, rev, file, [hyp heads], scenario set, note)
E = []


def edge(concl, thm, rev, path, hyps, sc="AF", note="", deffile=None, extra=(), bound=()):
    """`extra`: hypotheses that are section variables brought in by `include ... in`, so not in the signature text.
    `bound`: binder heads that the consumer quantifies over (its hypothesis is `∀ x, P x → concl x`): checked in the
    signature, not followed."""
    E.append(dict(concl=concl, thm=thm, rev=rev, file=path, hyps=hyps, sc=sc, note=note, deffile=deffile,
                  extra=list(extra), bound=list(bound)))


# --- top (compiled here): scratch/frontier/TYZChain.lean, which contains tyz-cm's and cm-bridge's
# reductions verbatim; both scenarios use it.  (TopChain.lean is the fork-main-only variant.)
# r3: the top is two kernel modules on main: atkin-li's C2 (GZ through FHNonvanishing, GrossZagierHeegner, with
# HeckeThetaNewform proved) and tyz-chain's reading A from four TYZ Props (everything else on the TYZ side proved).
edge("FrozenTarget", "frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner", MAIN,
     "ZInQKernel/Contrib/GZTheta/NewCMFinal.lean",
     ["SixContactMin", "TYZThm35ReadingA", "FHNonvanishing", "GrossZagierHeegner"])
# r4 (w59): leaf-fold8 compiles tyz-split's derivation of T0's pinned hypothesis from the printed TYZ Theorem 3.3 into
# OneProof (TYZSplit.lean = scratch/tyz-split/T11.lean from line 2), so both scenarios take T-11 from `TYZThm33`.
# (Until w58 scenario F used tyz-split's `tyzThm35ReadingA_of_printedThm33` in scratch/tyz-split/T11.lean.)
edge("TYZThm33Pinned", "tyzThm33Pinned_of_tyzThm33", MAIN, "ZInQKernel/OneProof/TYZSplit.lean", ["TYZThm33"], "AF",
     "tyz-split, compiled in OneProof by leaf-fold8", bound=["ℤ", "IsTYZLcal"])
edge("TYZThm35ReadingA", "tyzThm35ReadingA_of_leaves", MAIN, "ZInQKernel/Contrib/TYZChain/Main.lean",
     ["TYZThm11Integral", "TYZLemma29Mod2", "ShimuraReciprocityModFn", "TYZThm33Pinned"])
# (r1-r2: the top was this task's frozenTarget_of_open in scratch/frontier/TYZChain.lean, with the 7 TYZ Props of
#  cm-bridge's B1; it stays compiled there but is off the route)

# --- H
edge("SixContactMin", "sixContactMin_of_open8", *OPX,
     ["OpenResearchLeaves8", "OpenTextbookLeaves8", "OpenAddedLeaves8", "OpenGlue7"])
# (r4 at w58: leaf-fold7's sixContactMin_of_open7 in TailX.lean, bundles OpenResearchLeaves7, OpenTextbookLeaves7,
#  OpenAddedLeaves7, OpenGlue7; leaf-fold8 folds the height rows, H-87, H-88, six Contrib proofs and T-11 into it)
# (r4: leaf-fold7 in OneProof folds av-glue, av-split, curve-split, qm-split, hodge-split and mcr-glue into leaf-fold6's
#  sixContactMin_of_open6 (bundles OpenResearchLeaves5, OpenTextbookLeaves6, OpenAddedLeaves6, OpenGlue6))
# (r3: leaf-fold5's sixContactMin_of_open5 at LF5, bundles OpenResearchLeaves5, OpenTextbookLeaves5, OpenAddedLeaves5,
#  OpenGlue5; leaf-fold6 adds leafq-check's four reductions and keeps T8 as a leaf)
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
edge("HomLinearLift", "homLinearLift_of_holoHomLift", MAIN, "scratch/conj-pieces/Holo.lean", ["HoloHomLift"], "F")  # = 110ae272
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
edge("AnalyticUniformizationOfDim", "productMetrizationOfProductUnif_of_t35", MAIN,  # r3 and before: b38ee0c4
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
# --- r4 (w59): coarse-factor, mcr-quot and cloud-w07. First in the list, so they win over the older edges below.
CF = (MAIN, "scratch/coarse-factor/Discharge.lean")  # over OneProof's chain (imports ZInQKernel.OneProof.H.TailK)
edge("R1R2fpRep", "r1r2fpRep_of_canonical''", *CF,
     ["CanonicalModelY3", "CanonicalCoarseX6", "BabaGranathX6", "GonzalezRotgerX6", "ReciprocityOfFine"], "F",
     "coarse-factor: qm-glue's theorem with CoarseFactor proved from CanonicalCoarseX6 and CurveBijIso filled in")
edge("X6ConicModel", "x6ConicModel_of_canonical''", *CF, ["R1R2fpRep", "ConicCanonical", "MobiusGlue"], "F",
     "coarse-factor")
# mcr-quot: the four glue Props under the coordinate. Its file is MCRGlue.lean verbatim plus parts; its T5 is the
# kernel's ObjBridge.TorsionStructure, which Objects.lean proves `Iff.rfl` to PkgI2.TorsionStructure.{0}.
# CoverModelOfHeckeN has no edge here: the chain derives it only through HeckeNoVertRam, downstream of the
# coordinate that mcr-quot feeds, so it stays open (glue).
MQ = (MAIN, "scratch/mcr-quot/MCRQuot.lean")
for concl, thm, hyps in [
        ("FibreAutTame", "fibreAutTame_of''", ["TorsionStructure", "CurveBijIso", "ModelYIrreducible", "CurveClosedQbarFinite"]),
        ("FibreAutFixFinite", "fibreAutFixFinite_of'", ["CurveBijIso", "ModelYIrreducible"]),
        ("CoordinateFromSections", "coordinateFromSections_of''", ["FibreAutTame", "TorsionStructure"]),
        ("CMSectionsDisjoint", "cMSectionsDisjoint_of''", ["FibreAutTame", "FibreAutFixFinite", "CMStabInvolution"]),
        ("CMStabInvolution", "cMStabInvolution_of", ["CurveBijIso", "ModelYIrreducible", "CMStabObj"]),
        ("GenericQuotientP1", "genericQuotientP1_of''",
         ["FibreAutTame", "TorsionStructure", "TameQuotientSmooth", "CurveBijIso", "P1SchemeQ"]),
        ("ModelYIrreducible", "modelYIrreducible_of_coverModelN", ["TorsionStructure", "CoverModelOfHeckeN"]),
        ("CurveClosedQbarFinite", "curveClosedQbarFinite", [])]:
    edge(concl, thm, *MQ, hyps, "F", "mcr-quot", deffile=MQ[1])
# cloud-w07 (merged in w59): two textbook fields proved in Contrib (kernel constants, see ROOT_FIELDS)
CW7 = "ZInQKernel/Contrib/CloudW07JacobiansCurves/"
edge("JacobianExists", "JacobianExists_proof", MAIN, CW7 + "JacobianExists.lean", [], "F", "cloud-w07")
edge("NormalModelOfFunctionFieldQ", "NormalModelOfFunctionFieldQ_proof", MAIN, CW7 + "NormalModel.lean", [], "F",
     "cloud-w07")
# --- r4 (w58): height-glue, qm-glue, and leaf-fold7's own reduction of its glue field. These come first: where a
# conclusion has an older edge below (height-split, qm-split), the first edge in this list is the one followed.
HG = (MAIN, "scratch/height-glue/Rows.lean")  # height-split's HeightSplit.lean + metrization + the glue proofs
for concl, thm, hyps in [("AnalyticUniformizationExists", "analyticUniformizationExists_of_t35", ["UniformizationExists"]),
                         ("AnalyticUniformizationUnique", "analyticUniformizationUnique_of_t35", ["UniformizationExists"]),
                         ("UniformizationDim", "uniformizationDim_of_t35", ["UniformizationExists"]),
                         ("MetrizationOfUniformization", "metrizationOfUniformization", []),
                         ("NeronMetrizable", "neronMetrizable_of_t35", ["UniformizationExists"])]:
    edge(concl, thm, *HG, hyps, "F", "height-glue")
edge("R5fpCount", "r5fpCount_of_t11b", MAIN, "scratch/height-glue/QMFull.lean",
     ["EichlerOptimalEmbeddingCount", "T11b_Rigidity", "CMDescent", "QMUniformizationC"], "F",
     "height-glue: QMPairEmbeddingCorrespondence (H-3) proved from T11b and two QM leaves")
QG = "scratch/qm-glue/"  # over leaf-fold4's chain (TailK), like qm-split
edge("R1R2fpRep", "r1r2fpRep_of_canonical", MAIN, QG + "ModuliCompare.lean",
     ["CanonicalModelY3", "CanonicalCoarseX6", "BabaGranathX6", "GonzalezRotgerX6", "ReciprocityOfFine", "CoarseFactor",
      "CurveBijIso"], "F", "qm-glue: qm-split's universal Props from their existential forms and CoarseFactor")
edge("X6ConicModel", "x6ConicModel_of_canonical'", MAIN, QG + "ModuliCompare.lean",
     ["R1R2fpRep", "ConicCanonical", "CoarseFactor", "CurveBijIso", "MobiusGlue"], "F", "qm-glue")
edge("ValenceFormulaGammaStar", "valenceFormulaGammaStar_of_leaves", MAIN, QG + "HauptGlue.lean",
     ["ValenceFormulaCocompactEq", "ShimizuCovolumeO1"], "F", "qm-glue: GammaStarFromO1 proved")
edge("QMHauptmodulBase3", "qmHauptmodulBase3_of_leaves", MAIN, QG + "HauptGlue.lean",
     ["ThetaModularity", "ValenceFormulaCocompactEq", "ShimizuCovolumeO1", "IgusaCMValue24"], "F",
     "qm-glue: ThetaQuotientValue24 from the published value IgusaCMValue24")
edge("MobiusGlue", "mobiusGlue_of_t5'", MAIN, "ZInQKernel/OneProof/H/TailE.lean", ["TorsionStructure"], "F",
     "image-plane, compiled in OneProof (the chain's LeafQM.AV.Pin.MobiusGlue)")
edge("QuotientP1Coordinate", "quotientP1Coordinate_of_leaves", MAIN, "ZInQKernel/OneProof/H/TailW.lean",
     ["ProperCurveAF", "FiniteQuotientExists", "TameQuotientSmooth", "SmoothModelOfP1", "TameFixedPointsDisjoint",
      "TameInertiaCyclic", "FibreAutTame", "GenericQuotientP1", "CoordinateNormalization"], "F",
     "mcr-glue, compiled in OneProof: the glue field from six leaves and three glue Props")
edge("CoordinateNormalization", "coordinateNormalization_of", MAIN, "scratch/mcr-glue/MCRGlue.lean",
     ["CMSectionsDisjoint", "CoordinateFromSections"], "F", "mcr-glue", deffile="scratch/mcr-glue/MCRGlue.lean")
# --- r4 (w55-w57): reductions of leaf-fold6's fields by the split tasks. Kernel-world files prove the kernel's Prop
# (deffile = the kernel definition, compared with the copy in Leaves6); qm-split's files import leaf-fold4's chain
# (TailK), so their Props are the chain's own constants (no copied def text to compare).
MCR = (MAIN, "scratch/mcr-glue/MCRGlue.lean")  # model-glue's ModelGlue6.lean verbatim + five parts (compiled)
edge("ModelCoordinateResidue", "modelCoordinateResidue_of_leaves''", *MCR,
     ["ProperCurveAF", "FiniteQuotientExists", "TameQuotientSmooth", "SmoothModelOfP1", "TameFixedPointsDisjoint",
      "TameInertiaCyclic", "FibreAutTame", "GenericQuotientP1", "CMSectionsDisjoint", "CoordinateFromSections"], "F",
     "mcr-glue: the residue half proved; six leaves and four glue Props", deffile=MCR[1])
AVG = (MAIN, "scratch/av-glue/Combined.lean")  # copies of av-b1's two pieces, checked Iff.rfl against the kernel's
edge("ImageFactorization", "imageFactorization_of_cartier", *AVG, ["CartierSmooth"], "F", "av-glue")
edge("SimpleSurjIsogeny", "simpleSurjIsogeny_of_published'", *AVG,
     ["CartierSmooth", "PoincareComplement", "IsogenyQuasiInverse", "GeomConnOfRationalPoint", "GroupSchemeEquidim"], "F",
     "av-glue; IsogenyQuasiInverse is WeilPairing's (the field isogenyQuasiInverse)")
AVS = (MAIN, "scratch/av-split/AvSplitAll.lean")
edge("ReductionTorsionBijective", "h24", *AVS, ["MulEtaleAbelianScheme"], "F", "av-split", deffile=OBJ)
edge("TorsionStructure", "h25", *AVS, ["MumfordTorsionAlgClosed"], "F", "av-split", deffile=OBJ)
edge("UniformizationExists", "h38", *AVS, ["UniformizationLeafAll", "MumfordTorsionAlgClosed"], "F", "av-split",
     deffile="ZInQKernel/HDecomp/LeafPush2/T.lean")
edge("IsogenyQuasiInverse", "h54", *AVS, ["MilneIsogenyQuasiInverse"], "F", "av-split (verbatim copy of the Prop)",
     deffile=AVS[1])
edge("HomLatticeCorr", "h69", *AVS, ["UniformizationLeafAll", "GAGAMorphism"], "F", "av-split",
     deffile="ZInQKernel/Contrib/HomUnify/Corr.lean")
HS = (MAIN, "scratch/height-split/HeightSplit.lean")  # the rows are the kernel's Props, imported
FAL = "ZInQKernel/HDecomp/Faltings/Leaves.lean"
SS = ["NeronModelExists", "SemistableReductionThm", "SemistableNeronBaseChange"]  # N1, SS1, SS2 (H5 identification)
edge("R18_Javanpeykar", "r18_of_leaves", *HS, ["JavanpeykarBound"] + SS + ["NeronMetrizable"], "F", "height-split",
     deffile="ZInQKernel/HDecomp/LeafPush2/R18.lean")
edge("R19_GaudronRemond", "r19_of_leaves", *HS, ["GaudronRemondThm14"] + SS, "F", "height-split", deffile=FAL)
edge("R20_FaltingsLemma5", "r20_of_leaves'", *HS, ["FaltingsLemma5BC"] + SS + ["SemistablePersists"], "F",
     "height-split", deffile=FAL)
edge("R21_Bost", "r21_of_leaves'", *HS, ["BostLowerBound"] + SS + ["AnalyticUniformizationUnique"], "F",
     "height-split (MetrizedDimUnique proved)", deffile=FAL)
edge("R22_Pazuki", "r22_of_upper", *HS, ["PazukiCor13Upper"] + SS, "F", "height-split",
     deffile="ZInQKernel/HDecomp/LeafPush2/R22.lean")
edge("StableHeightFinite", "stableHeightFinite_of'", *HS, SS + ["NeronMetrizable", "AnalyticUniformizationUnique"], "F",
     "height-split", deffile="ZInQKernel/HDecomp/Faltings/Height.lean")
edge("NeronMetrizable", "neronMetrizable_of", *HS,
     ["AnalyticUniformizationExists", "UniformizationDim", "MetrizationOfUniformization"], "F", "height-split")
edge("R5fpCount", "r5fpCount_of", MAIN, "scratch/height-split/R5Count.lean",
     ["EichlerOptimalEmbeddingCount", "QMPairEmbeddingCorrespondence"], "F", "height-split",
     deffile="ZInQKernel/HDecomp/QM/Leaves.lean")
# curve-split (w56)
CVS = "scratch/curve-split/"
edge("X0Transitive", "x0Transitive_of_igusaGL2", MAIN, CVS + "X0Split.lean", ["IgusaGL2"], "F",
     "curve-split: Igusa's theorem as printed (kernel leaf; also from IgusaSL2X)")
edge("NormalCurveSmoothQ", "normalCurveSmoothQ_of_regularSmooth", MAIN, CVS + "CurvesGSplit.lean",
     ["RegularSmoothPerfect"], "F", "curve-split")
edge("GeomConnectedOfConstantFieldQ", "geomConnectedOfConstantFieldQ_of_zariski", MAIN, CVS + "CurvesGSplit.lean",
     ["ZariskiConnectedness"], "F", "curve-split")
edge("CurveBijIso", "curveBijIso", MAIN, CVS + "CurveBij.lean", [], "F", "curve-split: Mathlib only",
     deffile=CVS + "CurveBij.lean")
# hodge-split (w56)
HOD = (MAIN, "scratch/hodge-split/HodgeSplit.lean")  # rows copied verbatim from Leaves5.lean
TS2 = ["TateTwistInvariants", "AxSenTate"]
edge("FiniteImageHT", "finiteImageHT_of_tate", *HOD, TS2, "F", "hodge-split", deffile=HOD[1])
edge("T23_FontaineClosure", "t23_all_of_bdrInvariants", *HOD, ["BdRInvariants"], "F", "hodge-split",
     deffile="ZInQKernel/Contrib/G9/I4Layer.lean")
edge("DeRhamComparisonHT", "deRhamComparisonHT_of_leavesT", *HOD, ["HodgeTateDecompAbVar"] + TS2 + ["DeRhamH1AbVarT"],
     "F", "hodge-split", deffile="ZInQKernel/Contrib/R10/Amend.lean")
edge("R14Det", "r14Det_of_printed", *HOD, ["DSThm965", "DSThm966"], "F", "hodge-split", deffile=HOD[1])
edge("SenTwist", "senTwist_of_tate", *HOD, TS2, "F", "hodge-split", deffile=HOD[1])
edge("EigenformHT", "eigenformHT_of_kato_ds", *HOD, ["EigenformHTNew", "NewformOfEigenform", "DSThm965", "DSThm966"],
     "F", "hodge-split: the newform case of Kato's theorem stays open", deffile="ZInQKernel/Contrib/G9/I4Layer.lean")
# qm-split (w56-w57)
QMS = "scratch/qm-split/"
edge("QMClassNumberOne", "qmClassNumberOne_proof", MAIN, QMS + "ClassNumberOne.lean", [], "F",
     "qm-split: 𝒪 is left norm-Euclidean")
edge("QMDichotomyYu", "qmDichotomyYu_of_yu", MAIN, QMS + "YuLeaf.lean", ["YuThm11"], "F", "qm-split")
for concl, thm in [("QMAutCard", "qmAutCard_of"), ("ALFixedPoints", "alFixedPoints_of"),
                   ("CMOptimalEmbedding", "cmOptimalEmbedding_of")]:
    edge(concl, thm, MAIN, QMS + "QMAut.lean", ["QMCentralizerCM"], "F", "qm-split")
edge("QMCentralizerCM", "qmCentralizerCM_of", MAIN, QMS + "QMAut.lean", ["QMCentralizerCMC", "T11b_Rigidity"], "F",
     "qm-split: the form over ℚ̄ from the printed form over ℂ and T11(b)")
edge("STQM", "stqm_of", MAIN, QMS + "STQM.lean", ["ShimuraTaniyamaQbar"], "F", "qm-split")
edge("ThetaModularity", "thetaModularity_of", MAIN, QMS + "ThetaSplit.lean", ["IgusaPsi4", "IgusaChi10"], "F", "qm-split")
edge("ThetaRatiosAlgebraic", "thetaRatiosAlgebraic_of", MAIN, QMS + "ThetaRatios.lean",
     ["ThetaNullNonvanishing", "ThetaFourthRatiosAlgebraic"], "F", "qm-split")
edge("ValenceFormulaGammaStar", "valenceFormulaGammaStar_of_O1", MAIN, QMS + "Haupt.lean",
     ["ValenceFormulaCocompactEq", "ShimizuCovolumeO1"], "F", "qm-split")
edge("QMHauptmodulBase3", "qmHauptmodulBase3_of_O1", MAIN, QMS + "Haupt.lean",
     ["ValenceFormulaCocompactEq", "ShimizuCovolumeO1", "ThetaModularity", "ThetaQuotientValue24"], "F",
     "qm-split; `include hT hC in`: r4's ThetaModularity and the CM value", extra=["ThetaModularity", "ThetaQuotientValue24"])
edge("R1R2fpRep", "r1r2fpRep_of'", MAIN, QMS + "ModuliSplit.lean",
     ["CanonicalModelY3", "CoarseX6OfFine", "HauptmodulOfX6", "ReciprocityOfFine", "ResidueOfX6"], "F",
     "qm-split: HeckeOfFine proved")
# (qm-split's y3Connected_of [CanonicalModelY3, ConnectedOfFine] is not followed: qm-glue proves ConnectedOfFine from
#  ConnectedCanonical, which is the row TSHecke.Y3Connected itself, so the split adds a row and removes none)
edge("R1bFamily", "r1b_of'", MAIN, QMS + "ModuliSplit.lean", ["ShimuraFamily"], "F", "qm-split: R1bTransport proved")
edge("X6ConicModel", "x6ConicModel_of", MAIN, QMS + "ModuliSplit.lean", ["R1R2fpRep", "ConicOfWitness"], "F", "qm-split")
# tyz-split (w57): the CM leaf split into its CM part and its modular-curve part
edge("ShimuraReciprocityModFn", "shimuraReciprocityModFn_of_split", MAIN, "scratch/tyz-split/T5.lean",
     ["CMModuli", "X0RatStructure"], "F", "tyz-split")
# curve-split: the guard clause of ShimuraGoodReduction follows from R1R2fp
edge("ShimuraGoodReduction", "shimuraGoodReduction_of_noGuard", MAIN, CVS + "ShimuraGR.lean",
     ["R1R2fp", "ShimuraGoodReductionNoGuard"], "F", "curve-split", deffile=CVS + "ShimuraGR.lean")
# fork PRs #6-#10 (w57): fields proved in Contrib, exact fixed Props (T11bExists: a verbatim copy of av-b2's)
CW = "ZInQKernel/Contrib/"
edge("EigenformTwist", "EigenformTwist_proof", MAIN, CW + "CloudW08EigenformTwists/EigenformTwist.lean", [], "F", "PR #6")
edge("EGAIV_8_8_2_ii", "EGAIV_8_8_2_ii_proof", MAIN, CW + "CloudW01Spread/FinitePresentation.lean", [], "F", "PR #7")
edge("EGAIV_17_7_8_ii", "EGAIV_17_7_8_ii_proof", MAIN, CW + "CloudW01Spread/Smooth.lean", [], "F", "PR #7")
edge("ZariskiConnectedness", "ZariskiConnectedness_proof", MAIN, CW + "CloudW02Connectedness/Basic.lean", [], "F", "PR #8")
edge("T11bExists", "T11bExists_proof", MAIN, CW + "CloudW06PoincareRigidity/T11bExists.lean", [], "F", "PR #9",
     deffile=CW + "CloudW06PoincareRigidity/T11bExists.lean")
edge("NeronMappingAbelianSchemeSurj", "NeronMappingAbelianSchemeSurj_proof", MAIN, CW + "CloudW03NeronSurj/Main.lean",
     [], "F", "PR #10")
# Not folded (variants, recorded in the report): tyz-318's lemma318Literal_HHprime_of_sqrtTwoNotIn
# (94b05c87, scratch/tyz-318/Lemma318.lean) trades the LEAF Lemma318Literal for the GLUE SqrtTwoNotInHHprime;
# shimura-modfn's shimuraReciprocityModFn_of_split (6bc73469) splits the CM leaf into MainTheoremCMj, RatX0Rep and the
# leaf restricted to singular points, and its report recommends keeping the CM leaf.

# ---------------------------------------------------------------- bundles
STRUCTS = {
    "OpenResearchLeaves8": (OPX, "OpenResearchLeaves8"),
    "OpenTextbookLeaves8": (OPX, "OpenTextbookLeaves8"),
    "OpenAddedLeaves8": (OPX, "OpenAddedLeaves8"),
    "OpenGlue7": (OPX7, "OpenGlue7"),
}
# fields never projected on the route (h-leaves agent, grep of the flat file; g0-assemble3 §6)
UNUSED = {"r1rec", "r3", "r5", "r7b", "r8", "t10"}  # never projected in g0-assemble3; assemble-port, leaf-fold4 and leaf-fold5 have the same consumers
# (r2: in leaf-fold4's flat file r1rec, r7b, r8 occur only as `f := r.f` in three structure literals, t10 only there
#  and in T10_groupIso_of_tateDuality)
# (r4: in OneProof/H the six occur only as `f := r.f` / `f := t.f` (or a transport `_ofK5` of it) in the bundle
#  conversions of TailD, TailE, TailI, TailK, TailN, TailO and TailX, and t10 in LPrefix's T10_groupIso_of_tateDuality;
#  leaf-fold7 left the chain from LPrefix to TailO unchanged)
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
        hh = sorted([head_of_type(h) for h in hyps] + e["extra"])
        want = sorted(e["hyps"] + e["bound"])
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
    global REACHED, FOLLOWED
    seen, open_, rows = set(), [], []
    REACHED, FOLLOWED = seen, []
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
        FOLLOWED.append(e)
        for h in e["hyps"]:
            stack.append((h, f"{e['thm']}"))
    return open_, rows


REACHED = set()
FOLLOWED = []  # the edge followed for each reached conclusion (the first in E), in traversal order


def _cmp(A, B):
    """Verdict for two lists of def texts of one name (None if either is empty)."""
    if not A or not B:
        return None
    if any(x in B for x in A):
        return "identical"
    if any(unworld(x) == unworld(y) for x in A for y in B):
        return "identical up to the prefix " + " ".join(WORLD)
    return "DIFFERENT"


@functools.lru_cache(maxsize=None)
def kernel_defs(name):
    """{file: def texts} for the kernel files in OneProof/H's import closure that define `name`."""
    pat = (r"^(@\[[^]]*\][[:space:]]*)?((private|protected|noncomputable) )*"
           r"(def|abbrev|structure|opaque|irreducible_def) %s([[:space:]:({[]|$)" % re.escape(name))
    hits = [l.split(":", 1)[1] for l in _git("grep", "-l", "-E", pat, MAIN, "--", "ZInQKernel/") if l]
    return {f: c.def_texts_all(_show(MAIN, f), name) for f in hits if f in oph_kernel_imports()}


def defcheck():
    """Check 3: a Prop proved or reduced in another Lean world is the one the H base uses (followed F edges only).
    r4: the base is OneProof/H, which imports kernel modules where the flat files had copies, so a definition in a
    kernel module that OneProof/H imports is the base's own constant."""
    g3 = c.show(*OPH)
    out = []
    for e in FOLLOWED:
        if "F" not in e["sc"] or e["thm"] is None or "+" in e["concl"]:
            continue
        if e["rev"] == MAIN and not e["deffile"]:
            continue
        name = c.short_of(e["concl"])
        df = e["deffile"] or e["file"]
        B = c.def_texts_all(c.show(e["rev"], df), name)
        A = c.def_texts_all(g3, name)
        if A:
            out.append((name, _cmp(A, B) or "def not found in " + df))
            continue
        K = kernel_defs(name)
        if not K:
            # a Prop that an F edge introduces: compare with the files of the followed edges that take it
            vs = []
            for f in sorted({x["file"] for x in FOLLOWED if name in x["hyps"] and x["rev"] == MAIN} - {df}):
                C = c.def_texts_all(c.show(MAIN, f), name)
                if C:
                    vs.append(f"{_cmp(C, B) or 'def not found in ' + df} (vs {f}, which takes it)")
            if vs:
                out.append((name, "; ".join(vs)))
            continue
        if e["rev"] == MAIN and df in K:
            out.append((name, f"the kernel's own constant ({df}), which OneProof/H imports"))
        else:
            v = _cmp([x for t in K.values() for x in t], B)
            out.append((name, f"{v or 'def not found in ' + df} (vs {', '.join(sorted(K))}, imported by OneProof/H)"))
    return out


# r4: bundle fields whose type is a kernel constant written with `_root_`, proved by a file that imports the kernel
# module defining it (fork PRs #6-#10, folded by leaf-fold8 at w59; cloud-w07): the same constant, so there is no text
# to compare
ROOT_FIELDS = {"JacobianExists": "ZInQKernel/HDecomp/ModCurves/Defs.lean",
               "NormalModelOfFunctionFieldQ": "ZInQKernel/Contrib/CurvesG/CurveSplit.lean",
               "EigenformTwist": "ZInQKernel/HDecomp/ModCurves/C9.lean",
               "EGAIV_8_8_2_ii": "ZInQKernel/Contrib/SpreadOut/Spread.lean",
               "EGAIV_17_7_8_ii": "ZInQKernel/Contrib/SpreadOut/Spread.lean",
               "ZariskiConnectedness": "ZInQKernel/Contrib/ZariskiConn/Basic.lean",
               "NeronMappingAbelianSchemeSurj": "ZInQKernel/Contrib/NeronC/NMPInjective.lean"}


def rootcheck():
    types = {}
    for (rev, path), short in STRUCTS.values():
        for f, t in c.structure_fields(c.show(rev, path), short):
            types[head_of_type(t)] = t
    out = []
    for e in FOLLOWED:
        name = c.short_of(e["concl"])
        if "F" not in e["sc"] or name not in ROOT_FIELDS:
            continue
        kf = ROOT_FIELDS[name]
        q, _ = c.qualified_def(c.show(MAIN, kf), name)
        t = types.get(name, "")
        written = re.sub(r"\.\{[^}]*\}$", "", t.split()[0]) if t else ""
        imp = re.search(r"^import\s+%s\s*$" % re.escape(kf[:-5].replace("/", ".")), c.show(e["rev"], e["file"]), re.M)
        if written == "_root_." + q and imp:
            out.append((name, f"field type `{t}` is `{q}` of {kf}, which {e['file']} imports"))
        else:
            out.append((name, f"CHECK: field type `{t}`, kernel def `{q}`, imported: {bool(imp)}"))
    return out


def chaincheck():
    """r4: qm-split's and qm-glue's files are over leaf-fold4's chain (`import TailK`). For the Props that their
    followed edges conclude or assume, compare the definition the H base uses (OneProof/H, or a kernel module it
    imports) with leaf-fold4's chain sources, or with the edge's own file where the chain has none (a verbatim copy)."""
    g3, l4 = c.show(*OPH), c.show(*LF4C)
    out, done = [], set()
    for e in FOLLOWED:
        if "F" not in e["sc"] or not e["thm"] or e["rev"] != MAIN:
            continue
        txt = c.show(e["rev"], e["file"])
        if not re.search(r"^import TailK\b", txt, re.M):
            continue
        for name in [c.short_of(e["concl"])] + e["hyps"]:
            if name in done:
                continue
            done.add(name)
            A, base = c.def_texts_all(g3, name), "OneProof/H"
            if not A:
                K = kernel_defs(name)
                A, base = [x for t in K.values() for x in t], ", ".join(sorted(K))
            if not A:
                continue  # a Prop of the edge's own file (open, or proved by a later edge)
            B, src = c.def_texts_all(l4, name), "leaf-fold4's chain"
            if not B:
                B, src = c.def_texts_all(txt, name), e["file"]
            out.append((name, f"{_cmp(A, B) or 'def not found'} ({base} vs {src})"))
    return out


# r4: hodge-split states some rows over the kernel's G9 copy of pkg-I4 (`ZInQ.Contrib.G9.PkgI4.Qbar`), where the
# flat file has the chain's copy (`PkgI4.Qbar`); the texts are compared with that prefix removed as well
WORLD = ["ZInQ.Contrib.G9."]


def unworld(t):
    for w in WORLD:
        t = t.replace(w, "")
    return t


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
            print("def-text comparison (proved/reduced Prop vs the H base: OneProof/H or a kernel module it imports; "
                  "followed F edges only):")
            for name, r in defcheck():
                print(f"  {name:35s} {r}")
            print("kernel constants named with `_root_` in the bundles, proved by files importing their module:")
            for name, r in rootcheck():
                print(f"  {name:35s} {r}")
            print("chain-world edges (files over leaf-fold4's TailK): the H base's definition vs the chain's:")
            for name, r in chaincheck():
                print(f"  {name:35s} {r}")
            print("route T inputs and kernel leaf copies (def text vs the H base, and pairwise):")
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
    g3 = c.show(*OPH)
    for rev, path, names in EXTRA_DEFS:
        t = c.show(rev, path)
        for n in names:
            A, B = c.def_texts_all(g3, n), c.def_texts_all(t, n)
            v = "identical" if A and B and any(x in B for x in A) else "DIFFERENT or missing"
            if not A and B and rev == MAIN and path in oph_kernel_imports():
                v = "no copy: OneProof/H imports this file"  # r4
            print(f"  {n:20s} {rev}:{path}: {v}")
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


FIELDS_TSV = "scratch/leaf-fold8/fields8.tsv"  # the H base's field table (bundle, field, Lean type, form, ...)


def onep_check():
    """r4: compare the library theorem `ZInQ.OneProof.frozenTarget` (main) with scenario A (its hypothesis heads), and
    the H base's field table FIELDS_TSV (the source of the forms of its fields) with the bundles."""
    name = "_root_.ZInQ.OneProof.frozenTarget"
    sig = c.signature(c.show(MAIN, "ZInQKernel/OneProof/Main.lean"), name)
    hyps, concl = c.split_binders(sig, name)
    got = sorted(head_of_type(h) for h in hyps)
    open_, rows = expand("A")
    want = sorted(list(STRUCTS) + [n for n, src in open_ if src == "root" or "." not in src])
    print("OneProof.frozenTarget: hypotheses vs scenario A's (its bundles and the open nodes outside them):",
          "equal" if got == want else f"DIFFERENT {got} vs {want}", "; conclusion", head_of_type(concl))
    tsv = {}
    for ln in c.show(MAIN, FIELDS_TSV).strip().split("\n")[1:]:
        b, f, ty = ln.split("\t")[:3]
        tsv.setdefault(b, []).append((f, " ".join(ty.split())))
    key = {"OpenResearchLeaves8": "R", "OpenTextbookLeaves8": "T", "OpenAddedLeaves8": "A", "OpenGlue7": "G"}
    for sname, ((rev, path), short) in STRUCTS.items():
        a = [(f, " ".join(t.split())) for f, t in c.structure_fields(c.show(rev, path), short)]
        b = tsv.get(key[sname], [])
        if a == b:
            v = "same names and types"
        elif [(f, head_of_type(t)) for f, t in a] == [(f, head_of_type(t)) for f, t in b]:
            v = "same names and head constants (types abbreviated in the table: " + ", ".join(
                f for (f, t), (_, u) in zip(a, b) if t != u) + ")"
        else:
            v = f"DIFFERENT {sorted(set(a) ^ set(b))}"
        print(f"  {sname}: {len(a)} fields; {FIELDS_TSV.split('/')[-1]}: {len(b)} rows, {v}")


if __name__ == "__main__" and "doc" in sys.argv:
    doc_check()

if __name__ == "__main__" and "onep" in sys.argv:
    onep_check()

if __name__ == "__main__" and "doc" not in sys.argv and "onep" not in sys.argv:
    main()
