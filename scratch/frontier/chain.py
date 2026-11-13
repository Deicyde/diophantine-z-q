"""chain.py: follow the hypotheses of the chain to ZInQ.FrozenTarget and list what stays open.

Usage: python3 scratch/frontier/chain.py [A|F]   (default: both)

Scenario A ("compiled"): only theorems that compose in one Lean world today, i.e. the top chain
(scratch/frontier/TopChain.lean, compiled) and cpts-transport's compiled H assembly
`HSyn.sixContactMin_of_leaves5`. Its open set is the hypothesis list of that composite.

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

# ---------------------------------------------------------------- edges
# (concl, short theorem name, rev, file, [hyp heads], scenario set, note)
E = []


def edge(concl, thm, rev, path, hyps, sc="AF", note="", deffile=None):
    E.append(dict(concl=concl, thm=thm, rev=rev, file=path, hyps=hyps, sc=sc, note=note, deffile=deffile))


# --- top (compiled here)
edge("FrozenTarget", "frozenTarget_of_open_main", MAIN, "scratch/frontier/TopChain.lean",
     ["SixContactMin", "TYZThm11Integral", "TYZLcalOne", "TYZLemma29Mod2", "CMFieldOfDefinition",
      "TYZSigmaFixesZn", "Lemma318Literal", "GenusPointLeafCM", "FHNonvanishing", "GrossZagierHeegner"], "A")
# F: top split through GZDecomp + the finest TYZ graph
edge("FrozenTarget", "frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner",
     "6f77abb1", "ZInQKernel/Contrib/GZTheta/NewCMFinal.lean",
     ["SixContactMin", "TYZThm35ReadingA", "FHNonvanishing", "GrossZagierHeegner"], "F")
# --- TYZ, finest (cm-bridge + tyz-cm)
CMB = ("441c607c", "scratch/cm-bridge/Bridge.lean")
TCM = "66d92d11"
edge("TYZThm35ReadingA", "tyzThm35ReadingA_of_pinnedLeaves", *CMB,
     ["TYZThm11Integral", "TYZLcalOne", "TYZLemma29Mod2", "CMFieldOfDefinitionTYZ", "IInH4", "TYZSigmaFixesZn",
      "HprimeNormal", "Lemma318Literal", "CMFieldOfDefinition7", "GenusFieldLeLni", "Thm35First",
      "Lemma321Five", "Lemma321Seven"], "F")
edge("IInH4", "iInH4", MAIN, "ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean", [], "F")
edge("HprimeNormal", "hprimeNormal", MAIN, "ZInQKernel/Contrib/TYZGenus/RingClassBridge.lean", [], "F")
edge("GenusFieldLeLni", "genusFieldLeLni", *CMB, [], "F")
edge("CMFieldOfDefinition7", "cmFieldOfDefinition7_of", *CMB, ["CMFieldOfDefinition"], "F")
edge("Lemma321Seven", "lemma321Seven_of", *CMB, ["CMFieldOfDefinition7", "TYZThm36Seven", "BetaOnGenus7"], "F")
edge("CMFieldOfDefinitionTYZ", "cmFieldTYZ_of_shimura", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraField.lean",
     ["ShimuraReciprocityPic"], "F")
edge("CMFieldOfDefinition", "cmFieldOfDefinition_of", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraField.lean",
     ["ShimuraReciprocityPic"], "F")
edge("TYZSigmaFixesZn", "tyzSigmaFixesZn_of", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraZn.lean",
     ["ShimuraReciprocityPic", "EtaModelFricke"], "F")
edge("ShimuraReciprocityPic", "shimuraReciprocityPic_of", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean",
     ["ShimuraReciprocityModFn", "IsRatModFn", "IsRatModFn"], "F")
edge("IsRatModFn", "isRatModFn_xC_of", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraModFn.lean",
     ["EtaModelInvariant", "EtaCuspGrowth", "XQExpRational"], "F", "the yC instance has the same inputs with YQExpRational")
edge("XQExpRational", "xQExpRational", TCM, "ZInQKernel/Contrib/TYZGenus/ShimuraQExp.lean", [], "F")

# --- H
edge("SixContactMin", "sixContactMin_of_leaves5", *B5, ["ResearchLeaves4", "TextbookLeaves", "GluePieces5"])
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
edge("X1RationalCusp", "x1RationalCusp_of_igusaTransitive", "c87d3b9b", "ZInQKernel/Contrib/RLeaf/TateCusp.lean",
     ["IgusaTransitive"], "F", deffile="ZInQKernel/HDecomp/ModCurves/X1Belyi.lean")
# GluePieces5 fields, F
HBC = ("116dc2f2", "scratch/hodge-bc2/OmegaBC.lean")
edge("HodgeBCInjective", "hodgeBCInjective", "116dc2f2", "scratch/hodge-bc2/HodgeBCInjective.lean", [], "F")
edge("OmegaBaseChange", "omegaBaseChange", "116dc2f2", "scratch/hodge-bc2/IntegrationBC.lean", [], "F")
PM = "scratch/period-map/DevHeavy.lean"
edge("S8Nonzero", "s8Nonzero_proof", "cbe9fe4c", "scratch/period-glue/S8.lean", [], "F", deffile=PM)
edge("SphereFactorAffine", "sphereFactorAffine_proof", "80af6547", "scratch/period-glue/part_sphere.lean", [], "F",
     "proof on period-glue-b, a branch stopped at 10:12 (its last commit is an unchecked snapshot; 80af6547 itself is checked)",
     deffile="scratch/period-glue/PGLight.lean")
edge("PiTwistC", "piTwistC_of", "cbe9fe4c", "scratch/period-glue/PiTwist.lean",
     ["Over", "PtEquiv", "ToP1", "R1fpProps", "R2fpProps", "TwistOrbitFinite", "FibreTransferC"], "F",
     "instantiated at the triple chosen from R1R2fpRep (r1r2): Y, Φ, π, R1fpProps, R2fpProps come from r1r2", deffile=PM)
for d in ["Over", "PtEquiv", "ToP1", "R1fpProps", "R2fpProps", "R1R2fp"]:
    edge(d, None, None, None, ["R1R2fpRep"], "F", "data/clauses extracted from the research leaf r1r2 (R1R2fp_of_rep, Classical.choice)")
edge("QMTwistLattice", "qmTwistLattice_of", "cbe9fe4c", "scratch/period-glue/QMTwist.lean",
     ["T11aRiemannHom", "QMLatticeTwistAlg"], "F", deffile=PM)
edge("S8WeightExact", "s8WeightExact_of", "cbe9fe4c", "scratch/period-glue/W8.lean",
     ["ThetaModularity", "GammaStarGen"], "F", deffile=PM)
PTS = ("3d41b3d5", "scratch/prop-ts-glue/PropTSGlue.lean")
edge("VerticalResidueSeparable", "verticalResidueSeparable", "1b8a3b3d", "scratch/ts-sn/TSSN.lean", [], "F")
edge("SNSpecialize", "snSpecialize", "1b8a3b3d", "scratch/ts-sn/TSSN.lean", [], "F")
TSK = ("d9c06585", "scratch/ts-kummer/KummerTS.lean")
for p, t in [("KummerAbhyankarFinGlue", "kummerAbhyankarFinGlue"), ("KummerOtherBranchFin", "kummerOtherBranchFin"),
             ("KummerVerticalFin", "kummerVerticalFin"), ("KummerAbhyankarInfGlue", "kummerAbhyankarInfGlue"),
             ("KummerOtherBranchInf", "kummerOtherBranchInf"), ("KummerVerticalInf", "kummerVerticalInf")]:
    edge(p, t, *TSK, [], "F")
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
edge("LinkedFrob+KernelFieldBreaks+TateRamAtThree", "linkedTateLocal_of_tateBridge35", "3d1b90b5",
     "scratch/lt-local/LtLocal4.lean",
     ["RaynaudCriterion", "TorsionStructure", "UnramRoots", "UnramRoots", "TateBridge35", "FibreSimple", "QMEndRank"],
     "F", "route T: proves g0-assemble2's `LinkedTateLocal`, which g0-assemble3 rebuilt from the three fields; "
          "FibreSimple is derived inside g0-assemble3's assembly")
edge("UnramRoots", "unramRoots", "b066d686", "scratch/unram-roots/UnramRoots.lean", [], "F")
edge("TateBridge35", "tateBridge35_of_neron_nmp", "60340bed", "scratch/frob-pieces/FrobPiecesFull.lean",
     ["TateModuleFree", "AbVarSpreadsOut", "ProperSmoothGenConnected", "ReductionTorsionBijective",
      "NeronMappingAbelianScheme"], "F")
edge("FibreSimple", None, None, None, [], "F", "derived inside g0-assemble3's `gluePieces_of_gluePieces4` (not an open Prop)")
edge("TwistDescent", "twistDescent", "fdd133f1", "scratch/twist-descent/Dev.lean", [], "F")
# field 3 bypassed by T35 in the HDec world (leaf-fold2)
edge("AnalyticUniformizationOfDim", "productMetrizationOfProductUnif_of_t35", "b38ee0c4",
     "scratch/leaf-fold2/parts/b20_fold.lean", ["UniformizationExists"], "F",
     "bypass, not a proof: in the HDec world ProductMetrizationOfProductUnif (the field's only consumer) follows from T35")

# ---------------------------------------------------------------- bundles
STRUCTS = {
    "ResearchLeaves4": (G3, "ResearchLeaves4"),
    "TextbookLeaves": (G3, "TextbookLeaves"),
    "GluePieces5": (B5, "GluePieces5"),
}
# fields never projected on the route (h-leaves agent, grep of the flat file; g0-assemble3 §6)
UNUSED = {"r1rec", "r3", "r4", "r5", "r7b", "r8", "t1", "t3", "t4", "t10", "t16b", "t20", "t21", "t28", "t29a", "t29b"}
# fields that become used on route F (an F edge takes them as hypotheses)
USED_IN_F = {"r4", "t3", "t4"}

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
    route_T = {"LinkedFrob", "KernelFieldBreaks", "TateRamAtThree"}
    seen, open_, rows = set(), [], []
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
                    stack.append(("LinkedFrob+KernelFieldBreaks+TateRamAtThree", f"{node}.{f}"))
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


def defcheck():
    """Compare def texts of bundle-field Props proved in another file (check 3)."""
    g3 = c.show(*G3)
    out = []
    for e in E:
        if "F" not in e["sc"] or e["thm"] is None or "+" in e["concl"]:
            continue
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
            print("def-text comparison (proved field vs g0-assemble3's def):")
            for name, r in defcheck():
                print(f"  {name:35s} {r}")


if __name__ == "__main__" and "doc" not in sys.argv:
    main()


def doc_check(path="/home/jackmccarthy/dzq-wt/frontier/docs/research/frontier.md"):
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
