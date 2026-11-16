"""chain.py: follow the hypotheses of the chain to ZInQ.FrozenTarget and list what stays open.

Usage: python3 scratch/frontier/chain.py [A|F]   (default: both); `doc` compares frontier.md with scenario F; `onep`
compares the library theorem ZInQ.OneProof.frozenTarget with scenario A

Scenario A ("compiled"): only theorems that compose in one Lean world today, i.e. the top chain (r3: atkin-li's C2
and tyz-chain's T0, kernel modules) and the compiled H assembly: leaf-fold29's `HDec.HSyn.sixContactMin_of_open31`
(refresh r9; r8 leaf-fold19's `sixContactMin_of_open26`, r7 leaf-fold13's `sixContactMin_of_open16`, r6
leaf-fold11's `sixContactMin_of_open15`, r5 leaf-fold9's `sixContactMin_of_open9`, r4 leaf-fold8's
`sixContactMin_of_open8`, r3 leaf-fold5's `sixContactMin_of_open5`, r2 leaf-fold4's `sixContactMin_of_open4`, before
that assemble-port's `sixContactMin_of_leaves5`).
Its open set is the hypothesis list of that composite.

Scenario F ("frontier"): A plus every proof or reduction of an open Prop found on today's branches; since r9 its top is
gz-statements' C_d form of C2 (the restricted hL2 and hL3), on which the Gross–Zagier split needs no composite.
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
# r9: the H base is leaf-fold29 inside the library (ZInQKernel/OneProof/H/: leaf-fold20 to leaf-fold29 and
# leaf-fold-hx over leaf-fold19; r8: leaf-fold19, since 11-15; r7: leaf-fold13, since w66; r6: leaf-fold11, since
# w63; r5: leaf-fold9, since w60; r4: leaf-fold8, since w59). "OPH" is read as the text of all those modules
# (OpenResearchLeaves24 and sixContactMin_of_open31 are in TailZ37.lean, OpenAddedLeaves17 in TailZ34.lean,
# OpenTextbookLeaves11 in TailZ32.lean, the glue bundle OpenGlue7 in TailX.lean; defcheck looks for the chain's
# copies anywhere in them).
OPX = (MAIN, "ZInQKernel/OneProof/H/TailZ37.lean")
OPX34 = (MAIN, "ZInQKernel/OneProof/H/TailZ34.lean")
OPX32 = (MAIN, "ZInQKernel/OneProof/H/TailZ32.lean")
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


def _closure(roots, resolve, root_rev=MAIN):
    """Files in the import closure of `roots` (at MAIN; r6: the roots themselves at `root_rev`); resolve(module) gives a
    path, or None to stop there."""
    seen, todo = set(roots), list(roots)
    while todo:
        f = todo.pop()
        for m in re.finditer(r"^import\s+(.+)$", _show(root_rev if f in roots else MAIN, f), re.M):
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


def edge(concl, thm, rev, path, hyps, sc="AF", note="", deffile=None, extra=(), bound=(), nth=0, mp=False, iff=False):
    """`extra`: hypotheses that are section variables brought in by `include ... in`, so not in the signature text.
    `bound`: binder heads that the consumer quantifies over (its hypothesis is `∀ x, P x → concl x`): checked in the
    signature, not followed. `nth`: which declaration of that name in the file (0 = the first). `mp` (r6): `thm` is a
    Prop defined as an implication `A → concl`; the edge is modus ponens from `A` and `thm`, checked on its def text.
    `iff` (r6): `thm` concludes `A ↔ concl` from the other listed hypotheses, `A` the first of them; the edge is
    `(thm …).mp`."""
    E.append(dict(concl=concl, thm=thm, rev=rev, file=path, hyps=hyps, sc=sc, note=note, deffile=deffile,
                  extra=list(extra), bound=list(bound), nth=nth, mp=mp, iff=iff))


def _iff_parts(t):
    """The two sides of a top-level `↔`, or None."""
    depth, cur, parts = 0, "", []
    for ch in t:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "↔" and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    parts.append(cur.strip())
    return parts if len(parts) == 2 else None


def _arrows(t):
    """Top-level arrow components of a type."""
    parts, depth, cur = [], 0, ""
    for ch in t:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "→" and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    return parts + [cur.strip()]


def mp_heads(txt, name):
    """(antecedent heads, consequent head) of `def name : Prop := A₁ → … → B`, or None."""
    ds = c.def_texts_all(txt, name)
    if len(ds) != 1 or ":= " not in ds[0]:
        return None
    parts = _arrows(ds[0].split(":= ", 1)[1])
    return [c.short_of(c.head(p.lstrip("("))) for p in parts[:-1]], c.short_of(c.head(parts[-1].lstrip("(")))


# --- top (compiled here): scratch/frontier/TYZChain.lean, which contains tyz-cm's and cm-bridge's
# reductions verbatim; both scenarios use it.  (TopChain.lean is the fork-main-only variant.)
# r3: the top is two kernel modules on main: atkin-li's C2 (GZ through FHNonvanishing, GrossZagierHeegner, with
# HeckeThetaNewform proved) and tyz-chain's reading A from four TYZ Props (everything else on the TYZ side proved).
# r9: scenario F takes gz-statements' C_d form of the top (on main since 11-13): the headline uses hL2 and hL3 only at
# the curves C_d, and on that form gz-weil's parametrization, with Jacobi's formula proved by jacobi-lambda, leaves
# gz-hl3's split no composite of its own. The library theorem (scenario A) still takes the general hL3. First, so it
# wins over C2 in scenario F.
edge("FrozenTarget", "frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd", MAIN,
     "ZInQKernel/Contrib/GZStatements/Weak.lean",
     ["SixContactMin", "TYZThm35ReadingA", "FHNonvanishingCd", "GrossZagierHeegnerCd"], "F",
     "gz-statements: the C_d form of the top")
edge("FHNonvanishingCd", "fhNonvanishingCd_of_fhNonvanishing", MAIN, "ZInQKernel/Contrib/GZStatements/Weak.lean",
     ["FHNonvanishing"], "F", "gz-statements: the restricted form is weaker")
edge("GrossZagierHeegnerCd", "grossZagierHeegnerCd_of_leaves4", MAIN,
     "ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean",
     ["WeierstrassUniformization", "HeegnerPointRationalCd", "GrossZagierFormulaCd", "GrossConjugationCd"], "F",
     "gz-hl3's C_d split with gz-weil's parametrization, Jacobi's formula proved by jacobi-lambda")
edge("HeegnerPointRationalCd", "heegnerPointRationalCd_of_printed", MAIN,
     "ZInQKernel/Contrib/OneProof/GrossZagierHeegner/HeegnerCd.lean", ["ShimuraMainCM", "X0ModuliGaloisMero"], "F",
     "gz-heegner: the C_d form of gz-hl3's composite leaf")
edge("FrozenTarget", "frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishing_grossZagierHeegner", MAIN,
     "ZInQKernel/Contrib/GZTheta/NewCMFinal.lean",
     ["SixContactMin", "TYZThm35ReadingA", "FHNonvanishing", "GrossZagierHeegner"])
# r9 (leaf-fold24): gz-fh proves the twisted functional equation, so frozenTarget takes FHNonvanishing from the single
# leaf FriedbergHoffsteinB_FE (until r8: the top hypothesis hL2 itself)
edge("FHNonvanishing", "fhNonvanishing_of_friedbergHoffsteinB_FE", MAIN,
     "ZInQKernel/Contrib/OneProof/FHNonvanishing.lean", ["FriedbergHoffsteinB_FE"], "AF",
     "gz-fh, in the library since leaf-fold24")
# r9 (leaf-fold29): h29-ne3 proves TYZLemma29Mod2 from six published leaves (TYZ Lemma 2.9 for n != 3, Theorem 2.1 at
# (3, 1), Proposition 2.3, the test vector's existence, Legendre's and Jones-Pall's ternary forms), and frozenTarget
# takes them in place of h29
edge("TYZLemma29Mod2", "tyzLemma29Mod2_of_sixLeaves", MAIN, "ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean",
     ["LegendreThreeSquares", "JonesPallX2Y2Z16", "TYZTestVectorExists", "TYZLemma29PrintedNe3", "TYZThm21At31",
      "TYZProp23Printed"], "AF", "h29-ne3, in the library since leaf-fold29")
# r9 (leaf-fold-hx): theta-wp8 proves ThetaWeierstrass8, so hx-used's eta route gives Shimura reciprocity for modular
# functions at level 32 from ShimuraMainCM alone, and frozenTarget drops hX. First, so it wins over the edges below,
# which stay compiled but are off the route.
edge("TYZThm35ReadingA", "tyzThm35ReadingA_noHX", MAIN, "ZInQKernel/Contrib/OneProof/ThetaWeierstrass8.lean",
     ["TYZThm11Integral", "TYZLemma29Mod2", "ShimuraMainCM", "TYZThm33"], "AF",
     "theta-wp8 with hx-used's eta route, in the library since leaf-fold-hx")
# r4 (w59): leaf-fold8 compiles tyz-split's derivation of T0's pinned hypothesis from the printed TYZ Theorem 3.3 into
# OneProof (TYZSplit.lean = scratch/tyz-split/T11.lean from line 2), so both scenarios take T-11 from `TYZThm33`.
# (Until w58 scenario F used tyz-split's `tyzThm35ReadingA_of_printedThm33` in scratch/tyz-split/T11.lean.)
edge("TYZThm33Pinned", "tyzThm33Pinned_of_tyzThm33", MAIN, "ZInQKernel/OneProof/TYZSplit.lean", ["TYZThm33"], "AF",
     "tyz-split, compiled in OneProof by leaf-fold8", bound=["ℤ", "IsTYZLcal"])
edge("TYZThm35ReadingA", "tyzThm35ReadingA_of_leaves", MAIN, "ZInQKernel/Contrib/TYZChain/Main.lean",
     ["TYZThm11Integral", "TYZLemma29Mod2", "ShimuraReciprocityModFn", "TYZThm33Pinned"])
# r8 (w69): gt-ringclass proves t5-glue's RingClassLattice in the library (leaf-fold17), and frozenTarget takes the CM
# hypothesis from the two printed leaves of t5-glue's split (until r7: the top hypothesis hS; F split it by tyz-split
# and t5-glue)
edge("ShimuraReciprocityModFn", "shimuraReciprocityModFn_of_printed", MAIN,
     "ZInQKernel/Contrib/OneProof/RingClassLattice.lean", ["ShimuraMainCM", "X0ModuliGalois"], "AF",
     "gt-ringclass, in the library since leaf-fold17")
# (r1-r2: the top was this task's frozenTarget_of_open in scratch/frontier/TYZChain.lean, with the 7 TYZ Props of
#  cm-bridge's B1; it stays compiled there but is off the route)

# --- H
edge("SixContactMin", "sixContactMin_of_open31", *OPX,
     ["OpenResearchLeaves24", "OpenTextbookLeaves11", "OpenAddedLeaves17", "OpenGlue7"])
# (r8 at main 37391b11: leaf-fold19's sixContactMin_of_open26 in TailZ32.lean, bundles OpenResearchLeaves19,
#  OpenTextbookLeaves11, OpenAddedLeaves16, OpenGlue7; leaf-fold20 to leaf-fold28b fold gt-sga7, gt-unip, yu-prune,
#  gt-rayclass, sgr-split, h33-sign, gt-rigidity with rigid-prune, gz-fh, r16-split, elkies-coord and flt-cqj2,
#  leaf-fold-hx removes the top's hX (theta-wp8), and leaf-fold29 folds bg-explicit, st-qbar, faltings5-lower and
#  r6-nf with neron-dvr (four research fields go) and replaces the top's h29 by h29-ne3's six leaves)
# (r7 at w66: leaf-fold13's sixContactMin_of_open16 in TailZ22.lean, bundles OpenResearchLeaves13,
#  OpenTextbookLeaves10, OpenAddedLeaves12, OpenGlue7; leaf-fold14 to leaf-fold19 fold reduct-b (Route B-cp) and
#  t09-pic (their leaves become fields), sem-prune, gt-ega, gt-blr, gt-gamma, gt-theta, gt-ringclass (the top's hS
#  becomes hCM and hX), gt-grcount, gt-shpair, gt-elkies, gt-qm, gt-valence and fork PR #19 (mulEtaleAbelianScheme))
# (r6 at w63: leaf-fold11's sixContactMin_of_open15 in TailZ19.lean, bundles OpenResearchLeaves12,
#  OpenTextbookLeaves10, OpenAddedLeaves11, OpenGlue7; leaf-fold13 (w66) folds x6-glue (x6-fold: r1r2Ab and
#  x6ConicModel from five printed leaves on abelian schemes, geomConnOfAlgClosure and rayClassCMAb))
# (r6 drafted at w62: leaf-fold10's sixContactMin_of_open12 in TailZ15.lean, bundles OpenResearchLeaves10,
#  OpenTextbookLeaves10, OpenAddedLeaves9, OpenGlue7; leaf-fold11 (w63) folds genus-fold (genusX1Field removed),
#  route-a-fold (four fields restated on abelian schemes, plus mumfordRigidityCore), cm24-value (igusaCMValue24
#  proved) and c-to-printed (neronLocalizesDVR, faltingsLemma5BC, semistableNeronBaseChange from six printed leaves))
# (r5 at w60: leaf-fold9's sixContactMin_of_open9 in TailZ9.lean, bundles OpenResearchLeaves9, OpenTextbookLeaves9,
#  OpenAddedLeaves8, OpenGlue7; leaf-fold10 folds dimjac-glue, shimura-glue's printed Deligne leaf for Y3 and
#  reduct-glue's r6, SS1 and SS3, and the prune (w62) removes r3, serreTateThm2 and t10 from every generation)
# (r4 at w59: leaf-fold8's sixContactMin_of_open8 in TailZ4.lean, bundles OpenResearchLeaves8, OpenTextbookLeaves8,
#  OpenAddedLeaves8, OpenGlue7; leaf-fold9 proves r1rec, r5, r15, t33, normalModelOfFunctionFieldQ, splits r7b, r8
#  into reduct-split's four leaves and replaces r5count by shimura-split's GonzalezRotgerCountX6)
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
# --- r9: reports merged since r8 that no fold takes: gz-hl3 (hL3 from six leaves over genuine definitions: the
# Heegner point is a Lean object) and gz-heegner (gz-hl3's composite leaf HeegnerPointRational from ShimuraMainCM and
# the printed canonical-model theorem X0ModuliGaloisMero; grossZagierHeegner_of_printed composes the two). Off the
# route: scenario F takes the C_d form of the top (above), where the parametrization needs no leaf.
edge("GrossZagierHeegner", "grossZagierHeegner_of_leaves", MAIN, "ZInQKernel/Contrib/OneProof/GrossZagierHeegner.lean",
     ["WeierstrassUniformization", "StrongWeilCurve", "IsogenyLattice", "HeegnerPointRational", "GrossZagierFormula",
      "GrossConjugation"], "F", "gz-hl3: the Heegner point built from Mathlib's Weierstrass p and the Eichler integral")
edge("HeegnerPointRational", "heegnerPointRational_of_printed", MAIN,
     "ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean", ["ShimuraMainCM", "X0ModuliGaloisMero"], "F",
     "gz-heegner: Shimura reciprocity and the canonical model of X0(N) for functions with poles in the upper half-plane")
# --- r8: the former textbook field mulEtaleAbelianScheme, proved over every commutative base by fork PR #19
# (leaf-fold19 removes the field); unipotent-b's split of semistableUnipotent (F) still takes it
edge("MulEtaleAbelianScheme", "mulEtaleAbelianScheme_proof", MAIN, "ZInQKernel/Contrib/OneProof/MulEtale.lean", [], "F",
     "fork PR #19, in the library since leaf-fold19")
# --- r7 (w66): the reports merged in w66 that leaf-fold13 does not fold: reduct-b (the three SGA 7 IX DVR fields
# from their strictly henselian forms), unipotent-b (SGA 7 IX 3.5 as printed), t09-pic (four printed leaves over the
# vendored Picard functor) and igusa-alg (IgusaAlg 5-9 proved). First in the list, so they win over the older edges
# below. Not taken: sh-route's `…0` theorems (their statements add `[CharZero K]` and a perfect residue field to the
# fields' statements, and no compiled consumer takes them); shimura-cft's `shimuraFamilyAb_of_mainThmI` (its leaf
# ShimuraMainThmIDeligneY3Ab implies ShimuraHolFamily, by `mainThmI_iff_ab`, `mainThmIY3_of_mainThmI` and
# c-to-printed's `shimuraHolFamily_of_mainThmI`, so F keeps the weaker leaf); gap-triage's probe
# `modelYIrreducible_of_open9` (it takes leaf-fold9's whole bundle OpenAddedLeaves9).
RB = (MAIN, "scratch/reduct-b/ReductB.lean")  # reduct-glue's file (TailZ7 and TailZ14 verbatim) with reduct-b's Body
edge("SemistableReductionDVR", "semistableReductionDVR_of_raynaud", *RB,
     ["RaynaudSemistable", "MumfordTorsionAlgClosed", "MulEtaleAbelianScheme"], "F",
     "reduct-b: K1, SGA 7 IX 3.6 over a DVR from Raynaud's criterion", deffile=RB[1])
edge("RaynaudSemistable", "raynaudSemistable_of_SH_pair", *RB,
     ["RaynaudSemistableSH", "StrictHenselizationPair", "MulEtaleAbelianScheme"], "F", "reduct-b", deffile=RB[1])
edge("SemistablePersistsDVR", "semistablePersistsDVR_of_SH_pair", *RB,
     ["SemistablePersistsSH", "StrictHenselizationPair"], "F", "reduct-b", deffile=RB[1])
edge("SemistableUnipotent", "semistableUnipotent_of_printedGen", MAIN, "scratch/unipotent-b/UnipotentB.lean",
     ["SemistableUnipotentPrintedGen", "SemiAbelianDescendsSepClosed", "MulEtaleAbelianScheme",
      "StrictHenselizationInside"], "F", "unipotent-b: SGA 7 IX 3.5 as printed; the glue only for imperfect residue "
     "fields")
edge("T09_SymmIsogenyExists", "t09SymmIsogenyExists_of_four", MAIN, "scratch/t09-pic/Pic.lean",
     ["PicRepresentableAbVar", "PicZeroAbVar", "PhiAmpleIsogeny", "WeilPairingMumford"], "F",
     "t09-pic: over the vendored relative Picard functor")
IA = (MAIN, "scratch/igusa-alg/IgusaAlg.lean")  # over OneProof's TailA, with theta-split's and theta-glue's files
edge("QMThetaSymmetricCurve", "qmThetaSymmetricCurve_of_linYang", *IA, ["LinYangThetaCurve"], "F",
     "igusa-alg: IgusaAlg 5-9 proved by one Kronecker evaluation in the kernel", deffile=IA[1])
# --- r6 (w63): x6-glue's leaves for r1r2 and x6ConicModel, route A's transfers to the abelian-scheme fields,
# c-to-printed2's Kato leaf, shimura-glue's printed forms, reduct-glue's printed bases, t5-glue and theta-glue
# (branch heads where not on main; r7: all merged in w66, files unchanged, so read at main). First in the list, so
# they win over the older edges below. theta-split replaces a field at its consumer (BYPASS below). (r7: x6-glue's
# two theorems and the transfer to R1R2fpRepAb are off the route: x6-fold proves r1r2Ab and x6ConicModel in the
# library from the abelian-scheme forms of x6-glue's leaves.)
X6G = ("685a56e1", "scratch/x6-glue/X6Glue.lean")  # x6-glue's branch head (after its report); imports OneProof's TailK
edge("R1R2fpRep", "r1r2_of_published", *X6G,
     ["DeligneComponentsX6Printed", "GeomConnOfAlgClosure", "TorsionStructure", "BabaGranathRational", "RayClassCM",
      "GonzalezRotgerX6"], "F", "x6-glue: shimura-split's r1r2fpRep_of_printed_t5 over shimura-glue's printed forms")
edge("X6ConicModel", "x6ConicModel_of_published", *X6G,
     ["DeligneComponentsX6Printed", "GeomConnOfAlgClosure", "TorsionStructure", "BabaGranathRational", "RayClassCM",
      "GonzalezRotgerX6", "ElkiesEquationsX6"], "F", "x6-glue: Elkies' equations as a statement about the scheme")
# route-a-fold (w63) restates four fields on abelian schemes and fills the old ones by `(L_iff_ab …).mpr`; where an F
# split concludes the old form, the abelian-scheme field follows by the transfer's `.mp`
RA = (MAIN, "ZInQKernel/OneProof/H/TailZ17.lean")
edge("R1R2fpRepAb", "r1R2fpRep_iff_ab", *RA, ["R1R2fpRep", "MumfordRigidity"], "F", "route-a-fold", iff=True)
edge("ShimuraFamilyAb", "shimuraFamily_iff_ab", *RA, ["ShimuraFamily", "MumfordRigidity"], "F", "route-a-fold",
     iff=True)
edge("MumfordRigidity", "mumfordRigidity_of_core", MAIN, "ZInQKernel/OneProof/H/TailZ16.lean", ["MumfordRigidityCore"],
     "F", "r1univ-rigid (in the library since w63)")
CT2 = (MAIN, "scratch/c-to-printed2/CToPrinted2.lean")  # r6: c-to-printed2's branch head dbeaecf7 (merged in w66)
edge("EigenformHTNew", "eigenformHTNew_of_printedSS", *CT2,
     ["KatoRealizationCohSS", "TateTwistInvariants", "AxSenTate"], "F", "c-to-printed2: HTDual proved")
# (c-to-printed's shimuraFamily_of_mainThmI, ba24fa83 Shimura.lean, is not taken: its leaf ShimuraMainThmIY3 implies
#  shimura-split's ShimuraHolFamily (shimuraHolFamily_of_mainThmI) and is still a consequence)
# shimura-glue (w61): off the route for R1R2fpRep and X6ConicModel since x6-glue's theorems take its leaves directly
RG = (MAIN, "scratch/shimura-glue/RowsGlue.lean")  # over OneProof's chain (imports ZInQKernel.OneProof.H.TailK)
edge("DeligneComponentsX6", "deligneComponentsX6_of_printed", *RG, ["DeligneComponentsX6Printed"], "F",
     "shimura-glue: Deligne's pi_0 in printed form; nrd computation compiled", deffile=RG[1])
edge("BabaGranathX6'", "babaGranathX6'_of_rational", *RG, ["BabaGranathRational", "MobiusCompose"], "F",
     "shimura-glue: no j-normalization in the leaf", deffile=RG[1])
edge("ElkiesConicX6", "elkiesConicX6_of_t", *RG, ["ElkiesConicT", "MobiusCompose"], "F",
     "shimura-glue: Elkies in his coordinate t", deffile=RG[1])
edge("ReciprocityCanonical", "reciprocityCanonical_of_rayClass", *RG, ["RayClassCM"], "F",
     "shimura-glue: over Tau Ceti's rayClassField", deffile=RG[1])
edge("MobiusCompose", "mobiusCompose", *RG, [], "F", "shimura-glue", deffile=RG[1])
Z14 = (MAIN, "ZInQKernel/OneProof/H/TailZ14.lean")  # reduct-glue's Body.lean, compiled in OneProof by leaf-fold10
edge("RaynaudSemistable", "raynaudSemistable_of_SH'", *Z14,
     ["RaynaudSemistableSH", "StrictHenselizationNeron", "MulEtaleAbelianScheme"], "F",
     "reduct-glue: SGA 7 IX 4.7 from its strictly henselian form")
edge("PersistsFromSH", "persistsFromSH_of", *Z14, ["StrictHenselizationPair"], "F", "reduct-glue")
edge("UnipotentFromSH", "unipotentFromSH_of", *Z14, ["StrictHenselizationInside"], "F", "reduct-glue")
edge("SemistableLocalGlobal", "semistableLocalGlobal_leaf", *Z14, ["NeronLocalizesDVR"], "F",
     "reduct-glue (compiled in OneProof)")
edge("SemistableNeronBaseChangeLocalGlobal", "semistableNeronBaseChangeLocalGlobal_of", *Z14,
     ["IdentityComponentOL", "OpenImmersionOfLocal", "NeronLocalizesDVR"], "F", "reduct-glue (compiled in OneProof)")
# reduct-glue's named glue Props are implications `SH form → DVR form` (`def ReductionFromSH : Prop :=
# SemistableReductionSH → SemistableReductionDVR`, ...); the DVR leaf follows by modus ponens, checked on the def text
for concl, imp, sh in [("SemistableUnipotent", "UnipotentFromSH", "SemistableUnipotentSH"),
                       ("SemistableReductionDVR", "ReductionFromSH", "SemistableReductionSH"),
                       ("SemistablePersistsDVR", "PersistsFromSH", "SemistablePersistsSH"),
                       ("IdentityComponentBaseChangeDVR", "IdentityComponentFromSH", "IdentityComponentBaseChangeSH")]:
    edge(concl, imp, *Z14, [sh, imp], "F", "reduct-glue: modus ponens on the implication " + imp, mp=True)
T5G = (MAIN, "scratch/t5-glue/T5Glue.lean")  # r6: t5-glue's branch head 405763f6 (merged in w66)
edge("CMModuli", "cmModuli_of_t5'", *T5G, ["ShimuraMainCM", "RingClassLattice"], "F",
     "t5-glue: AbsArtinSurjectiveQNeg and InvertibleColon proved (Tau Ceti)", deffile=T5G[1])
edge("X0RatStructure", "x0RatStructure_of_leaf", *T5G, ["X0ModuliGalois"], "F", "t5-glue", deffile=T5G[1])
TG = (MAIN, "scratch/theta-glue/ThetaGlue.lean")  # r6: theta-glue's branch head 336ec1fd (merged in w66)
edge("ThetaEightSquare", "thetaEightSquare", *TG, [], "F", "theta-glue: duplication formula plus a degree-16 identity",
     deffile=TG[1])
edge("QMThetaSymmetricCurve", "qmThetaSymmetricCurve_of_alg59", *TG, ["LinYangThetaCurve", "IgusaAlg"], "F",
     "theta-glue: IgusaAlg 3 and 4 proved; 5-9 closed polynomial identities, VERIFIED by exact expansion",
     deffile=TG[1])
# (cm24-value's CM24.igusaCMValue24_field (r6: d8d1363a; merged in w66): off the route since w63, where leaf-fold11
#  compiles it (TailZ18))
edge("IgusaCMValue24", "CM24.igusaCMValue24_field", MAIN, "scratch/cm24-value/CM24Kernel.lean", [], "F",
     "cm24-value: proved outright, no leaf", deffile="ZInQKernel/OneProof/H/TailZ3.lean")
# --- r5 (w60): the splits of shimura-split, modular-split and reduct-split that leaf-fold9 did not fold (leaf-fold9
# §5). First in the list, so they win over the older edges below.
SS = (MAIN, "scratch/shimura-split/Rows.lean")  # over OneProof's chain (imports ZInQKernel.OneProof.H.TailK)
edge("R1R2fpRep", "r1r2fpRep_of_printed_t5", *SS,
     ["DeligneComponentsX6", "GeomConnOfAlgClosure", "TorsionStructure", "BabaGranathX6'", "ReciprocityCanonical",
      "GonzalezRotgerX6"], "F",
     "shimura-split: coarse-factor's theorem with CanonicalModelY3, ReciprocityOfFine, PairsLift (from T5) and the "
     "surjectivity clause of BabaGranathX6 proved")
edge("X6ConicModel", "x6ConicModel_of_elkies_t5", *SS, ["R1R2fpRep", "ElkiesConicX6", "TorsionStructure"], "F",
     "shimura-split: MobiusGlue from T5")
edge("Y3Connected", "y3Connected_of_deligne", *SS, ["DeligneComponentsY3"], "F",
     "shimura-split: the orbit computation (the second declaration of that name, in HDec.QMSplit.Moduli)", nth=1)
edge("ShimuraFamily", "shimuraFamily_of_hol", MAIN, "scratch/shimura-split/ShimuraFam.lean", ["ShimuraHolFamily"],
     "F", "shimura-split: the GAGA-level step")
MS = "scratch/modular-split/"
edge("DimJacobianEqGenus", "dimJacobianEqGenus_of_glue", MAIN, MS + "DimJac.lean", ["H0DifferentialsEqHolo"], "F",
     "modular-split: Milne Prop. 2.1 and Serre duality proved over the vendored CloudW07 library")
edge("CarayolR17'", "carayolR17'_of_realization", MAIN, MS + "R17.lean", ["CarayolRealization"], "F",
     "modular-split")
edge("EigenformHTNew", "eigenformHTNew_of_coh", MAIN, MS + "EigenHT.lean", ["KatoRealizationCoh", "HTDual"], "F",
     "modular-split")
RS = (MAIN, "ZInQKernel/OneProof/H/TailZ7.lean")  # reduct-split's Reduction.lean verbatim, compiled in OneProof
edge("RaynaudCriterion", "raynaudCriterion_final'", *RS,
     ["RaynaudSemistable", "SemistableUnipotent", "NeronSchemeModelExistsDVR", "MumfordTorsionAlgClosed",
      "FixedTorsionRationalImperfect"], "F", "reduct-split")
edge("SemistableReductionThm", "semistableReductionThm_final", *RS,
     ["SemistableReductionDVR", "SemistablePersistsDVR", "NeronSchemeModelExistsDVR", "SemistableLocalGlobal",
      "SemistableAlmostAll"], "F", "reduct-split")
edge("SemistablePersists", "semistablePersists_final", *RS,
     ["SemistablePersistsDVR", "NeronSchemeModelExistsDVR", "SemistableLocalGlobal"], "F", "reduct-split")
edge("SemistableNeronBaseChange", "semistableNeronBaseChange_of_leaves", *RS,
     ["IdentityComponentBaseChangeDVR", "SemistableLocalGlobal", "SemistableNeronBaseChangeLocalGlobal"], "F",
     "reduct-split")
edge("FaltingsLemma5BC", "faltingsLemma5BC_final", *RS, ["FaltingsLemma5"], "F", "reduct-split")
# --- r4 (w59): coarse-factor, mcr-quot and cloud-w07.
CF = (MAIN, "scratch/coarse-factor/Discharge.lean")  # over OneProof's chain (imports ZInQKernel.OneProof.H.TailK)
edge("R1R2fpRep", "r1r2fpRep_of_canonical''", *CF,
     ["CanonicalModelY3", "CanonicalCoarseX6", "BabaGranathX6", "GonzalezRotgerX6", "ReciprocityOfFine"], "F",
     "coarse-factor: qm-glue's theorem with CoarseFactor proved from CanonicalCoarseX6 and CurveBijIso filled in")
# (r4 also took coarse-factor's x6ConicModel_of_canonical'' [R1R2fpRep, ConicCanonical, MobiusGlue]; r5 drops it:
#  ConicCanonical is X6ConicModel verbatim (shimura-split, Iff.rfl), so it was a renaming, not a reduction)
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
    "OpenResearchLeaves24": (OPX, "OpenResearchLeaves24"),
    "OpenTextbookLeaves11": (OPX32, "OpenTextbookLeaves11"),
    "OpenAddedLeaves17": (OPX34, "OpenAddedLeaves17"),
    "OpenGlue7": (OPX7, "OpenGlue7"),
}
# fields the proof does not use: none (r6: the integrator's prune, merged in w62, removed r3, serreTateThm2 and t10,
# the three that its fixed Lean scan, wip/prune-scan e3045e7d, found unused at w61; genus-fold (w63) removed
# genusX1Field; leaf-fold11's PruneScan finds no unused field at w63, x6-fold's none at w66; r8: sem-prune removed
# bdRInvariants and raynaudKernelBound with faltingsLemma5BC after cutting their consumers, PruneScan 0 unused)
UNUSED = set()
# (r5: {"r3", "t10", "serreTateThm2", "semistableReductionDVR", "semistableUnipotent", "neronSchemeModelExistsDVR"},
#  never projected; leaf-fold9 proved r1rec and r5 from r1r2; reduct-split's four leaves entered only TailZ9's proofs
#  of r7b and r8, which stayed unprojected; until r4: {"r1rec", "r3", "r5", "r7b", "r8", "t10"}, never projected in
#  g0-assemble3; assemble-port, leaf-fold4 and leaf-fold5 have the same consumers)
# (r2: in leaf-fold4's flat file r1rec, r7b, r8 occur only as `f := r.f` in three structure literals, t10 only there
#  and in T10_groupIso_of_tateDuality)
# (r4: in OneProof/H the six occur only as `f := r.f` / `f := t.f` (or a transport `_ofK5` of it) in the bundle
#  conversions of TailD, TailE, TailI, TailK, TailN, TailO and TailX, and t10 in LPrefix's T10_groupIso_of_tateDuality;
#  leaf-fold7 left the chain from LPrefix to TailO unchanged)
# fields that become used on route F (an F edge takes them as hypotheses); `chain.py F` recomputes the set
# (r5: reduct-split's raynaudCriterion_final', semistableReductionThm_final and semistablePersists_final took three of
#  its four leaves; serreTateThm2 fed only r7b)
USED_IN_F = set()

# r6: a field that a task makes unnecessary by replacing its consumer, not by proving it. `checks`: theorems whose
# signatures are compared ((rev, file, theorem, hypothesis heads, conclusion head)); `new`: the Props the replacement
# takes in place of the field (open nodes of F unless an edge proves them); `uses`: every line of OneProof/H that
# mentions the field must match one of these patterns (a field declaration, a copy `f := t.f`, or the consumer).
BYPASS = {
    "ThetaRatiosAlgebraic": dict(
        task="theta-split", new=["ThetaEightSquare", "QMThetaSymmetricCurve"],
        note="its consumer thetaPointOfFibre_of_qm_ratios (TailA) is replaced by route 1's final form, the same "
             "conclusion from the global identity and the curve part",
        checks=[(MAIN, "ZInQKernel/OneProof/H/TailA.lean", "thetaPointOfFibre_of_qm_ratios",
                 ["FibreQMPeriod", "ThetaRatiosAlgebraic"], "ThetaPointOfFibre"),
                (MAIN, "scratch/theta-split/ThetaUse.lean", "thetaPointOfFibre_of_qm_curve",
                 ["FibreQMPeriod", "ThetaEightSquare", "QMThetaSymmetricCurve"], "ThetaPointOfFibre")],
        field=None, uses=[]),
    # r9: dcy3-used (merged by leaf-fold29, not folded: the used form is weaker than the field, so autofold.py cannot
    # take it). The chain reads the field only through TailZ23 and TailZ13's y3Connected_of_deligne
    # (deligneComponentsY3_of_printed …), as Y3Connected, which follows from two research fields.
    "DeligneComponentsY3PrintedAb": dict(
        task="dcy3-used", new=["MumfordGroupLaw", "ShimuraMainThmIDeligneY3AbU"],
        note="the term y3Connected_of_deligne (deligneComponentsY3_of_printed …) of TailZ13 is replaced by "
             "y3Connected_of_leaves",
        checks=[(MAIN, "ZInQKernel/OneProof/H/TailZ12.lean", "deligneComponentsY3_of_printed",
                 ["DeligneComponentsY3Printed"], "DeligneComponentsY3"),
                (MAIN, "ZInQKernel/Contrib/OneProof/DeligneComponentsY3Used.lean", "y3Connected_of_leaves",
                 ["MumfordGroupLaw", "ShimuraMainThmIDeligneY3AbU"], "Y3Connected")],
        field="deligneComponentsY3PrintedAb",
        uses=[r"^\s*deligneComponentsY3PrintedAb : _root_\.ShimuraGlue\.DeligneComponentsY3PrintedAb$",
              r"^\s*deligneComponentsY3PrintedAb := [a-z]\.deligneComponentsY3PrintedAb$",
              r"^\s*l\.deligneComponentsY3PrintedAb$", r"^\* `deligneComponentsY3Printed : "]),
}
# r6: leaves on which the forms of other rows rest, listed in F although no edge takes them. (Drafted at w62 with
# r1univ-rigid's MumfordRigidityCore, a field of the library theorem since w63; at w62 also BYPASS "GenusX1Field":
# genus-route replaced t34's two uses by dim J1(N) <= N^2 (t34Le), and genus-fold (w63) removed the field.)
FORM_LEAVES = {}


def sig_ok(rev, path, thm, hyps, concl, nth=0):
    sig = c.signature(c.show(rev, path), thm, nth=nth)
    if sig is None:
        return f"MISSING {thm} in {rev}:{path}"
    hh, cc = c.split_binders(sig, thm)
    got = (sorted(head_of_type(h) for h in hh), head_of_type(cc))
    return "ok" if got == (sorted(hyps), concl) else f"MISMATCH {thm}: {got} vs {(sorted(hyps), concl)}"


def bypass_check():
    out = []
    for h, b in BYPASS.items():
        vs = [sig_ok(*x) for x in b["checks"]]
        if b["field"]:
            bad = [ln.strip() for f in sorted(_files(MAIN, OPH[1])) for ln in _show(MAIN, f).split("\n")
                   if re.search(r"\b%s\b" % b["field"], ln) and not any(re.search(p, ln) for p in b["uses"])]
            vs.append("every use matches" if not bad else f"OTHER USES {bad[:3]}")
        out.append((h, "; ".join(vs)))
    for h, fl in FORM_LEAVES.items():
        out.append((h, "; ".join(sig_ok(*x) for x in fl["checks"])))
    return out

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
        if e["mp"]:
            got = mp_heads(txt, e["thm"])
            want = ([h for h in e["hyps"] if h != e["thm"]], c.short_of(e["concl"]))
            if got != want:
                bad += 1
                print(f"MISMATCH (implication) {e['thm']} ({e['rev']}:{e['file']}): {got} vs {want}")
            continue
        sig = c.signature(txt, e["thm"], nth=e["nth"])
        if sig is None:
            print(f"MISSING THEOREM {e['thm']} in {e['rev']}:{e['file']}")
            bad += 1
            continue
        hyps, concl = c.split_binders(sig, e["thm"])
        hh = sorted([head_of_type(h) for h in hyps] + e["extra"])
        want = sorted(e["hyps"] + e["bound"])
        ch = head_of_type(concl)
        if e["iff"]:
            sides = _iff_parts(concl)
            got = tuple(head_of_type(x) for x in sides) if sides else None
            if hh != sorted(e["hyps"][1:] + e["bound"]) or got != (c.short_of(e["hyps"][0]), c.short_of(e["concl"])):
                bad += 1
                print(f"MISMATCH (iff) {e['thm']} ({e['rev']}:{e['file']}): hyps {hh}, sides {got} vs listed {e['hyps']} "
                      f"-> {e['concl']}")
            continue
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
                if sc == "F" and h in BYPASS:  # r6: the field's consumer is replaced; follow the replacement's Props
                    b = BYPASS[h]
                    rev, path, thm = b["checks"][-1][:3]
                    FOLLOWED.append(dict(concl=h, thm=thm, rev=rev, file=path, hyps=list(b["new"]), sc="F",
                                         note=b["task"], deffile=None, extra=[], bound=[], nth=0, mp=False, iff=False,
                                         bypass=True))
                    for x in b["new"]:
                        stack.append((x, f"{b['task']} (replaces {node}.{f})"))
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
    if sc == "F":  # r6
        for h, fl in FORM_LEAVES.items():
            if h not in seen:
                seen.add(h)
                open_.append((h, f"{fl['task']} (form leaf)"))
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
        if not e["deffile"] and (e["rev"] == MAIN or _library_world(c.show(e["rev"], e["file"]))):
            continue  # r6: a library-world file at a branch head is worldcheck's
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


def _library_world(txt):
    """A file over the library's modules (imports ZInQKernel modules, not leaf-fold4's TailK)."""
    return bool(re.search(r"^import ZInQKernel\.", txt, re.M)) and not re.search(r"^import TailK\b", txt, re.M)


def _decls(txt, name):
    """Lines that declare `name` (any declaration kind, namespaced or not)."""
    return [ln for ln in txt.split("\n")
            if re.match(r"^(?:noncomputable |private |protected )*(?:def|abbrev|theorem|lemma|structure|opaque) "
                        r"(?:\S+\.)?%s\b" % re.escape(name), ln)]


def _in_verbatim(txt, line):
    """Whether the first occurrence of `line` in txt is inside a `namespace …Verbatim` or a `section Verbatim` block
    (r7: t09-pic's copy of its field is in a section), i.e. a copy kept for an `rfl` check."""
    stack = []
    for ln in txt.split("\n"):
        if ln == line:
            return any(x.split(".")[-1] == "Verbatim" for x in stack)
        m = re.match(r"^(?:namespace|section) (\S+)", ln)
        if m:
            stack.append(m.group(1))
        m = re.match(r"^end (\S+)", ln)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
    return False


def worldcheck():
    """r5: a followed F-only edge in a library file outside OneProof/H (shimura-split, modular-split, tyz-split: files
    that import ZInQKernel modules, not leaf-fold4's TailK) concludes the library theorem's own constant if the file
    has no definition of that name and the module that defines it is in both the file's import closure and that of
    `ZInQKernel/OneProof/Main.lean`. defcheck skips these edges (no deffile). r6: the same for such a file at a branch
    head, which must also see the defining module's text of that constant as main has it; a definition of the name in
    a namespace other than the constant's own (a `Verbatim` copy for an `rfl` check) is reported, not refused (r7: at
    main too, where c-to-printed2's file is since w66, and in a `section Verbatim`, as in t09-pic's file). r9: a
    constant that Main does not import may be defined in the import closure of the followed F edge's file at main
    that takes it (gz-statements' GrossZagierHeegnerCd, which its C_d top takes); and a library module at main may
    define the constant it concludes if every followed F edge that takes it is in that module or imports it
    (gz-statements' FHNonvanishingCd)."""
    kern = _files(MAIN, "ZInQKernel/")
    res = lambda mod: (lambda p: p if p in kern else None)(mod.replace(".", "/") + ".lean")
    base = set(_closure(["ZInQKernel/OneProof/Main.lean"], res))
    takers = {}
    for e2 in FOLLOWED:
        if e2["thm"] and "F" in e2["sc"] and e2["rev"] == MAIN:
            for h in e2["hyps"]:
                takers.setdefault(h, set()).add(e2["file"])
    out = []
    for e in FOLLOWED:
        if e["sc"] != "F" or not e["thm"] or e["deffile"] or e["file"].startswith(OPH[1]):
            continue
        if e.get("bypass"):
            continue  # r6: checked by bypass_check
        txt = c.show(e["rev"], e["file"])
        if not _library_world(txt):
            continue
        name = c.short_of(e["concl"])
        own = [ln for ln in _decls(txt, name) if not ln.startswith("theorem") and not ln.startswith("lemma")]
        cons = sorted(takers.get(name, ()))
        if own and not all(_in_verbatim(txt, ln) for ln in own):
            if e["rev"] == MAIN and e["file"].startswith("ZInQKernel/") and cons and all(
                    e["file"] in set(_closure([f], res)) for f in cons):
                out.append((name, f"the library's own constant: defined in {e['file']} itself, which "
                                  f"{', '.join(cons)} (the file that takes it) is or imports"))
                continue
            out.append((name, f"CHECK: {e['file']} has its own definition"))
            continue
        defs = [f for f in _closure([e["file"]], res, e["rev"]) if f != e["file"]
                and c.def_texts_all(_show(MAIN, f), name)]
        near = set(_closure(cons, res)) if cons else set()
        if not (defs and all(f in base or f in near for f in defs)):
            out.append((name, f"CHECK: defined in {defs or 'no imported file'} ({e['file']})"))
            continue
        phrase = "only a `Verbatim` copy (for an `rfl` check) in" if own else "no definition in"
        where = ("in OneProof/Main's import closure" if all(f in base for f in defs) else
                 "in the import closure of %s, which takes it" % ", ".join(cons))
        v = f"the library's own constant: {phrase} {e['file']}, which imports {', '.join(defs)} ({where})"
        if e["rev"] != MAIN:
            same = all(c.def_texts_all(c.show(e["rev"], f), name) == c.def_texts_all(_show(MAIN, f), name) for f in defs)
            v = v.replace(phrase, "at %s, %s" % (e["rev"], phrase), 1)
            v += "; the definition there is %s at %s and at main" % ("the same" if same else "DIFFERENT", e["rev"])
            if not same:
                v = "CHECK: " + v
        out.append((name, v))
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
            hy = {h for e in FOLLOWED for h in e["hyps"]}
            used = {f for s, f, h in rows if f in UNUSED and h in hy}
            print("USED_IN_F (never-projected fields that a followed F edge takes):",
                  "equal" if used == USED_IN_F else f"DIFFERENT {sorted(used)} vs {sorted(USED_IN_F)}")
            print("def-text comparison (proved/reduced Prop vs the H base: OneProof/H or a kernel module it imports; "
                  "followed F edges only):")
            for name, r in defcheck():
                print(f"  {name:35s} {r}")
            print("kernel constants named with `_root_` in the bundles, proved by files importing their module:")
            for name, r in rootcheck():
                print(f"  {name:35s} {r}")
            print("library files outside OneProof/H (followed F-only edges without a deffile): the constant they conclude:")
            for name, r in worldcheck():
                print(f"  {name:35s} {r}")
            print("chain-world edges (files over leaf-fold4's TailK): the H base's definition vs the chain's:")
            for name, r in chaincheck():
                print(f"  {name:35s} {r}")
            print("fields replaced at their consumer, and form leaves (signatures; uses of the field in OneProof/H):")
            for name, r in bypass_check():
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


# the H base's field table. r7: the integrator's docs/one-proof/kinds.tsv (bundle, field, kind, flag, strict, strictest,
# source, rated_by; since w66), with the field types from the build's docs/one-proof/open-statements.json. (r6 kept
# its own table, scratch/frontier/fields11.tsv, because leaf-fold11 had none; the report applies the integrator's
# rulings, not this check.)
FIELDS_TSV = "docs/one-proof/kinds.tsv"
OPEN_JSON = "docs/one-proof/open-statements.json"
TSV_BUNDLE = {"OpenResearchLeaves24": "research", "OpenTextbookLeaves11": "textbook", "OpenAddedLeaves17": "added",
              "OpenGlue7": "glue"}


def onep_check():
    """r4: compare the library theorem `ZInQ.OneProof.frozenTarget` (main) with scenario A (its hypothesis heads); r7:
    and the bundles with the integrator's field table FIELDS_TSV (field names) and the build's OPEN_JSON (field names
    and type heads; the hypotheses outside the bundles by head)."""
    import json
    name = "_root_.ZInQ.OneProof.frozenTarget"
    sig = c.signature(c.show(MAIN, "ZInQKernel/OneProof/Main.lean"), name)
    hyps, concl = c.split_binders(sig, name)
    got = sorted(head_of_type(h) for h in hyps)
    open_, rows = expand("A")
    tops = sorted(n for n, src in open_ if src == "root" or "." not in src)
    want = sorted(list(STRUCTS) + tops)
    print("OneProof.frozenTarget: hypotheses vs scenario A's (its bundles and the open nodes outside them):",
          "equal" if got == want else f"DIFFERENT {got} vs {want}", "; conclusion", head_of_type(concl))
    tsv = {}
    for ln in c.show(MAIN, FIELDS_TSV).strip().split("\n")[1:]:
        b, f = ln.split("\t")[:2]
        tsv.setdefault(b, set()).add(f)
    js = json.loads(c.show(MAIN, OPEN_JSON))
    jb = {}
    for h in js["hypotheses"]:
        jb.setdefault(h["bundle"], []).append((h["field"], head_of_type(h["type"])))
    for sname, ((rev, path), short) in STRUCTS.items():
        a = sorted((f, head_of_type(t)) for f, t in c.structure_fields(c.show(rev, path), short))
        t = tsv.get(TSV_BUNDLE[sname], set())
        j = sorted(jb.get(sname, []))
        vt = "same names" if {f for f, _ in a} == t else f"DIFFERENT {sorted({f for f, _ in a} ^ t)}"
        vj = "same names and type heads" if a == j else f"DIFFERENT {sorted(set(a) ^ set(j))}"
        print(f"  {sname}: {len(a)} fields; {FIELDS_TSV.split('/')[-1]}: {len(t)} rows, {vt}; "
              f"{OPEN_JSON.split('/')[-1]}: {len(j)} entries, {vj}")
    rest = sorted(h for _, h in jb.get("frozenTarget", []))  # the theorem's own hypotheses (h11, h29, hS, h33, ...)
    print(f"  outside the bundles: {OPEN_JSON.split('/')[-1]} {len(rest)} hypotheses,",
          "same heads as scenario A's" if rest == tops else f"DIFFERENT {rest} vs {tops}",
          f"; count field {js.get('count')}")


if __name__ == "__main__" and "doc" in sys.argv:
    doc_check()

if __name__ == "__main__" and "onep" in sys.argv:
    onep_check()

if __name__ == "__main__" and "doc" not in sys.argv and "onep" not in sys.argv:
    main()
