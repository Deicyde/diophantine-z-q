"""homfree-noemb generator: writes the rerouted T6 branch (copies of the consumers and of the bundle chain) as one Lean
module. Run from the repository root: python3 scratch/homfree-noemb/gen/gen.py OUT.lean"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

H = "ZInQKernel/OneProof/H/"
HFC = "_root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC"
SQ = "_root_.HFReroute.sigmaQbar"

def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "HF" + pr
    return base + "_hf" + pr

# ---- file order (topological by imports) ----
def mod2file(m):
    return m.replace(".", "/") + ".lean"
def imports(f):
    return [l.split()[1] for l in open(f) if l.startswith("import ")]
order = []
seen = set()
def visit(m):
    if m in seen: return
    seen.add(m)
    f = mod2file(m)
    if not os.path.exists(f): return
    for i in imports(f):
        if i.startswith("ZInQKernel"): visit(i)
    order.append(f)
sys.setrecursionlimit(100000)
TOPMOD = max(re.findall(r"^import (ZInQKernel\.OneProof\.H\.TailZ\d+)$", open("ZInQKernel/OneProof/Main.lean").read(), re.M), key=lambda m: int(m.rsplit("TailZ", 1)[1]))
visit(TOPMOD)  # leaf-fold33: the top module from Main.lean (was TailZ45)
rank = {f: i for i, f in enumerate(order)}

# ---- part A: taint list ----
items = []   # (file, short, kinds, edits)
for l in open("scratch/homfree-noemb/taint_out.txt"):
    m = re.match(r"^([TS]) (\S+) (\S+)", l)
    if not m: continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    short = parts[-1]
    if mod == "ZInQKernel.OneProof.Main": continue
    if short == "mk" or (len(parts) > 1 and re.match(r"^(Open)?TextbookLeaves\d*$", parts[-2])): continue
    items.append((mod2file(mod), short, None, []))
# carriers: read from Taint.lean's output; file found by its `structure` line
import glob
cl = [l for l in open("scratch/homfree-noemb/taint_out.txt") if l.startswith("carriers ")][0]
cnames = sorted({c.split(".")[-1] for c in re.findall(r"[\w.]+", cl[len("carriers "):])},
                key=lambda c: int(re.sub(r"\D", "", c) or 0))
def cfile(c):
    for f in sorted(glob.glob(H + "*.lean")):
        if re.search(r"^structure " + c + r" ", open(f).read(), re.M):
            return f
    raise SystemExit("no file for " + c)
TOPN = max(int(re.sub(r"\D", "", c) or 0) for c in cnames)
TOP = "OpenTextbookLeaves%d" % TOPN
for c in cnames:
    ed = [("  homFreeFiniteAlgClosed : " + HFC + "\n", "")] if c == TOP else []
    items.append((cfile(c), c, ("structure",), ed))

# ---- part B: the consumers of T6 ----
B = [
 # TailA, G0FibreSimple
 (H+"TailA.lean", "EndDivisionOfEnd0Division", ("def",), [
   ("∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k),", "∀ (k : Type) [Field k] [CharZero k] (_ : k →+* ℂ) (A : PkgI3.AbVar k),")]),
 (H+"TailA.lean", "CentralizerOfMatrixEnd0", ("def",), [
   ("∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (q : QMStr A)", "∀ (k : Type) [Field k] [CharZero k] (_ : k →+* ℂ) (A : PkgI3.AbVar k) (q : QMStr A)")]),
 (H+"TailA.lean", "fibreSimple_of_pieces", ("theorem",), [
   ("h4 LeafQM.AV.Qbar P.A P.q d hd hM", "h4 LeafQM.AV.Qbar " + SQ + " P.A P.q d hd hM"),
   ("h3 LeafQM.AV.Qbar P.A (", "h3 LeafQM.AV.Qbar " + SQ + " P.A (")]),
 (H+"TailA.lean", "centralizerOfMatrixEnd0_of_homFree", ("theorem",), [
   ("intro k _ _ A q d hd hM", "intro k _ _ σ A q d hd hM"), ("(hHF k A A)", "(hHF k σ A A)")]),
 (H+"TailA.lean", "fibreSimple_of_pieces'", ("theorem",), []),
 (H+"TailA.lean", "end0Division_of_homFree", ("theorem",), [
   ("intro k _ _ A hdiv f hf", "intro k _ _ σ A hdiv f hf"), ("(hHF k A A)", "(hHF k σ A A)")]),
 (H+"TailA.lean", "fibreSimple_of_pieces''", ("theorem",), []),
 # TailA, G0Galois
 (H+"TailA.lean", "g8", ("theorem",), []),
 (H+"TailA.lean", "g8_g11", ("theorem",), []),
 (H+"TailA.lean", "g8_g12", ("theorem",), []),
 # Objects / C2 (PkgI3)
 ("ZInQKernel/HDecomp/Objects.lean", "finrank_equivEnd", ("theorem",), [
   ("hH K A A", "hH K (_root_.HFReroute.sigmaNF K) A A")]),
 ("ZInQKernel/HDecomp/I3Linalg/C2.lean", "C2_absolutelyIrreducible", ("theorem",), []),
 # TailC, FS5NoCM
 (H+"TailC.lean", "com_int_of_end0_quat", ("theorem",), [
   ("{k : Type} [Field k]\n    {A : PkgI3.AbVar k}", "{k : Type} [Field k] (σ : k →+* ℂ)\n    {A : PkgI3.AbVar k}"),
   ("hHF k A A", "hHF k σ A A")]),
 (H+"TailC.lean", "comIntOrQuadOrder_of", ("theorem",), [
   ("com_int_of_end0_quat_hf t6 P.q e", "com_int_of_end0_quat_hf t6 " + SQ + " P.q e")]),
 (H+"TailC.lean", "comOfMatrixEnd0_of_homFree", ("theorem",), [("hHF Qbar A A", "hHF Qbar " + SQ + " A A")]),
 (H+"TailC.lean", "comIntOrQuadOrder_of_leaves", ("theorem",), []),
 (H+"TailC.lean", "fibreComTrivialFull_of_leaves'", ("theorem",), []),
 (H+"TailC.lean", "fibreComTrivialFull_of_leaves''", ("theorem",), []),
 # TailC, G4WeilRes
 (H+"TailC.lean", "homLattice_free", ("theorem",), [("hHFF Qbar (A ij.1) (A ij.2)", "hHFF Qbar " + SQ + " (A ij.1) (A ij.2)")]),
 (H+"TailC.lean", "tateHom_injective", ("theorem",), [
   ("theorem tateHom_injective_hf (hHFF : " + HFC + ") {k : Type} [Field k]",
    "theorem tateHom_injective_hf (hHFF : " + HFC + ") {k : Type} [Field k] (σ : k →+* ℂ)"),
   ("(hHFF k A B)", "(hHFF k σ A B)")]),
 (H+"TailC.lean", "inertiaFixesHomsMon", ("theorem",), [
   ("tateHom_injective_hf hHFF A₁ B₂", "tateHom_injective_hf hHFF " + SQ + " A₁ B₂")]),
 (H+"TailC.lean", "inertiaFixesHomsMon_of_leaves", ("theorem",), []),
 # TailC, G0ModField.KernelField
 (H+"TailC.lean", "kernelField_of_model", ("theorem",), []),
 (H+"TailC.lean", "kernelFieldExists_of_pieces", ("theorem",), []),
 (H+"TailC.lean", "kernelFieldExists_of_leaves", ("theorem",), []),
 (H+"TailC.lean", "kernelFieldExists_of_leaves_FS5", ("theorem",), []),
 (H+"TailC.lean", "kernelFieldExists_of_split", ("theorem",), []),
 (H+"TailC.lean", "kernelFieldExists_of_split'", ("theorem",), []),
 (H+"TailC.lean", "endEqOFibre_of", ("theorem",), [
   ("centralizerOfMatrixEnd0_of_homFree_hf hHF Qbar P.A", "centralizerOfMatrixEnd0_of_homFree_hf hHF Qbar " + SQ + " P.A"),
   ("(hHF Qbar P.A P.A)", "(hHF Qbar " + SQ + " P.A P.A)")]),
 (H+"TailC.lean", "kernelFieldExists_of_split''", ("theorem",), []),
 # TailF, LTGoodRed.QM
 (H+"TailF.lean", "four_le_finrank", ("theorem",), [
   ("{k : Type} [Field k] (A : PkgI3.AbVar k)\n    (φ", "{k : Type} [Field k] (σ : k →+* ℂ) (A : PkgI3.AbVar k)\n    (φ"),
   ("hM1 k A A", "hM1 k σ A A")]),
 (H+"TailF.lean", "finrank_le_baseChange", ("theorem",), [
   ("[Field Ω] [Algebra k Ω] :", "[Field Ω] [Algebra k Ω] (σ : Ω →+* ℂ) :"),
   ("hM1 Ω (A.baseChange Ω)", "hM1 Ω σ (A.baseChange Ω)")]),
 (H+"TailF.lean", "finrank_end0", ("theorem",), [
   ("{k : Type} [Field k] (A : PkgI3.AbVar k) :", "{k : Type} [Field k] (σ : k →+* ℂ) (A : PkgI3.AbVar k) :"),
   ("hM1 k A A", "hM1 k σ A A")]),
 (H+"TailF.lean", "QMSplitCaseRank", ("def",), [
   ("[Algebra k Ω] (φ : O →+* PkgI3.AbVar.End A)", "[Algebra k Ω] (_ : Ω →+* ℂ) (φ : O →+* PkgI3.AbVar.End A)")]),
 (H+"TailF.lean", "qmEndRank_of", ("theorem",), [
   ("refine le_antisymm ?_ (four_le_finrank_hf hM1 A' φ hφ)",
    "refine le_antisymm ?_ (four_le_finrank_hf hM1 ((" + SQ + ").comp (IntermediateField.val L').toRingHom) A' φ hφ)"),
   ("finrank_le_baseChange_hf hM1 A' Ω", "finrank_le_baseChange_hf hM1 A' Ω (_root_.HFReroute.sigmaAlgClosure ((" + SQ + ").comp (IntermediateField.val L').toRingHom))"),
   ("(finrank_end0_hf hM1 A'').symm", "(finrank_end0_hf hM1 (_root_.HFReroute.sigmaAlgClosure ((" + SQ + ").comp (IntermediateField.val L').toRingHom)) A'').symm"),
   ("exact hS L' A' Ω φ hφ", "exact hS L' A' Ω (_root_.HFReroute.sigmaAlgClosure ((" + SQ + ").comp (IntermediateField.val L').toRingHom)) φ hφ")]),
 (H+"TailF.lean", "qmSplitCaseRank", ("theorem",), [
   ("intro k _ _ A Ω _ _ _ φ _ hdim hdiv d _ he", "intro k _ _ A Ω _ _ _ σΩ φ _ hdim hdiv d _ he"),
   ("hM1 k A A", "hM1 k (σΩ.comp (algebraMap k Ω)) A A"),
   ("hM1 Ω (A.baseChange Ω)", "hM1 Ω σΩ (A.baseChange Ω)"),
   ("finrank_end0_hf hM1 A", "finrank_end0_hf hM1 (σΩ.comp (algebraMap k Ω)) A")]),
 (H+"TailF.lean", "qmEndRank_of_leaves", ("theorem",), []),
 (H+"TailI.lean", "qmEndRank_of_leaves3", ("theorem",), []),
 (H+"TailI.lean", "linkedTateLocal_of_leaves3", ("theorem",), []),
]
items += B

# dot-notation helpers on carriers (renamed through the structure name, not the short name)
NOREN = set()
for s_ in ["belyiX1", "frobeniusDense", "leafSqrtCrit", "x1ModelExists"]:
    items.append((H + "LPrefix.lean", "TextbookLeaves." + s_, ("theorem",), []))
    NOREN.add("TextbookLeaves." + s_)

# part-A edits
extra = {
 "textbookLeaves4_of_open6": [("t6 := t6_of_algClosed5 t.homFreeFiniteAlgClosed", "t6 := t.homFreeFiniteAlgClosed")],
 "openTextbookLeaves%d_of_OpenTextbookLeaves%d" % (TOPN - 1, TOPN): [("homFreeFiniteAlgClosed := n.homFreeFiniteAlgClosed",
    "homFreeFiniteAlgClosed := _root_.ZInQ.Contrib.OneProof.HomFreeC.homFreeFiniteC _root_.uniformizationLeafAll_proof n.mumfordTorsionAlgClosed")],
}

WHICH = {("ZInQKernel/HDecomp/Objects.lean", "finrank_equivEnd"): 0}
ren = {s: newname(s) for (_, s, _, _) in items if s not in NOREN}
# dedupe and order
uniq = {}
for f, s, k, e in items:
    key = (f, s)
    if key in uniq: continue
    hits = find_decl(f, s) if k is None else find_decl(f, s, k)
    w = WHICH.get(key)
    if len(hits) != 1 and w is None:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[key] = (rank[f], hits[w or 0], f, s, k, e + extra.get(s, []), w or 0)
blocks = []
bblocks = []
BSET = {(f, n) for (f, n, _, _) in B}
TYPAT = re.compile(r"(?<![\w.'])(_root_\.)?(PkgI3\.)?HomFreeFinite(?![\w'])")
for _, _, f, s, k, e, w in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, w)
    txt = TYPAT.sub(HFC, txt)
    txt = txt.replace("_root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed", HFC)
    for a, b in e:
        if a not in txt:
            raise SystemExit(f"edit not applicable in {s}: {a!r}")
        txt = txt.replace(a, b)
    # no notation commands in a contribution: expand the local notation `Kd[d]` (TailC)
    txt = re.sub(r'^local notation "Kd\[" d "\]" => .*\n', "", txt, flags=re.M)
    txt = re.sub(r"Kd\[([^\]]+)\]", r"(AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (\1) : Polynomial ℚ))", txt)
    if "notation" in txt and re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation left in {s}")
    (bblocks if (f, s) in BSET else blocks).append(txt)
d = os.path.dirname(__file__)
hdrB = open(os.path.join(d, "header_consumers.lean")).read()
hdrA = open(os.path.join(d, "header.lean")).read()
open(sys.argv[1], "w").write(hdrB + "\n" + "\n".join(bblocks))
open(sys.argv[2], "w").write(hdrA + "\n" + "\n".join(blocks))
print(len(bblocks), len(blocks), "blocks")
