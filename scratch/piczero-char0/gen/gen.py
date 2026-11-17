"""piczero-char0 generator: writes the rerouted chain (copies of every declaration of frozenTarget's proof that reads
picZeroAbVar or a field computed from it, or takes a bundle carrying one) as one Lean module, with
* picZeroAbVar : T09Pic.PicZeroAbVar            -> PicZeroChar0.PicZeroAbVar0
* mumfordKLFiniteSectionAC : PicFix....          -> PicZeroChar0.MumfordKLFiniteSectionAC0
* phiAmpleIsogeny : T09Pic.PhiAmpleIsogeny       -> PicZeroChar0.PhiAmpleIsogeny0
* t09SymmIsogenyExists : WeilPairing.T09_...     -> PicZeroChar0.T09_SymmIsogenyExists0
* t9 (dead: only the discarded antecedent of G12Det) removed, with G12Det, g12, g8_g12_hf, g12Det_of copied
  without it.
Copied names X -> X_pz (structures XPZ). Run from the repository root:
  python3 scratch/piczero-char0/gen/gen.py OUT.lean"""
import re, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

H = "ZInQKernel/OneProof/H/"
HF = "ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean"
HFC = "ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute/Consumers.lean"
P0 = "_root_.PicZeroChar0."
TAINT = "scratch/piczero-char0/taint2_out.txt"

def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "PZ" + pr
    return base + "_pz" + pr

def mod2file(m): return m.replace(".", "/") + ".lean"
def imports(f): return [l.split()[1] for l in open(f) if l.startswith("import ")]
order, seen = [], set()
def visit(m):
    if m in seen: return
    seen.add(m)
    f = mod2file(m)
    if not os.path.exists(f): return
    for i in imports(f):
        if i.startswith("ZInQKernel"): visit(i)
    order.append(f)
sys.setrecursionlimit(100000)
TOPMOD = max(re.findall(r"^import (ZInQKernel\.OneProof\.H\.TailZ\d+)$", open("ZInQKernel/OneProof/Main.lean").read(), re.M),
             key=lambda m: int(m.rsplit("TailZ", 1)[1]))
visit(TOPMOD)
rank = {f: i for i, f in enumerate(order)}

tl = open(TAINT).read().split("\n")
cl = [l for l in tl if l.startswith("carriers ")][0]
cnames = sorted({c.split(".")[-1] for c in re.findall(r"[\w.]+", cl[len("carriers "):])})
items = []
for l in tl:
    m = re.match(r"^([TS]) (\S+) (\S+)", l)
    if not m: continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    if mod == "ZInQKernel.OneProof.Main": continue
    if len(parts) > 1 and parts[-2] in cnames: continue   # projections, mk
    items.append((mod2file(mod), parts[-1], None, []))
def cfile(c):
    for f in sorted(glob.glob(H + "*.lean")) + [HF]:
        if re.search(r"^structure " + c + r" ", open(f).read(), re.M):
            return f
    raise SystemExit("no file for " + c)
for c in cnames:
    items.append((cfile(c), c, ("structure",), []))
NOREN = set()
for s_ in ["belyiX1", "frobeniusDense", "leafSqrtCrit", "x1ModelExists"]:
    items.append((HF, "TextbookLeavesHF." + s_, ("theorem",), []))
    NOREN.add("TextbookLeavesHF." + s_)

# part B: the consumers whose statements change
B = [
 (H + "TailA.lean", "G12Det", ("def",), [
   ("HSyn.EigenformRepExists → LeafPush.T09_WeilPairing.{0} →", "HSyn.EigenformRepExists →")]),
 (H + "TailA.lean", "g12", ("theorem",), [
   ("\n    (hT9 : LeafPush.T09_WeilPairing.{0}) (hW : G12Weight)", "\n    (hW : G12Weight)"),
   ("hD hR14 hT9 K A", "hD hR14 K A")]),
 (H + "TailA.lean", "g12Det_of", ("theorem",), [
   ("  intro _ _ K _ _ A r e N", "  intro _ K _ _ A r e N")]),
 (HFC, "g8_g12_hf", ("theorem",), [
   ("\n    (hT9 : LeafPush.T09_WeilPairing.{0})\n", "\n"),
   (" hT18 hT19 hT9 hW hD A T", " hT18 hT19 hW hD A T")]),
 (H + "TailK.lean", "tatePairingZl_of_leaves4", ("theorem",), []),
 (H + "TailK.lean", "detTate_of_leaves4", ("theorem",), []),
]
items += B

extra = {
 "addedLeaves12_of_open13": [("_root_.T09Pic.t09SymmIsogenyExists_of_four", P0 + "t09SymmIsogenyExists0_of_four")],
 "openAddedLeaves18_of_OpenAddedLeaves19": [("_root_.PicFix.phiAmpleIsogeny_of_printed", P0 + "phiAmpleIsogeny0_of_printed")],
 "openAddedLeaves19_of_OpenAddedLeaves20": [("_root_.PhiAmple.mumfordKLFiniteSectionAC_of_open",
                                             P0 + "mumfordKLFiniteSectionAC0_of_open")],
 "openTextbookLeaves13_of_OpenTextbookLeaves14_hf": [
   ("_root_.ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open ",
    P0 + "Poincare.poincareComplement_of_open0 "),
   ("_root_.PicFix.phiAmpleIsogeny_of_printed", P0 + "phiAmpleIsogeny0_of_printed")],
 "g8_g12_of_leaves3_hf": [("HSyn.t19_proved t.t9 (g8Matrix", "HSyn.t19_proved (g8Matrix")],
}

ren = {s: newname(s) for (_, s, _, _) in items if s not in NOREN}
uniq = {}
for f, s, k, e in items:
    key = (f, s)
    if key in uniq: continue
    hits = find_decl(f, s) if k is None else find_decl(f, s, k)
    if len(hits) != 1:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[key] = (rank[f], hits[0], f, s, k, e + extra.get(s, []))
used_extra = set()
SWAPS = [
 (re.compile(r"(?<![\w.'])(_root_\.)?(HDec\.)?WeilPairing\.T09_SymmIsogenyExists(?![\w'])"), P0 + "T09_SymmIsogenyExists0"),
 (re.compile(r"(?<![\w.'])(_root_\.)?T09Pic\.PicZeroAbVar(?![\w'])"), P0 + "PicZeroAbVar0"),
 (re.compile(r"(?<![\w.'])(_root_\.)?T09Pic\.PhiAmpleIsogeny(?![\w'])"), P0 + "PhiAmpleIsogeny0"),
 (re.compile(r"(?<![\w.'])(_root_\.)?PicFix\.MumfordKLFiniteSectionAC(?![\w'])"), P0 + "MumfordKLFiniteSectionAC0"),
]
blocks = []
seen_top = set()
for _, _, f, s, k, e in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, 0, seen_top)
    for a, b in e:
        if a not in txt:
            raise SystemExit(f"edit not applicable in {s}: {a!r}")
        txt = txt.replace(a, b)
    if s in extra: used_extra.add(s)
    for p, b in SWAPS:
        txt = p.sub(b, txt)
    # T9 is dead: drop the field and its assignments
    txt = re.sub(r"^  t9 : LeafPush\.T09_WeilPairing\.\{0\}\n", "", txt, flags=re.M)
    txt = re.sub(r"^  t9 := .*\n", "", txt, flags=re.M)
    if re.search(r"\bt9\b", re.sub(r"--.*", "", txt)) and s not in ("G12Det",):
        print("note: t9 still mentioned in", s)
    txt = re.sub(r'^local notation "Kd\[" d "\]" => .*\n', "", txt, flags=re.M)
    txt = re.sub(r"Kd\[([^\]]+)\]", r"(AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (\1) : Polynomial ℚ))", txt)
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation left in {s}")
    blocks.append(txt)
missing = set(extra) - used_extra
if missing: raise SystemExit(f"extra edits unused: {missing}")
hdr = open(os.path.join(os.path.dirname(__file__), "header.lean")).read()
open(sys.argv[1], "w").write(hdr + "\n" + "\n".join(blocks))
print(len(blocks), "blocks")
