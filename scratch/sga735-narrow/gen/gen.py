"""sga735-narrow generator: writes the bypass fold of `sga7_IX_3_5_ForwardGeom` into the weaker leaf
`SGA735AC.SGA7_IX_3_5_ForwardGeomAC` as one Lean file (scratch check, FoldCheck.lean).

The new leaf cannot fill the old field, so every declaration of `sixContactMin_of_open41`'s proof that depends on
the field (or on `semistableUnipotent`, the field it is converted into at TailZ33) or takes a bundle carrying one of
them is copied verbatim up to the renaming `X ↦ X_sg` / `XSG` (taint list: scratch/sga735-narrow/taint_out.txt,
from Taint.lean). In the copies:
* research generations 20..28 carry `sga7_IX_3_5_ForwardGeomAC : SGA735AC.SGA7_IX_3_5_ForwardGeomAC`
  (renamed field, weakened type); generation 29 becomes the new top bundle `OpenResearchLeaves30`;
* research generations 14..19 carry `semistableUnipotent : SGA735AC.SemistableUnipotentCP` (weakened type);
* the one conversion (TailZ33's `_hf` copy) and the one consumer (`raynaudCriterionNF_of14_hf`) are edited.
Run from the repository root:  python3 scratch/sga735-narrow/gen/gen.py scratch/sga735-narrow/FoldCheck.lean
"""
import re, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

H = "ZInQKernel/OneProof/H/"
AC = "_root_.SGA735AC.SGA7_IX_3_5_ForwardGeomAC"
CP = "_root_.SGA735AC.SemistableUnipotentCP"
TOPOLD, TOPNEW = "OpenResearchLeaves29", "OpenResearchLeaves30"


def newname(n):
    if n == TOPOLD:
        return TOPNEW
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "SG" + pr
    return base + "_sg" + pr


def mod2file(m):
    return m.replace(".", "/") + ".lean"


def imports(f):
    return [l.split()[1] for l in open(f) if l.startswith("import ")]


order, seen = [], set()


def visit(m):
    if m in seen:
        return
    seen.add(m)
    f = mod2file(m)
    if not os.path.exists(f):
        return
    for i in imports(f):
        if i.startswith("ZInQKernel"):
            visit(i)
    order.append(f)


sys.setrecursionlimit(100000)
visit("ZInQKernel.OneProof.H.TailZ48")
rank = {f: i for i, f in enumerate(order)}

TAINT = "scratch/sga735-narrow/taint_out.txt"
items = []  # (file, short, kinds, edits)
for l in open(TAINT):
    m = re.match(r"^([TS]) (\S+) (\S+)", l)
    if not m:
        continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    short = parts[-1]
    if name == "HDec.HSyn.sixContactMin_of_open41":
        continue  # the top theorem is written by hand below
    if short == "mk" or (len(parts) > 1 and re.match(r"^OpenResearchLeaves\d+$", parts[-2])):
        continue  # projections / constructors come with the structures
    items.append((mod2file(mod), short, None, []))

cl = [l for l in open(TAINT) if l.startswith("carriers ")][0]
cnames = sorted({c.split(".")[-1] for c in re.findall(r"[\w.]+", cl[len("carriers "):])},
                key=lambda c: int(re.sub(r"\D", "", c) or 0))


def cfile(c):
    for f in sorted(glob.glob(H + "*.lean")):
        if re.search(r"^structure " + c + r" ", open(f).read(), re.M):
            return f
    raise SystemExit("no file for " + c)


def gen_of(c):
    return int(re.sub(r"\D", "", c))


for c in cnames:
    g = gen_of(c)
    if g >= 20:
        ed = [("  sga7_IX_3_5_ForwardGeomAC : _root_.UnipotentForward.SGA7_IX_3_5_ForwardGeom\n",
               "  sga7_IX_3_5_ForwardGeomAC : " + AC + "\n")]
    else:
        ed = [("  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent\n",
               "  semistableUnipotent : " + CP + "\n")]
    items.append((cfile(c), c, ("structure",), ed))

HF = "ZInQKernel/Contrib/OneProof/HomFreeFiniteAlgClosedReroute.lean"
extra = {
    "openResearchLeaves19_of_OpenResearchLeaves20_hf": [(
        "semistableUnipotent := _root_.UnipotentForward.semistableUnipotent_of_forwardGeom n.sga7_IX_3_5_ForwardGeomAC",
        "semistableUnipotent := _root_.SGA735AC.semistableUnipotentCP_of_forwardGeomAC n.sga7_IX_3_5_ForwardGeomAC")],
    "raynaudCriterionNF_of14_hf": [(
        "_root_.GapNeron.raynaudCriterion_leavesNF (raynaudSemistable_of14_hf_sg r t) r.semistableUnipotent",
        "_root_.SGA735AC.raynaudCriterion_leavesNF_cp (raynaudSemistable_of14_hf_sg r t) r.semistableUnipotent")],
}

ren = {s: newname(s) for (_, s, _, _) in items}
ren["sga7_IX_3_5_ForwardGeom"] = "sga7_IX_3_5_ForwardGeomAC"

uniq = {}
for f, s, k, e in items:
    key = (f, s)
    if key in uniq:
        continue
    hits = find_decl(f, s) if k is None else find_decl(f, s, k)
    if len(hits) != 1:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[key] = (rank[f], hits[0], f, s, k, e + extra.get(s, []))

used = set()
blocks = []
for _, _, f, s, k, e in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, 0)
    for a, b in e:
        if a not in txt:
            raise SystemExit(f"edit not applicable in {s}: {a!r}")
        txt = txt.replace(a, b)
        used.add((s, a))
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation left in {s}")
    if s == TOPOLD:
        txt = re.sub(r"/--[^\n]*?-/\nstructure " + TOPNEW,
                     "/-- `OpenResearchLeaves29` with `sga7_IX_3_5_ForwardGeom` replaced by the restricted leaf "
                     "`sga7_IX_3_5_ForwardGeomAC` (sga735-narrow). -/\nstructure " + TOPNEW, txt, flags=re.S)
    # each block in its own section, so that its scope commands (open/set_option) do not leak into later blocks
    blocks.append("section\n" + txt + "end\n")

for s, ed in extra.items():
    for a, _ in ed:
        if (s, a) not in used:
            raise SystemExit(f"edit for {s} not used")

# the field docstring of the new top bundle
for i, b in enumerate(blocks):
    if "structure " + TOPNEW + " " in b:
        b2 = re.sub(r"  /--[^\n]*-/\n  sga7_IX_3_5_ForwardGeomAC :",
                    "  /-- sga735-narrow, printed form (restricted): SGA 7 I Exp. IX Prop. 3.5, direction semistable => "
                    "(sigma-1)^2 = 0 on T_l = lim A(K^s)[l^n] for sigma in inertia, one sigma at a time, over a strictly "
                    "henselian DVR with algebraically closed residue field (number UNVERIFIED); a specialization of "
                    "sga7_IX_3_5_ForwardGeom (SGA735AC.forwardGeomAC_of_forwardGeom) under both readings of "
                    "semistable (k(s) or geometric special fibre); its one use is r6 at number fields. -/\n"
                    "  sga7_IX_3_5_ForwardGeomAC :", b)
        if b2 == b:
            raise SystemExit("top field docstring not replaced")
        blocks[i] = b2

hdr = open(os.path.join(os.path.dirname(__file__), "header.lean")).read()
tail = """
namespace HDec
namespace HSyn

/-- **G0 with the restricted leaf `sga7_IX_3_5_ForwardGeomAC` in place of `sga7_IX_3_5_ForwardGeom`**
(sga735-narrow; `sixContactMin_of_open41` with the research bundle `OpenResearchLeaves30`). -/
theorem sixContactMin_of_open42 (r : OpenResearchLeaves30) (t : OpenTextbookLeaves15) (l : OpenAddedLeaves20) :
    ZInQ.SixContactMin :=
  sixContactMin_of_open40_hf_sg r (openTextbookLeaves14HF_of_OpenTextbookLeaves15 t) l

end HSyn
end HDec

#print axioms HDec.HSyn.sixContactMin_of_open42
"""
open(sys.argv[1], "w").write(hdr + "\nset_option maxHeartbeats 1000000\n\n" + "\n".join(blocks) + tail)
print(len(blocks), "blocks")
