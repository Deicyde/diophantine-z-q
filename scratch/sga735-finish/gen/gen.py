"""sga735-finish generator: the bypass fold of `sga7_IX_3_5_ForwardGeom` into the nilpotent leaf
`SGA735Nil.SGA7_IX_3_5_ForwardUnipAC`, with r6 re-typed to `SGA735Nil.RaynaudCriterionNFNil`.

Copy set: scratch/sga735-finish/r6taint_out.txt (R6Taint.lean on the closure of sixContactMin_of_open48): every
constant on the path from the top to the field or to an r6-typed constant. Each is copied verbatim up to the
renaming X -> X_nl / XNL, with
* r6's type `PkgI2.RaynaudCriterionNF.{0}` (any spelling) -> `SGA735Nil.RaynaudCriterionNFNil`;
* the field `sga7_IX_3_5_ForwardGeom : UnipotentForward.SGA7_IX_3_5_ForwardGeom` ->
  `sga7_IX_3_5_ForwardUnipAC : SGA735Nil.SGA7_IX_3_5_ForwardUnipAC`;
* `semistableUnipotent : ReductSplit.SemistableUnipotent` -> `semistableUnipotent : SGA735Nil.SemistableUnipotentNilCP`;
* the conversion and the r6 producer edited; the readers replaced by SGA7IX35UnipReaders.lean.
Run from the repository root: python3 scratch/sga735-finish/gen/gen.py scratch/sga735-finish/FoldCheck.lean
"""
import re, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

TAINT = "scratch/sga735-finish/r6taint_out.txt"
TOPOLD, TOPNEW = "OpenResearchLeaves31", "OpenResearchLeaves32"
TOPTHM, TOPTHMNEW = "sixContactMin_of_open48", "sixContactMin_of_open49"
NIL = "_root_.SGA735Nil."

# readers / producers not copied: short name -> replacement short name (defined in the Contrib files)
MAPPED = {
    "raynaudPlace_of_R6": "raynaudPlace_of_R6Nil",
    "goodReduction_of_QM_rational3_of_alg": "goodReduction_of_QM_rational3_of_alg_nil",
    "goodReduction_of_QM_rational3": "goodReduction_of_QM_rational3_nl",
    "goodReduction_of_QM_rational3'": "goodReduction_of_QM_rational3'_nl",
}
SKIP = {"raynaudCriterion_leavesNF", "raynaudCriterion_of_leavesNF", "RaynaudCriterionNF"}


def newname(n):
    if n == TOPOLD:
        return TOPNEW
    if n == TOPTHM:
        return TOPTHMNEW
    if n in MAPPED:
        return MAPPED[n]
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "NL" + pr
    return base + "_nl" + pr


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
visit("ZInQKernel.OneProof.H.TailZ55")
rank = {f: i for i, f in enumerate(order)}

bad = set()
for l in open(TAINT):
    if l.startswith("bad structures "):
        bad = {x.split(".")[-1] for x in re.findall(r"[\w.']+", l[len("bad structures "):])}

items = []
for l in open(TAINT):
    m = re.match(r"^([ABS]) (\S+) (\S+)$", l.rstrip())
    if not m:
        continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    short = parts[-1]
    if short in SKIP or short in MAPPED:
        continue
    if len(parts) > 1 and parts[-2] in bad:
        f0 = mod2file(mod)
        if not find_decl(f0, parts[-2] + "." + short):
            continue  # projections / constructors come with the structures
        items.append((f0, parts[-2] + "." + short, None, parts, name))
        continue
    k = ("structure",) if short in bad else None
    items.append((mod2file(mod), short, k, parts, name))

ren = {s.split(".")[-1]: newname(s.split(".")[-1]) for (_, s, _, _, _) in items}
ren.update(MAPPED)
ren["sga7_IX_3_5_ForwardGeom"] = "sga7_IX_3_5_ForwardUnipAC"

R6PAT = re.compile(r"(?<![\w.'])(?:_root_\.)?(?:HDec\.)?(?:PkgI2\.|GapNeron\.)?RaynaudCriterionNF(?:\.\{\w+\})?(?![\w'])")

EDITS = {
    "openResearchLeaves19_of_OpenResearchLeaves20_hf_gm": [(
        "semistableUnipotent := _root_.UnipotentForward.semistableUnipotent_of_forwardGeom n.sga7_IX_3_5_ForwardUnipAC",
        "semistableUnipotent := _root_.SGA735Nil.semistableUnipotentNilCP_of_forwardUnipAC n.sga7_IX_3_5_ForwardUnipAC")],
    "raynaudCriterionNF_of14_hf_gm": [(
        "_root_.GapNeron.raynaudCriterion_leavesNF (",
        "_root_.SGA735Nil.raynaudCriterion_leavesNF_nil (")],
}

uniq = {}
for f, s, k, parts, full in items:
    if (f, s) in uniq:
        continue
    hits = find_decl(f, s) if k is None else find_decl(f, s, k)
    dn = s
    if not hits:
        dn = ".".join(parts[-2:])
        hits = find_decl(f, dn)
    if len(hits) != 1:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[(f, s)] = (rank[f], hits[0], f, dn, k, s.split('.')[-1], full)

used = set()
blocks = []
for _, _, f, dn, k, s, full in sorted(uniq.values()):
    txt = emit(f, dn, ren, (), k, 0)
    if full.startswith("HDec.") and not re.search(r"^namespace HDec(\.|\s|$)", txt, re.M):
        txt = "namespace HDec\n" + txt + "end HDec\n"
    txt = R6PAT.sub(NIL + "RaynaudCriterionNFNil", txt)
    txt = re.sub(r"^(\s+)sga7_IX_3_5_ForwardUnipAC : (_root_\.)?UnipotentForward\.SGA7_IX_3_5_ForwardGeom\s*$",
                 r"\1sga7_IX_3_5_ForwardUnipAC : " + NIL + "SGA7_IX_3_5_ForwardUnipAC", txt, flags=re.M)
    txt = re.sub(r"^(\s+)semistableUnipotent : (_root_\.)?ReductSplit\.SemistableUnipotent\s*$",
                 r"\1semistableUnipotent : " + NIL + "SemistableUnipotentNilCP", txt, flags=re.M)
    for a, b in EDITS.get(s, []):
        if a not in txt:
            raise SystemExit(f"edit not applicable in {s}: {a!r}")
        txt = txt.replace(a, b)
        used.add(a)
    for mm in list(re.finditer(r'^local notation "(\w+)" => (.+)$', txt, re.M)):
        tok, rhs = mm.group(1), mm.group(2).strip()
        txt = txt.replace(mm.group(0) + "\n", "")
        txt = re.sub(r"(?<![\w'.])" + re.escape(tok) + r"(?![\w'])", "(" + rhs + ")", txt)
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation left in {s}")
    if "UnipotentForward.SGA7_IX_3_5_ForwardGeom" in txt:
        raise SystemExit(f"field type left in {s}")
    blocks.append("section\n" + txt + "end\n")

for s, ed in EDITS.items():
    for a, _ in ed:
        if a not in used:
            raise SystemExit(f"edit for {s} not used")

hdr = open(os.path.join(os.path.dirname(__file__), "header.lean")).read()
tail = """
#print axioms HDec.HSyn.sixContactMin_of_open49
"""
open(sys.argv[1], "w").write(hdr + "\nset_option maxHeartbeats 1000000\nset_option synthInstance.maxHeartbeats 200000\n\n" + "\n".join(blocks) + tail)
print(len(blocks), "blocks")
