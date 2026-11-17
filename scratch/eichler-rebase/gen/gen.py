"""eichler-rebase generator: the bypass fold that removes the research field `gonzalezRotgerProp56X6` on main's top
(`sixContactMin_of_open48`, TailZ55) with no new leaf.

The chain reads González–Rotger's count only as the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (the field `r5count :
LeafQM.AV.R5fpCount` of the old research bundles, consumed by `FS5NoCM.fibreComTrivialFull_of_leaves''`), and the
research generations compute `r5count` / `gonzalezRotgerCountX6` / `gonzalezRotgerCountX6Ab` from
`gonzalezRotgerProp56X6`. eichler-bound proved the bound itself, `EichlerBound.r5fpCountLe_proof :
UniformizationLeafAll → GAGAMorphism → MumfordTorsionAlgClosed → GR56.R5fpCountLe`. A weaker field cannot fill the
old ones, so this generator COPIES (fold33-pic's copylib) every declaration listed by `scratch/eichler-rebase/Taint.lean`
(`T`: its value reads one of the tainted fields; `S`: its type mentions a structure carrying one), verbatim up to
* the renaming `X ↦ X_eb` (structures and `Upper` names without `_`: `X ↦ XEB`);
* in each carrier structure, the tainted field replaced by `r5le : GR56.R5fpCountLe`;
* each assignment `f := <expr reading v.g>` of a tainted field replaced by `r5le := v.r5le`;
* the consumer `FS5NoCM.fibreComTrivialFull_of_leaves'' … r.r5count` replaced by gr56-prove's
  `FS5NoCM.fibreComTrivialFull_of_leaves''_le … r.r5le`.
It then adds `OpenResearchLeaves32` (`OpenResearchLeaves31` without `gonzalezRotgerProp56X6`, no new field), the map
to `OpenResearchLeaves31EB` (`r5le := EichlerBound.r5fpCountLe_proof uniformizationLeafAll_proof t.gagaMorphism
t.mumfordTorsionAlgClosed`), `sixContactMin_of_open49` and `ZInQ.Contrib.TYZChain.frozenTarget_E` (Main's
`frozenTarget`, verbatim, over `OpenResearchLeaves32`).

Run from the repository root:  python3 scratch/eichler-rebase/gen/gen.py TAINT_OUT.txt OUT.lean"""
import re, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

TAINT, OUT = sys.argv[1], sys.argv[2]
H = "ZInQKernel/OneProof/H/"
MAINF = "ZInQKernel/OneProof/Main.lean"


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "EB" + pr
    return base + "_eb" + pr


def mod2file(m): return m.replace(".", "/") + ".lean"
def imports(f): return [l.split()[1] for l in open(f) if l.startswith("import ")]


MAIN = open(MAINF).read()
TOPMOD = max(re.findall(r"^import (ZInQKernel\.OneProof\.H\.TailZ\d+)$", MAIN, re.M),
             key=lambda m: int(m.rsplit("TailZ", 1)[1]))
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
visit(TOPMOD)
rank = {f: i for i, f in enumerate(order)}

tl = open(TAINT).read().split("\n")
FIELDS = re.search(r"tainted fields \[([^\]]*)\]", open(TAINT).read()).group(1).replace(" ", "").split(",")
print("tainted fields", FIELDS, file=sys.stderr)
cl = [l for l in tl if l.startswith("carriers ")][0]
carriers_full = re.findall(r"[\w.]+", cl[len("carriers "):])
cnames = sorted({c.split(".")[-1] for c in carriers_full})
items = []
for l in tl:
    m = re.match(r"^([TS]) (\S+) (\S+)$", l)
    if not m: continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    if mod == "ZInQKernel.OneProof.Main": continue
    if len(parts) > 1 and parts[-2] in cnames: continue   # projections, mk
    if any(p.startswith("_") or p in ("match_1", "proof_1") or re.match(r"^(match|proof|eq)_\d+$", p) for p in parts[1:]):
        continue                                          # auxiliary
    if FIELDS and parts[-1] in FIELDS: continue          # projections of non-carrier namespaces
    items.append((mod2file(mod), parts[-1], None))


def cfile(c):
    for f in order:
        if re.search(r"^structure " + re.escape(c) + r" ", open(f).read(), re.M):
            return f
    raise SystemExit("no file for " + c)
for c in cnames:
    items.append((cfile(c), c, ("structure",)))

ren = {s: newname(s) for (_, s, _) in items}
uniq = {}
for f, s, k in items:
    key = (f, s)
    if key in uniq: continue
    hits = find_decl(f, s) if k is None else find_decl(f, s, k)
    if len(hits) != 1:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[key] = (rank[f], hits[0], f, s, k)

FALT = "|".join(re.escape(x) for x in FIELDS)
DOC_R5 = ("  /-- eichler-rebase bypass: replaces `{f}`; the upper bound `#CM(R) ≤ 2^b·h(R)`, the only half of\n"
          "  González–Rotger's count the chain reads (`FS5NoCM.nocm_on_witness`). -/\n"
          "  r5le : _root_.GR56.R5fpCountLe\n")


def edit_struct(txt):
    """replace the (unique) tainted field of a copied carrier, with its docstring and continuation lines."""
    pat = re.compile(r"(  /--(?:(?!-/).)*?-/\n)?  (" + FALT + r") :[^\n]*\n(?:    [^\n]*\n)*", re.S)
    hits = list(pat.finditer(txt))
    if len(hits) != 1:
        raise SystemExit(f"carrier with {len(hits)} tainted fields:\n{txt[:400]}")
    h = hits[0]
    return txt[:h.start()] + DOC_R5.format(f=h.group(2)) + txt[h.end():]


def edit_assign(txt):
    L = txt.split("\n")
    out, i, n = [], 0, 0
    while i < len(L):
        l = L[i]
        m = re.match(r"^(\s+)(" + FALT + r") :=(.*)$", l)
        if m:
            ind = m.group(1)
            chunk = [l]
            j = i + 1
            while j < len(L) and L[j].strip() and len(L[j]) - len(L[j].lstrip()) > len(ind):
                chunk.append(L[j]); j += 1
            c = "\n".join(chunk)
            v = re.search(r"(?<![\w.'])(\w+)\.(" + FALT + r")\b", c)
            if not v:
                raise SystemExit("no source bundle in " + c)
            comma = "," if c.rstrip().endswith(",") else ""
            out.append(f"{ind}r5le := {v.group(1)}.r5le{comma}")
            n += 1
            i = j
            continue
        out.append(l)
        i += 1
    return "\n".join(out), n


blocks = []
seen_top = set()
stats = {"struct": 0, "assign": 0, "consumer": 0}
for _, _, f, s, k in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, 0, seen_top)
    if k == ("structure",):
        txt = edit_struct(txt)
        stats["struct"] += 1
    txt, n = edit_assign(txt)
    stats["assign"] += n
    if "FS5NoCM.fibreComTrivialFull_of_leaves''" in txt:
        txt, n1 = re.subn(r"FS5NoCM\.fibreComTrivialFull_of_leaves''(?![\w'])", "FS5NoCM.fibreComTrivialFull_of_leaves''_le", txt)
        txt, n2 = re.subn(r"(?<![\w.'])(\w+)\.r5count\)", r"\1.r5le)", txt)
        assert n1 == n2 == 1, (s, n1, n2)
        stats["consumer"] += 1
    code = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", txt, flags=re.S))
    if re.search(r"\.(" + FALT + r")\b", code):
        raise SystemExit(f"unreplaced read of a tainted field in {s}:\n{txt}")
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation in {s}")
    blocks.append(txt)
print(len(blocks), "blocks", stats, file=sys.stderr)

# ---- the new top ----
_mt = re.search(r"theorem _root_\.ZInQ\.OneProof\.frozenTarget\n.*?\n(?=end ZInQ\.Contrib\.TYZChain)", MAIN, re.S).group(0)
_b = dict((v, t) for v, t in re.findall(r"\((\w) : HDec\.HSyn\.(\w+)\)", _mt))
TOPR, TOPT, TOPL = _b["r"], _b["t"], _b["l"]
TOP = re.search(r"HDec\.HSyn\.(sixContactMin_of_open(\d+)) r t l\)", _mt)
TOPN, TOPK = TOP.group(1), int(TOP.group(2))
assert TOPR in cnames, (TOPR, cnames)
RK = int(re.match(r"OpenResearchLeaves(\d+)$", TOPR).group(1))
NEWR = f"OpenResearchLeaves{RK + 1}"
NEWTOP = f"sixContactMin_of_open{TOPK + 1}"
MAIN_IMPORTS = re.findall(r"^import .*$", MAIN, re.M)
MAIN_OPENS = re.search(r"namespace ZInQ\.Contrib\.TYZChain\n\n((?:open .*\n)*)", MAIN).group(1)
topf = cfile(TOPR)
sm = re.search(r"((?:/--(?:(?!-/).)*?-/\n)?)structure " + TOPR + r" : Prop where\n((?:  .*\n)+)", open(topf).read(), re.S)
body = sm.group(2)
fl = re.findall(r"^  (\w+) :", body, re.M)
assert "gonzalezRotgerProp56X6" in fl
pieces = re.split(r"(?=^  /--)|(?=^  \w+ :)", body, flags=re.M)
# attach each docstring to the field that follows it
fields, doc = [], ""
for p in pieces:
    if not p: continue
    if p.startswith("  /--"):
        doc = p
    else:
        fields.append(doc + p); doc = ""
kept = [x for x in fields if not re.search(r"^  gonzalezRotgerProp56X6 :", x, re.M)]
assert len(kept) == len(fields) - 1
top = [f'''/-- `{TOPR}` without `gonzalezRotgerProp56X6` (eichler-rebase bypass; no new field: the only bound the chain
reads is proved, `EichlerBound.r5fpCountLe_proof`, from `uniformizationLeafAll` (proved) and the textbook fields
`gagaMorphism` and `mumfordTorsionAlgClosed`). -/
structure {NEWR} : Prop where
''' + "".join(kept)]
conv = []
for f in fl:
    if f == "gonzalezRotgerProp56X6":
        conv.append("  r5le := _root_.EichlerBound.r5fpCountLe_proof _root_.uniformizationLeafAll_proof t.gagaMorphism\n"
                    "    t.mumfordTorsionAlgClosed\n")
    else:
        conv.append(f"  {f} := n.{f}\n")
top.append(f'''/-- `{newname(TOPR)}` from `{NEWR}`: the bound `GR56.R5fpCountLe` from the textbook fields (eichler-bound). -/
theorem {newname(TOPR)[0].lower() + newname(TOPR)[1:]}_of_{NEWR} (n : {NEWR}) (t : {TOPT}) : {newname(TOPR)} where
''' + "".join(conv))
top.append(f'''/-- **G0 without `gonzalezRotgerProp56X6` and with no new leaf** (eichler-rebase bypass fold). -/
theorem {NEWTOP} (r : {NEWR}) (t : {TOPT}) (l : {TOPL}) : ZInQ.SixContactMin :=
  {newname(TOPN)} ({newname(TOPR)[0].lower() + newname(TOPR)[1:]}_of_{NEWR} r t) t l
''')
ft = _mt.replace("theorem _root_.ZInQ.OneProof.frozenTarget", "theorem frozenTarget_E", 1)
ft = re.sub(r"(?<=HDec\.HSyn\.)" + TOPR + r"(?![\w])", NEWR, ft)
ft = ft.replace(f"HDec.HSyn.{TOPN} r t l", f"HDec.HSyn.{NEWTOP} r t l")
assert NEWR in ft and NEWTOP in ft

hdr = "\n".join(MAIN_IMPORTS) + f'''
import ZInQKernel.Contrib.OneProof.GR56Lattice
import ZInQKernel.Contrib.OneProof.R5fpCountLe

/-! # eichler-rebase: the bypass fold that removes `gonzalezRotgerProp56X6` with no new leaf
(generated by `scratch/eichler-rebase/gen/gen.py` from `scratch/eichler-rebase/Taint.lean`'s output, on main's top
`{TOPN}` ({TOPMOD.split(".")[-1]}))

The chain reads González–Rotger's count only as the upper bound `#CM(R) ≤ 2^{{b(R)}} h(R)` in
`FS5NoCM.nocm_on_witness` (TailC), through the field `r5count : LeafQM.AV.R5fpCount` of the old research bundles,
which later generations compute from `gonzalezRotgerCountX6`, `gonzalezRotgerCountX6Ab` and finally
`gonzalezRotgerProp56X6`. eichler-bound proved the bound from textbook fields (`EichlerBound.r5fpCountLe_proof`). A
weaker field cannot fill the old ones, so this module copies (suffix `_eb` / `EB`) every declaration of
`{TOPN}`'s proof that reads one of these fields or takes a bundle carrying one, with the field replaced by
`r5le : GR56.R5fpCountLe`, its assignments by `r5le := _.r5le`, and the consumer by gr56-prove's
`FS5NoCM.fibreComTrivialFull_of_leaves''_le`. The originals are unchanged.
-/

set_option linter.all false
set_option maxHeartbeats 1000000
'''
tail = ("\nnamespace HDec\n\nnamespace HSyn\n\n" + "\n".join(top) + "\nend HSyn\n\nend HDec\n\n"
        "namespace ZInQ.Contrib.TYZChain\n\n" + MAIN_OPENS + "\n"
        "/-- `ZInQ.OneProof.frozenTarget` (Main.lean, verbatim) with the research bundle `" + NEWR +
        "` (no `gonzalezRotgerProp56X6`). -/\n" + ft + "\nend ZInQ.Contrib.TYZChain\n\n"
        f"#print axioms HDec.HSyn.{NEWTOP}\n#print axioms ZInQ.Contrib.TYZChain.frozenTarget_E\n")
open(OUT, "w").write(hdr + "\n" + "\n".join(blocks) + tail)
print("top", TOPN, "->", NEWTOP, "research", TOPR, "->", NEWR, file=sys.stderr)
