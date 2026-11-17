"""fold34-eichler generator: the bypass of eichler-bound, regenerated on the current tree.

Copies every declaration listed by scratch/fold34-eichler/Taint.lean (T: value depends on a count field; S: type
mentions a structure with a count field), except Main's frozenTarget, renamed X -> X_eb / XEB, with
* every count field (`r5count`, `gonzalezRotgerCountX6`, `gonzalezRotgerCountX6Ab`, `gonzalezRotgerProp56X6`) of a
  copied structure typed `_root_.GR56.R5fpCountLe` (docstring replaced);
* every assignment `F := <expr reading x.G>` of a count field F replaced by `F := x.G`;
* the one reader `FS5NoCM.fibreComTrivialFull_of_leaves_hf''` replaced by its `_le` form (Contrib/OneProof/R5fpCountLeHF).
Run from the repository root (after Taint.lean has written TAINT):
  python3 scratch/fold34-eichler/gen/gen.py TAINT OUT.lean
e.g. python3 scratch/fold34-eichler/gen/gen.py scratch/fold34-eichler/taint_out.txt ZInQKernel/OneProof/H/EichlerBoundCopy.lean"""
import re, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

FIELDS = ("r5count", "gonzalezRotgerCountX6Ab", "gonzalezRotgerCountX6", "gonzalezRotgerProp56X6")
FRE = "|".join(FIELDS)
TAINT, OUT = sys.argv[1], sys.argv[2]


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "EB" + pr
    return base + "_eb" + pr


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
cfull = re.findall(r"[\w.]+", cl[len("carriers "):])
cnames = sorted({c.split(".")[-1] for c in cfull})
items = []
items_ns = []
for l in tl:
    m = re.match(r"^([TS]) (\S+) (\S+)", l)
    if not m: continue
    kind, mod, name = m.groups()
    parts = name.split(".")
    if mod == "ZInQKernel.OneProof.Main": continue
    if len(parts) > 1 and parts[-2] in cnames:
        items_ns.append((mod2file(mod), parts[-2], parts[-1]))   # projections, mk, or a namespaced lemma
        continue
    items.append((mod2file(mod), parts[-1]))
def cfile(c):
    for f in order:
        if re.search(r"^structure " + c + r" ", open(f).read(), re.M):
            return f
    raise SystemExit("no file for " + c)
structs = {c: cfile(c) for c in cnames}
for c, f in structs.items():
    items.append((f, c))

ren = {s: newname(s) for (_, s) in items}
# lemmas in a carrier's namespace (e.g. `ResearchLeaves3.h5`, read as `r.h5`): copied under the renamed namespace
for f, c, x in items_ns:
    fields = re.findall(r"^  (\w+) :", re.search(r"^structure " + c + r" : Prop where\n((?:  .*\n|\n)*?)(?=^\S)",
                        open(structs[c]).read(), re.M).group(1), re.M)
    if x in fields or x == "mk":
        continue
    items.append((f, c + "." + x))
uniq = {}
for f, s in items:
    if (f, s) in uniq: continue
    k = ("structure",) if s in structs else ("theorem", "lemma", "def", "abbrev", "instance")
    hits = find_decl(f, s, k)
    if len(hits) != 1:
        raise SystemExit(f"{s} in {f}: {len(hits)} hits")
    uniq[(f, s)] = (rank[f], hits[0], f, s, k)

NEWDOC = ("  /-- fold34-eichler (eichler-bound): the upper bound `#CM(R) ≤ 2^{b(R)} h(R)` (`GR56.R5fpCountLe`), the only\n"
          "  half of González–Rotger's count that the chain reads (`FS5NoCM.nocm_on_witness_le`); replaces this generation's\n"
          "  count field of the same name. -/\n")


def struct_swap(txt, s):
    n = 0
    def rep(mo):
        nonlocal n
        n += 1
        return NEWDOC + f"  {mo.group(2)} : _root_.GR56.R5fpCountLe\n"
    txt2 = re.sub(r"(  /--(?:(?!/--|^  \w+ :).)*?-/\n)?  (" + FRE + r") : [^\n]*\n((?:    [^\n]*\n)*)",
                  rep, txt, flags=re.S | re.M)
    if n != 1:
        raise SystemExit(f"struct {s}: {n} count fields")
    return txt2


def assign_swap(txt, s, log):
    L = txt.split("\n")
    out = []
    i = 0
    while i < len(L):
        l = L[i]
        m = re.match(r"^(\s+)(" + FRE + r") :=(.*)$", l)
        if m:
            ind = m.group(1)
            chunk = [l]
            j = i + 1
            while j < len(L) and L[j].strip() and len(L[j]) - len(L[j].lstrip()) > len(ind):
                chunk.append(L[j]); j += 1
            c = "\n".join(chunk)
            v = re.search(r"(?<![\w.'])(\w+)\.(" + FRE + r")(?![\w'])", c)
            if not v:
                raise SystemExit("no source count field in " + s + ": " + c)
            comma = "," if c.rstrip().endswith(",") else ""
            new = f"{ind}{m.group(2)} := {v.group(1)}.{v.group(2)}{comma}"
            if new.strip() != c.strip():
                log.append(f"{s}: {c.strip()!r} -> {new.strip()!r}")
            out.append(new)
            i = j
            continue
        out.append(l)
        i += 1
    return "\n".join(out)


log = []
blocks = []
seen_top = set()
nread = 0
for _, _, f, s, k in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, 0, seen_top)
    if s in structs:
        txt = struct_swap(txt, s)
    else:
        txt = assign_swap(txt, s, log)
        if "FS5NoCM.fibreComTrivialFull_of_leaves_hf''" in txt:
            txt = txt.replace("FS5NoCM.fibreComTrivialFull_of_leaves_hf''", "FS5NoCM.fibreComTrivialFull_of_leaves_hf''_le")
            nread += 1
    # a count field read anywhere but in a forwarding line is an unhandled reader
    for mo in re.finditer(r"(?<![\w.'])(\w+)\.(" + FRE + r")(?![\w'])", txt):
        line = txt[txt.rfind("\n", 0, mo.start()) + 1: txt.find("\n", mo.end())]
        if not re.match(r"^\s+(" + FRE + r") := \w+\.(" + FRE + r"),?$", line) and "fibreComTrivialFull_of_leaves_hf''_le" not in txt[max(0, mo.start() - 400):mo.start()]:
            raise SystemExit(f"unhandled read in {s}: {line!r}")
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation in {s}")
    blocks.append(txt)
if nread != 1:
    raise SystemExit(f"reader replaced {nread} times")
hdr = open(os.path.join(os.path.dirname(__file__), "header.lean")).read()
hdr = re.sub(r"^import ZInQKernel\.OneProof\.H\.TailZ\d+$", "import " + TOPMOD, hdr, count=1, flags=re.M)
open(OUT, "w").write(hdr + "\n" + "\n".join(blocks))
print(len(blocks), "blocks;", len(structs), "structures;", "top module", TOPMOD)
print("\n".join(log))
