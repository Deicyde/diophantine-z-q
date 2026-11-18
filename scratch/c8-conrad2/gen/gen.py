"""c8-conrad2 generator (adapted from scratch/fold34-eichler/gen/gen.py): the C8 copy reroute.

Copies every declaration listed by scratch/c8-conrad2/Taint.lean (T: value depends on one of the seed fields
`t09SymmIsogenyExists`, `phiAmpleIsogeny`, `weilPairingMumford`, `detTate`; S: type mentions a structure carrying one),
except those in EXCLUDE (handwritten in the dry-run's top section), renamed X -> X_c8 / XC8, with
* in every copied structure, the first seed field replaced by `c8 : HDec.G0Galois.C8Conrad.C8Inputs` and the other
  seed fields deleted;
* in every copied term, the first assignment of a seed field `F := <expr reading x.G>` replaced by `c8 := x.c8` and
  the others deleted (if `<expr>` reads no bundle, `c8 := c8` and the declaration gets the binder `(c8 : C8Inputs)`);
* the two readers replaced: `detTate_of_leaves4_pz l.t09SymmIsogenyExists ...` (in `gluePieces_of_open4_hf_pz_eb`)
  by `l.c8`, and `g12Det_of_pz m.r14det m.detTate m.finIndex ...` (in `g8_g12_of_leaves3_hf_pz_eb`) by
  `C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10`.
Run from the repository root:
  python3 scratch/c8-conrad2/gen/gen.py TAINT OUT.lean"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

FIELDS = ("t09SymmIsogenyExists", "phiAmpleIsogeny", "weilPairingMumford", "detTate")
FRE = "|".join(FIELDS)
TAINT, OUT = sys.argv[1], sys.argv[2]
EXCLUDE = set(sys.argv[3].split(",")) if len(sys.argv) > 3 else set()
C8T = "_root_.HDec.G0Galois.C8Conrad.C8Inputs"


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + "C8" + pr
    return base + "_c8" + pr


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
    if parts[-1] in EXCLUDE: continue
    if len(parts) > 1 and parts[-2] in cnames:
        items_ns.append((mod2file(mod), parts[-2], parts[-1]))
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

NEWDOC = ("  /-- c8-conrad2: the inputs of step C8 by local algebraicity (`C8Conrad.C8Inputs`: Conrad's App. B and the\n"
          "  glue), replacing this generation's Weil-pairing fields (`t09SymmIsogenyExists` / `phiAmpleIsogeny`,\n"
          "  `weilPairingMumford` / `detTate`), which only fed `DetTate` at C8. -/\n")


ROWS = "picRepresentableAbVar|picZeroAbVar"


def strip_rows(txt):
    """delete the Picard-row fields (copied structures) and their forwarding assignments (copied terms)."""
    txt = re.sub(r"(  /--(?:(?!/--|^  \w+ :).)*?-/\n)?  (" + ROWS + r") : [^\n]*\n((?:    [^\n]*\n)*)", "", txt,
                 flags=re.S | re.M)
    L = txt.split("\n")
    out, i = [], 0
    while i < len(L):
        m = re.match(r"^(\s+)(" + ROWS + r") :=", L[i])
        if m:
            j = i + 1
            while j < len(L) and L[j].strip() and len(L[j]) - len(L[j].lstrip()) > len(m.group(1)):
                j += 1
            i = j
            continue
        out.append(L[i]); i += 1
    return "\n".join(out)


def struct_swap(txt, s):
    n = 0
    def rep(mo):
        nonlocal n
        n += 1
        return (NEWDOC + f"  c8 : {C8T}\n") if n == 1 else ""
    txt2 = re.sub(r"(  /--(?:(?!/--|^  \w+ :).)*?-/\n)?  (" + FRE + r") : [^\n]*\n((?:    [^\n]*\n)*)",
                  rep, txt, flags=re.S | re.M)
    if n == 0:
        raise SystemExit(f"struct {s}: no seed field")
    return txt2


def assign_swap(txt, s, log):
    L = txt.split("\n")
    out = []
    i = 0
    done = False
    needs_binder = False
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
            if not done:
                v = re.search(r"(?<![\w.'])(\w+)\.(" + FRE + r"|c8)(?![\w'])", c)
                comma = "," if c.rstrip().endswith(",") else ""
                if v:
                    new = f"{ind}c8 := {v.group(1)}.c8{comma}"
                else:
                    new = f"{ind}c8 := c8{comma}"
                    needs_binder = True
                log.append(f"{s}: {c.strip()[:120]!r} -> {new.strip()!r}")
                out.append(new)
                done = True
            else:
                log.append(f"{s}: deleted {c.strip()[:80]!r}")
            i = j
            continue
        out.append(l)
        i += 1
    txt = "\n".join(out)
    if needs_binder:
        txt, k = re.subn(r"^((?:theorem|def) " + re.escape(newname(s)) + r") ", r"\1 (c8 : " + C8T + ") ", txt, count=1, flags=re.M)
        if k != 1:
            raise SystemExit("binder insert failed in " + s)
        log.append(f"{s}: binder (c8 : C8Inputs) added")
    return txt


READ1 = re.compile(r"detTate_of_leaves4_pz\s+l\.t09SymmIsogenyExists\s+l\.isogenyQuasiInverse\s+t\.t5\s+\(tateModuleFree_of_t5' t\.t5\),")
READ2 = "(g12Det_of_pz m.r14det m.detTate m.finIndex (frobeniusDenseQ_of t.frobeniusDense))"
NEW2 = "(_root_.HDec.G0Galois.C8Conrad.g12DetPZ_of_inputs r.r14 r.r13 m.c8 h9 r.r10)"
log = []
blocks = []
seen_top = set()
nread = [0, 0]
for _, _, f, s, k in sorted(uniq.values()):
    txt = emit(f, s, ren, (), k, 0, seen_top)
    if s in structs:
        txt = strip_rows(struct_swap(txt, s))
    else:
        txt, a = READ1.subn("l.c8,", txt)
        nread[0] += a
        if READ2 in txt:
            txt = txt.replace(READ2, NEW2); nread[1] += 1
        txt = strip_rows(assign_swap(txt, s, log))
    for mo in re.finditer(r"(?<![\w.'])(\w+)\.(" + FRE + r")(?![\w'])", txt):
        line = txt[txt.rfind("\n", 0, mo.start()) + 1: txt.find("\n", mo.end())]
        raise SystemExit(f"unhandled read in {s}: {line!r}")
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation in {s}")
    blocks.append(txt)
print("readers replaced", nread)
hdr = open(os.path.join(os.path.dirname(__file__), "header.lean")).read()
open(OUT, "w").write(hdr + "\n" + "\n".join(blocks))
print(len(blocks), "blocks;", len(structs), "structures;", "top module", TOPMOD)
print("\n".join(log))
