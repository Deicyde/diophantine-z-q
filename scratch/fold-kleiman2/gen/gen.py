"""fold-kleiman2: generate the copy reroute that replaces the added field `kleimanPicZeroProper`
(`PicFix.KleimanPicZeroProper`) by the leaf `kleimanPicZeroProper954` (`KleimanSection2.KleimanPicZeroProper954`).

Usage (from the repository root):  python3 scratch/fold-kleiman2/gen/gen.py [--write]

It reads `ZInQKernel/OneProof/Main.lean` for the current top theorem `HDec.HSyn.sixContactMin_of_openM` and its added
bundle `OpenAddedLeavesA`, walks the chain of `sixContactMin_*` theorems below it in `ZInQKernel/OneProof/H/`, and
copies (verbatim up to renaming `X ↦ X_k954`, `OpenAddedLeavesA ↦ OpenAddedLeavesN`) every declaration on that chain
that takes the added bundle, plus every declaration they call that takes it, until the generation where the chain
converts the bundle to `OpenAddedLeaves24` (`openAddedLeaves24_of_OpenAddedLeaves25 l`); there the copy enters
fold33-pic's `sixContactMin_of_open45_pz{,_eb}` with `openAddedLeaves22PZ_of_OpenAddedLevesN l`, whose
`picZeroAbVar` is `KleimanSection2.picZeroAbVar0_of_954`. The one reader of `l.kleimanPicZeroProper` outside that
conversion, `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open`, is replaced by
`hodgeTateDecompAbVar_of_open_k954` (the same proof with `PicZeroAbVar0` from the 954 leaf). Any other reader of the
field makes the script stop with an error (then extend REPLACE below). No existing declaration is changed.

Output: `ZInQKernel/OneProof/H/TailZ{K+1}.lean` (K = the largest existing TailZ number) with `--write`, else stdout,
and the Main.lean patch is printed (apply with --write too: it retypes `l` and the top call).
"""
import os
import re
import sys

ROOT = os.getcwd()
HDIR = os.path.join(ROOT, "ZInQKernel/OneProof/H")
MAIN = os.path.join(ROOT, "ZInQKernel/OneProof/Main.lean")
SUF = "_k954"
FIELD_OLD = "kleimanPicZeroProper"
FIELD_NEW = "kleimanPicZeroProper954"

# reader replacements inside copied declarations (regex, replacement)
REPLACE = [
    (re.compile(r"_root_\.ZInQ\.Contrib\.HodgeTateFromPairing\.hodgeTateDecompAbVar_of_open\b(.*?)\bl\.kleimanPicZeroProper\b"),
     r"hodgeTateDecompAbVar_of_open_k954\1l.kleimanPicZeroProper954"),
]


def die(msg):
    sys.stderr.write("gen.py: " + msg + "\n")
    sys.exit(1)


# ---------------------------------------------------------------- index of H declarations
DECL = re.compile(r"^(theorem|structure|def|lemma|abbrev) ([A-Za-z_][\w']*)\b")
index = {}  # short name -> (file, start, end, kind)
for fn in sorted(os.listdir(HDIR)):
    if not fn.endswith(".lean"):
        continue
    path = os.path.join(HDIR, fn)
    L = open(path).read().split("\n")
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m:
            continue
        # docstring directly above
        s = i
        if s > 0 and L[s - 1].rstrip().endswith("-/"):
            k = s - 1
            while k >= 0 and not L[k].lstrip().startswith("/--"):
                k -= 1
            s = k
        e = i + 1
        while e < len(L) and (L[e].startswith(" ") or L[e].startswith("\t")):
            e += 1
        name = m.group(2)
        if name in index and index[name][0] != path:
            index.setdefault("__dups__", set()).add(name)
        index[name] = (path, s, e, m.group(1), i)
DUPS = index.pop("__dups__", set())


def text(name):
    p, s, e, _, _ = index[name]
    return "\n".join(open(p).read().split("\n")[s:e])


def header_body(t):
    # split declaration text at the first ':=' or ' where' after the declaration line (not in the docstring)
    m0 = re.search(r"^(theorem|lemma|def|abbrev) ", t, re.M)
    off = m0.start() if m0 else 0
    m = re.search(r"(:=|\bwhere\b)", t[off:])
    k = off + m.start()
    return t[:k], t[k:]


# ---------------------------------------------------------------- top of the chain (Main.lean)
main = open(MAIN).read()
m = re.search(r"\(l : HDec\.HSyn\.(OpenAddedLeaves\d+)\)", main)
if not m:
    die("Main.lean: no `(l : HDec.HSyn.OpenAddedLeavesA)` binder")
OLD = m.group(1)
m = re.search(r"HDec\.HSyn\.(sixContactMin_of_open\d+) r t l", main)
if not m:
    die("Main.lean: no `HDec.HSyn.sixContactMin_of_openM r t l` call")
TOP = m.group(1)
maxA = max(int(x) for x in re.findall(r"structure OpenAddedLeaves(\d+)\b",
                                       "\n".join(open(os.path.join(HDIR, f)).read() for f in os.listdir(HDIR) if f.endswith(".lean"))))
NEW = f"OpenAddedLeaves{maxA + 1}"
maxM = max(int(x) for x in re.findall(r"theorem sixContactMin_of_open(\d+)\b",
                                      "\n".join(open(os.path.join(HDIR, f)).read() for f in os.listdir(HDIR) if f.endswith(".lean"))))
NEWTOP = f"sixContactMin_of_open{maxM + 1}"
maxT = max(int(x) for x in re.findall(r"^TailZ(\d+)\.lean$", "\n".join(os.listdir(HDIR)), re.M))
MOD = f"TailZ{maxT + 1}"
TOPMOD = os.path.basename(index[TOP][0])[:-5]

if OLD not in index or index[OLD][3] != "structure":
    die(f"bundle {OLD} not found")
old_struct = text(OLD)
if f"  {FIELD_OLD} :" not in old_struct:
    die(f"{OLD} has no field {FIELD_OLD} (already folded?)")
if "  picRepresentableAbVar :" not in old_struct:
    die(f"{OLD} has no field picRepresentableAbVar: extend the conversion to OpenAddedLeaves22PZ by hand")

# ---------------------------------------------------------------- walk
TERM = re.compile(r"\bopenAddedLeaves24_of_OpenAddedLeaves25 l\b")
IDENT = re.compile(r"(?<![\w.'])[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*")
copy = []      # in discovery order (top first)
seen = set()
todo = [TOP]
terminal = None
while todo:
    n = todo.pop(0)
    if n in seen:
        continue
    seen.add(n)
    if n in DUPS:
        die(f"{n} is declared in two H modules")
    t = text(n)
    hdr, body = header_body(t)
    if OLD not in hdr:
        continue
    copy.append(n)
    if TERM.search(body):
        if OLD != "OpenAddedLeaves25":
            die("terminal conversion found but the bundle is not OpenAddedLeaves25")
        terminal = n
        continue
    for tok in set(IDENT.findall(body)):
        short = tok.split(".")[-1] if tok.startswith("_root_.HDec.HSyn.") else tok
        if short in index and short not in seen and index[short][3] in ("theorem", "def", "lemma", "abbrev"):
            todo.append(short)
if terminal is None:
    die("no terminal conversion `openAddedLeaves24_of_OpenAddedLeaves25 l` reached")

ren = {n: n + SUF for n in copy}


def rename(t):
    def sub(mm):
        tok = mm.group(0)
        return ren.get(tok, tok)
    t = re.sub(r"(?<![\w.'])[A-Za-z_][\w']*", sub, t)
    return re.sub(rf"\b{OLD}\b", NEW, t)


def dep_order(names):
    # bottom-up: a declaration after the copies it calls
    out, done = [], set()

    def visit(n):
        if n in done:
            return
        done.add(n)
        _, body = header_body(text(n))
        for c in names:
            if c != n and re.search(rf"(?<![\w.']){re.escape(c)}(?![\w'])", body):
                visit(c)
        out.append(n)
    for n in names:
        visit(n)
    return out


blocks = []
for n in dep_order(copy):
    p, s, e, kind, i = index[n]
    t = text(n)
    hdr, body = header_body(t)
    if n == terminal:
        mm = re.search(r"\b(sixContactMin_of_open47(_eb)?) r t \(openAddedLeaves24_of_OpenAddedLeaves25 l\)", body)
        if not mm:
            die(f"terminal {n}: unexpected body {body!r}")
        tgt = "sixContactMin_of_open45_pz" + (mm.group(2) or "")
        body = body.replace(mm.group(0), f"{tgt} r t (openAddedLeaves22PZ_of_{NEW} l)")
        # the head of the terminal is renamed but the target is not a copy
    for rx, rp in REPLACE:
        body = rx.sub(rp, body)
    if re.search(rf"\b{FIELD_OLD}\b(?!954)", body):
        die(f"{n} reads {FIELD_OLD} in an unknown way: extend REPLACE")
    hdr2 = rename(hdr)
    body2 = rename(body)
    # docstring tag
    hdr2 = hdr2.replace("-/\ntheorem", f" Copy (fold-kleiman2): added bundle `{NEW}`, `{FIELD_OLD}` replaced by "
                        f"`{FIELD_NEW}` (Kleiman 9.5.4 as printed). -/\ntheorem", 1)
    rel = os.path.relpath(p, ROOT)
    blocks.append(f"-- copied from {rel}:{i + 1} ({n})\n" + hdr2 + body2)

# ---------------------------------------------------------------- the new bundle
# split the structure into field chunks (docstring + field line)
lines_ = old_struct.split("\n")
start = next(k for k, l in enumerate(lines_) if l.startswith("structure "))
chunks, cur = [], []
for l in lines_[start + 1:]:
    cur.append(l)
    if re.match(r"^  [A-Za-z_][\w']* : ", l):
        chunks.append(cur)
        cur = []
keep = [c for c in chunks if not re.match(rf"^  {FIELD_OLD} : ", c[-1])]
names_kept = [re.match(r"^  ([A-Za-z_][\w']*) : ", c[-1]).group(1) for c in keep]
new_field = f"""  /-- kleiman-section2, printed form: Kleiman, *The Picard scheme* (FGA Explained, Ch. 9; arXiv math/0504020),
  Thm 9.5.4, under its own hypotheses: for `X` projective (a closed immersion into `ℙ^N_K` over `K`), geometrically
  integral and geometrically normal over a field `K`, with a `K`-point, every `P` locally of finite type over `K`
  representing the tree's `picardFunctor` on locally Noetherian `K`-schemes, and every open `V` on the connected
  component of the point classifying `𝒪_X`, `V → Spec K` is proper (numbering and hypotheses as reported from the
  arXiv text; UNVERIFIED on the host). Weaker than `{FIELD_OLD}` (which assumed `X` only proper); its one use, as
  `PicZeroChar0.PicZeroAbVar0`, is `KleimanSection2.picZeroAbVar0_of_954`. -/
  {FIELD_NEW} : _root_.KleimanSection2.KleimanPicZeroProper954"""
struct = (f"/-- `{OLD}` without `{FIELD_OLD}`, with the leaf `{FIELD_NEW}` (fold-kleiman2, kleiman-section2). -/\n"
          f"structure {NEW} : Prop where\n" + "\n".join("\n".join(c) for c in keep) + "\n" + new_field)

conv = f"""/-- `OpenAddedLeaves22PZ` (fold33-pic's generation whose field is `picZeroAbVar : PicZeroChar0.PicZeroAbVar0`) from
`{NEW}`: `picZeroAbVar` by `KleimanSection2.picZeroAbVar0_of_954` (with `PicLocFinType`, `IdentityComponentLFT` and
Cartier's theorem proved). -/
theorem openAddedLeaves22PZ_of_{NEW} (n : {NEW}) : OpenAddedLeaves22PZ where
  picRepresentableAbVar := n.picRepresentableAbVar
  picZeroAbVar := _root_.KleimanSection2.picZeroAbVar0_of_954 n.{FIELD_NEW}"""

ht = """/-- `ZInQ.Contrib.HodgeTateFromPairing.t09SymmIsogenyExists0_of_open` with `PicZeroAbVar0` from Kleiman 9.5.4 as
printed (`KleimanSection2.picZeroAbVar0_of_954`) instead of `PicFix.KleimanPicZeroProper` (fold-kleiman2). -/
theorem t09SymmIsogenyExists0_of_open_k954 (h1 : _root_.T09Pic.PicRepresentableAbVar)
    (hK : _root_.KleimanSection2.KleimanPicZeroProper954) (hM : _root_.AvSplit.MumfordTorsionAlgClosed) :
    _root_.PicZeroChar0.T09_SymmIsogenyExists0 :=
  have h2 : _root_.PicZeroChar0.PicZeroAbVar0 := _root_.KleimanSection2.picZeroAbVar0_of_954 hK
  _root_.PhiSurj.t09SymmIsogenyExists0_of_four0 h1 h2 (_root_.PhiSurj.phiAmpleIsogeny0_of_open h1 h2 hM)
    (_root_.PhiSurj.weilPairingMumford0_of_open h1 h2 hM)

/-- `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open` with the leaf
`KleimanSection2.KleimanPicZeroProper954` instead of `PicFix.KleimanPicZeroProper` (fold-kleiman2; same proof). -/
theorem hodgeTateDecompAbVar_of_open_k954 (hHT : _root_.ZInQ.Contrib.HodgeTateFromPairing.HodgeTateDecompExists)
    (hM : _root_.AvSplit.MumfordTorsionAlgClosed) (h1 : _root_.T09Pic.PicRepresentableAbVar)
    (hK : _root_.KleimanSection2.KleimanPicZeroProper954) :
    _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar :=
  _root_.ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_leaves0 hHT
    _root_.ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
    _root_.ZInQ.Contrib.CloudB3W11.axSenTate_proof
    (t09SymmIsogenyExists0_of_open_k954 h1 hK hM)
    (_root_.HDec.HSyn.isogenyQuasiInverse_lf7 _root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof)
    (_root_.AvSplit.Final.h25 hM)"""

top_hdr, _ = header_body(text(TOP))
mm = re.search(r"\(r : (\w+)\) \(t : (\w+)\)", top_hdr)
R, T = mm.group(1), mm.group(2)
top = f"""/-- **G0 with only the open leaves and the open glue** (fold-kleiman2: `{FIELD_OLD}` replaced by Kleiman 9.5.4 as
printed, `{FIELD_NEW}`). -/
theorem {NEWTOP} (r : {R}) (t : {T}) (l : {NEW}) : ZInQ.SixContactMin :=
  {TOP}{SUF} r t l"""

out = f"""import ZInQKernel.OneProof.H.{TOPMOD}
import ZInQKernel.Contrib.OneProof.KleimanPicZero954

/-! # OneProof H, fold-kleiman2: `{NEWTOP}` (generated by scratch/fold-kleiman2/gen/gen.py)

Field removed: `{FIELD_OLD}` (`PicFix.KleimanPicZeroProper`, Kleiman 9.5.4 as used: `X` only proper; GLUE).
Field added: `{FIELD_NEW}` (`KleimanSection2.KleimanPicZeroProper954`, Kleiman 9.5.4 under its own hypotheses;
kleiman-section2). The new leaf is weaker than the field, so this is a copy reroute, not an autofold: the chain reads the
field only as `PicZeroChar0.PicZeroAbVar0` (through `PicZeroChar0.picZeroAbVar0_of_leaves`), which
`KleimanSection2.picZeroAbVar0_of_954` proves from the new leaf. This module copies, verbatim up to the renaming
`X ↦ X{SUF}` and `{OLD} ↦ {NEW}`, the {len(copy)} declarations from `{TOP}` down to `{terminal}` that take the added
bundle; `{terminal}{SUF}` enters fold33-pic's `sixContactMin_of_open45_pz_eb` through
`openAddedLeaves22PZ_of_{NEW}`, and `l.{FIELD_OLD}` in `openResearchLeaves35_of_OpenResearchLeaves36_eb` is read
through `hodgeTateDecompAbVar_of_open_k954`. The originals are unchanged. -/

set_option linter.style.haveILetI false

namespace HDec

namespace HSyn

{struct}

{conv}

{ht}

end HSyn

end HDec

""" + "\n\n".join("namespace HDec\nnamespace HSyn\n" + b.rstrip() + "\nend HSyn\nend HDec" for b in blocks) + f"""

namespace HDec

namespace HSyn

{top}

end HSyn

end HDec

#print axioms HDec.HSyn.{NEWTOP}
"""

new_main = main.replace(f"(l : HDec.HSyn.{OLD})", f"(l : HDec.HSyn.{NEW})", 1)
new_main = new_main.replace(f"HDec.HSyn.{TOP} r t l", f"HDec.HSyn.{NEWTOP} r t l", 1)
new_main = re.sub(r"^import ZInQKernel\.OneProof\.H\.TailZ\d+$", f"import ZInQKernel.OneProof.H.{MOD}", new_main, count=1, flags=re.M)

sys.stderr.write(f"top {TOP} ({TOPMOD}), bundle {OLD} -> {NEW}, new top {NEWTOP} in {MOD}; copied {len(copy)}: "
                 + ", ".join(dep_order(copy)) + f"; terminal {terminal}\n")
if "--write" in sys.argv:
    open(os.path.join(HDIR, MOD + ".lean"), "w").write(out)
    open(MAIN, "w").write(new_main)
    sys.stderr.write(f"wrote ZInQKernel/OneProof/H/{MOD}.lean and patched Main.lean\n")
else:
    sys.stdout.write(out)
