"""fold33-copy generator: a COPY reroute of the research-bundle chain.

Reads the taint list of scratch/fold33-copy/Taint.lean (every declaration of `sixContactMin_of_open41`'s proof whose
type or value mentions one of the research bundles `OpenResearchLeaves14`..`29`) and writes one Lean module with a
copy of each, verbatim up to the renaming `X ↦ X<SUF>` (structures, `Upper` names without `_`) / `x_<suf>` and the
edits of the chosen folds. The originals stay untouched.

Run from the repository root:
  python3 scratch/fold33-copy/gen/gen.py TAINT.txt FOLDS OUT.lean
FOLDS: `sga3` (sga3-nbhd: suffix NS) or `sga3,gm` (sga3-nbhd and goodmodel-iso fold G: suffix GM)."""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
from copylib import emit, find_decl

H = "ZInQKernel/OneProof/H/"
TAINT, FOLDS, OUT = sys.argv[1], sys.argv[2].split(","), sys.argv[3]
SUF = {("sga3",): "NS", ("sga3", "gm"): "GM"}[tuple(FOLDS)]
suf = SUF.lower()
EXCLUDE_MODS = {"ZInQKernel.OneProof.H.TailZ48", "ZInQKernel.OneProof.Main"}  # the old top: rewritten by hand


def newname(n):
    m = re.match(r"^(.*?)('*)$", n)
    base, pr = m.groups()
    if base[0].isupper() and "_" not in base:
        return base + SUF + pr
    return base + "_" + suf + pr


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

# ---- the taint list ----
carriers = []
srcs = []
for l in open(TAINT):
    if l.startswith("carriers "):
        carriers = re.findall(r"HDec\.HSyn\.(OpenResearchLeaves\d+)", l)
    m = re.match(r"^T (\S+) (\S+) (src|aux)$", l.strip())
    if m and m.group(3) == "src" and m.group(1) not in EXCLUDE_MODS:
        srcs.append((m.group(1), m.group(2)))
assert carriers, "no carriers line"
CARR = set(carriers)


def locate(f, full):
    """the name as written at the declaration: the shortest suffix of `full` with exactly one hit in `f`."""
    parts = full.split(".")
    for k in range(1, len(parts) + 1):
        s = ".".join(parts[-k:])
        for kinds in (("theorem", "lemma", "def", "abbrev", "structure", "instance"),):
            h = find_decl(f, s, kinds)
            if len(h) == 1:
                return s
            h2 = find_decl(f, "_root_." + s, kinds)
            if len(h2) == 1 and k == len(parts):
                return "_root_." + s
    raise SystemExit(f"cannot locate {full} in {f}")


items = []
NOREN = set()
for mod, full in srcs:
    f = mod2file(mod)
    s = locate(f, full)
    parts = full.split(".")
    if len(parts) >= 2 and parts[-2] in CARR:
        NOREN.add(parts[-1])  # helper in a carrier's namespace: renamed through the carrier's name
    items.append((f, s, full))
ren = {}
for f, s, full in items:
    short = full.split(".")[-1]
    if short in NOREN:
        continue
    ren[short] = newname(short)

# ---- the edits ----
DOC3 = ("  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;\n"
        "  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/\n")
FIELD3 = "  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10\n"
NBHD_DOC = re.compile(r"  /-- gt-sga3, narrowed: SGA 3 VI_B 3\.10 in neighbourhood form:[^\n]*-/\n"
                      r"  sga3_VIB_3_10_Nbhd : _root_\.SGA3IdComp\.SGA3_VIB_3_10_Nbhd\n")
EDITS = []  # (old, new, expected total count or None)
if "sga3" in FOLDS:
    EDITS += [
        (DOC3 + FIELD3, "  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10` not copied (its readers no longer need SGA 3 VI_B 3.10)\n", None),
        (NBHD_DOC, "  -- fold33-copy (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` not copied (its readers no longer need SGA 3 VI_B 3.10)\n", None),
        ("  sga3_VIB_3_10 := n.sga3_VIB_3_10\n", "", None),
        ("  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd\n", "", None),
        # reader 1 (TailZ23, researchLeaves9_of_open14)
        ("_root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4\n"
         "    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint",
         "_root_.SGA3Nbhd.semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 t.geomConnOfRationalPoint", None),
        # reader 2 (TailZ33)
        ("_root_.SGA7PersistsNF.sga7_IX_3_3_of_SH n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization n.sga3_VIB_3_10 t.geomConnOfRationalPoint",
         "_root_.SGA3Nbhd.NF.sga7_IX_3_3_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint", None),
        # reader 3 (TailZ41)
        ("_root_.GapPersists.semistablePersistsSHcp_of_SH n.sga3_VIB_3_10 n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint",
         "_root_.SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint", None),
        # reader 4 (TailZ44): the conversion line
        ("  sga3_VIB_3_10 := _root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof\n", "", None),
        # reader 5 (TailZ45)
        ("_root_.DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre n.sga7_IX_3_3_SHpre (_root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof) _root_.geomConnOfRationalPoint_proof",
         "_root_.SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre' n.sga7_IX_3_3_SHpre _root_.geomConnOfRationalPoint_proof", None),
        ("With sga3_VIB_3_10 and geomConnOfRationalPoint (idComp_baseChange, SGA 3 VI_B 3.3 proved) replaces sga7_IX_3_3_SH. -/",
         "With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-copy: by sga3-nbhd's "
         "SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/", None),
    ]
if "gm" in FOLDS:
    DED = "_root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind"
    EDITS += [
        ("  mumfordGroupLaw : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw\n",
         "  -- fold33-copy (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which\n"
         "  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`\n"
         "  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR\n", None),
        ("_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw",
         "_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw", None),
        ("    (_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU)\n",
         "    (_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)\n"
         "      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))\n", None),
        (re.compile(r"  /-- dict-models, printed form: Mumford-Fogarty-Kirwan, GIT, Thm 6\.14 over a connected[^\n]*-/\n"
                    r"  mumfordGroupLawConn : _root_\.DictModels\.MumfordConn\.MumfordGroupLawConn\n"),
         "  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an "
         "affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR "
         "(GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the "
         "textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). "
         "Replaces mumfordGroupLawConn. -/\n"
         "  neronSchemeExtensionDedekind : " + DED + "\n", None),
        ("  mumfordGroupLaw := _root_.DictModels.MumfordConn.mumfordGroupLaw_of_conn n.mumfordGroupLawConn\n",
         "  mumfordGroupLaw := _root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind\n", None),
        ("  mumfordGroupLawConn := n.mumfordGroupLawConn\n", "  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind\n", None),
    ]
counts = [0] * len(EDITS)

uniq = {}
for f, s, full in items:
    key = (f, s)
    if key in uniq:
        continue
    hits = find_decl(f, s)
    assert len(hits) == 1, (f, s, hits)
    uniq[key] = (rank[f], hits[0], f, s, full)
blocks = []
top_seen = set()
for _, _, f, s, full in sorted(uniq.values()):
    txt = emit(f, s, ren)
    # top-level context commands persist to the end of the module: emit each once (repeating the 220 `open` lines
    # of the sources made name resolution, hence the late conversions, time out)
    L = txt.split("\n")
    k = 1
    keep = L[:1]
    while k < len(L) and not re.match(r"^(namespace|section|noncomputable section)\b", L[k]) and not L[k].startswith("/--") \
            and re.match(r"^(open|set_option|attribute|universe|variable|local|omit|include)\b", L[k]) and not L[k].rstrip().endswith(" in"):
        if L[k] not in top_seen:
            top_seen.add(L[k])
            keep.append(L[k])
        k += 1
    txt = "\n".join(keep + L[k:])
    for i, (a, b, _) in enumerate(EDITS):
        if isinstance(a, re.Pattern):
            txt, k = a.subn(b.replace("\\", "\\\\"), txt)
        else:
            k = txt.count(a)
            txt = txt.replace(a, b)
        counts[i] += k
    if re.search(r"^\s*(local |scoped )?notation", txt, re.M):
        raise SystemExit(f"notation in {s}")
    blocks.append(txt)
body = "\n".join(blocks)
# every removed field must be gone from the code (comments aside)
code = "\n".join(l for l in body.split("\n") if not l.lstrip().startswith("--"))
code = re.sub(r"/-.*?-/", "", code, flags=re.S)
if "sga3" in FOLDS:
    assert not re.search(r"sga3_VIB_3_10", code), "sga3 field left"
if "gm" in FOLDS:
    assert "mumfordGroupLawConn" not in code and "MumfordRigidity.MumfordGroupLaw\n" not in code, "gm field left"
    assert "qmFamilyGroupLaw_of_groupLaw" not in code and "y3Connected_of_leaves" not in code
for (a, b, _), k in zip(EDITS, counts):
    print(f"{k:4d}  {(a.pattern if isinstance(a, re.Pattern) else a)[:90]!r}", file=sys.stderr)
    if k == 0:
        raise SystemExit("edit never applied")
hdr = open(os.path.join(os.path.dirname(__file__), f"header_{suf}.lean")).read()
open(OUT, "w").write(hdr + "\n" + body)
print(len(blocks), "blocks;", len(ren), "renamed short names;", "carriers", len(carriers), file=sys.stderr)
