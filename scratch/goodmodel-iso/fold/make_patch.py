"""goodmodel-iso combined fold G: write the patched sources under OUT/ (mirroring the tree).
usage: make_patch.py ROOT OUT

G = group-law-dvr's fold F2 with the glue `neronGoodModelIso` dropped (now proved:
`ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind`, Contrib/OneProof/NeronGoodModelIso.lean), plus the removal
of the textbook field `neronSchemeExtensionExists` (proved from the same leaf by
`ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind`).

Edits (manual: autofold cannot express them, see docs/research/goodmodel-iso.md):
 1. (group-law-dvr's narrowing, unchanged) OpenResearchLeaves14..27: field `mumfordGroupLaw` retyped from
    `MumfordRigidity.MumfordGroupLaw` to `GroupLaw.MumfordGroupLawDVR`; TailZ23's three sites and TailZ34's one site
    read it through `qmFamilyGroupLaw_of_dvr`.
 2. TailZ45: `OpenResearchLeaves28.mumfordGroupLawConn` replaced by `neronSchemeExtensionDedekind` (LEAF);
    `mumfordGroupLaw := mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.
 3. TailZ45: new generation `OpenTextbookLeaves14` (= 13 without `neronSchemeExtensionExists`), the conversion
    `openTextbookLeaves13_of_OpenTextbookLeaves14 (n) (h : NeronSchemeExtensionDedekind)`, and the top theorem
    `sixContactMin_of_open39 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves14) (l : OpenAddedLeaves19)`.
 4. Main.lean: `frozenTarget` takes `t : OpenTextbookLeaves14` and calls `sixContactMin_of_open39`.
"""
import sys, os
root, out = sys.argv[1], sys.argv[2]
OLD = "mumfordGroupLaw : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw"
NEW = "mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR"
H = "ZInQKernel/OneProof/H/"
gens = [23, 25, 26, 27, 28, 29, 33, 34, 35, 36, 37, 38, 41, 44]
files = {}


def get(p):
    if p not in files:
        files[p] = open(os.path.join(root, p)).read()
    return files[p]


def rep(p, a, b, count=1):
    s = get(p)
    n = s.count(a)
    assert n == count, (p, a[:60], n)
    files[p] = s.replace(a, b)


# 1. narrowing (group-law-dvr)
for g in gens:
    rep(H + f"TailZ{g}.lean", OLD, NEW)
rep(H + "TailZ23.lean", "import ZInQKernel.OneProof.H.TailZ40\n",
    "import ZInQKernel.OneProof.H.TailZ40\nimport ZInQKernel.Contrib.OneProof.MumfordGroupLawRed\n")
rep(H + "TailZ23.lean", "qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw",
    "qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw", 3)
rep(H + "TailZ34.lean",
    "(_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU)",
    "(_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)\n"
    "      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))")

# 2. TailZ45: the research field
p45 = H + "TailZ45.lean"
s = get(p45)
decl = "  mumfordGroupLawConn : _root_.DictModels.MumfordConn.MumfordGroupLawConn\n"
i = s.index(decl)
j = s.rfind("  /--", 0, i)
oldfield = s[j:i] + decl
newfield = ("  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an "
            "affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR "
            "(GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the "
            "textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). "
            "Replaces mumfordGroupLawConn. -/\n"
            "  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind\n")
rep(p45, oldfield, newfield)
rep(p45, "  mumfordGroupLaw := _root_.DictModels.MumfordConn.mumfordGroupLaw_of_conn n.mumfordGroupLawConn\n",
    "  mumfordGroupLaw := _root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind\n")
rep(p45, "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\n",
    "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\nimport ZInQKernel.Contrib.OneProof.NeronGoodModelIso\n")

# 3. TailZ45: the textbook generation 14 and the top theorem
p44 = H + "TailZ44.lean"
s44 = get(p44)
a = s44.index("structure OpenTextbookLeaves13 : Prop where\n")
b = s44.index("\n\n", a)
body = s44[a:b].split("\n")[1:]
kept = [l for l in body if "neronSchemeExtensionExists" not in l]
assert len(kept) == len(body) - 1, body
names = [l.split(":")[0].strip() for l in kept]
new_gen = ("\n/-- `OpenTextbookLeaves13` without `neronSchemeExtensionExists` (goodmodel-iso: its case of BLR 1.4 Thm 3 "
           "follows from the research leaf `neronSchemeExtensionDedekind`). -/\n"
           "structure OpenTextbookLeaves14 : Prop where\n" + "\n".join(kept) + "\n\n"
           "/-- `OpenTextbookLeaves13` from `OpenTextbookLeaves14` and BLR 1.4 Thm 3 over Dedekind schemes "
           "(`neronSchemeExtensionExists_of_dedekind`). -/\n"
           "theorem openTextbookLeaves13_of_OpenTextbookLeaves14 (n : OpenTextbookLeaves14)\n"
           "    (h : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) : OpenTextbookLeaves13 where\n"
           + "".join(f"  {x} := n.{x}\n" for x in names)
           + "  neronSchemeExtensionExists := _root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h\n\n"
           "/-- **G0 with only the open leaves and the open glue** (goodmodel-iso: `mumfordGroupLawConn` and "
           "`neronSchemeExtensionExists` replaced by the one leaf `neronSchemeExtensionDedekind`). -/\n"
           "theorem sixContactMin_of_open39 (r : OpenResearchLeaves28) (t : OpenTextbookLeaves14) "
           "(l : OpenAddedLeaves19) : ZInQ.SixContactMin :=\n"
           "  sixContactMin_of_open38 r (openTextbookLeaves13_of_OpenTextbookLeaves14 t r.neronSchemeExtensionDedekind) l\n")
rep(p45, "\nend HSyn\n", new_gen + "\nend HSyn\n")
rep(p45, "#print axioms HDec.HSyn.sixContactMin_of_open38",
    "#print axioms HDec.HSyn.sixContactMin_of_open38\n#print axioms HDec.HSyn.sixContactMin_of_open39")

# 4. Main.lean
pm = "ZInQKernel/OneProof/Main.lean"
rep(pm, "(t : HDec.HSyn.OpenTextbookLeaves13)", "(t : HDec.HSyn.OpenTextbookLeaves14)")
rep(pm, "(HDec.HSyn.sixContactMin_of_open38 r t l)", "(HDec.HSyn.sixContactMin_of_open39 r t l)")

for p, s in files.items():
    q = os.path.join(out, p)
    os.makedirs(os.path.dirname(q), exist_ok=True)
    open(q, 'w').write(s)
print(len(files), "files")
