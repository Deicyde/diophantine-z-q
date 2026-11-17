"""fold33-combine, field 3 (goodmodel-iso, fold G): `mumfordGroupLawConn` (research) and `neronSchemeExtensionExists`
(textbook) replaced by the one printed leaf `neronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over an affine Dedekind
scheme), on top of leaf-fold33b + the sga3-nbhd prune.

Research side: goodmodel-iso's G.patch (scratch/goodmodel-iso/fold/G.patch, written on c1e4ed1b), in place:
  * `mumfordGroupLaw` narrowed from `MumfordRigidity.MumfordGroupLaw` to `GroupLaw.MumfordGroupLawDVR` in
    OpenResearchLeaves14..27; its three readers in TailZ23 (`qmFamilyGroupLaw_of_groupLaw` -> `qmFamilyGroupLaw_of_dvr`)
    and the one in TailZ34 (`y3Connected_of_leaves` -> `y3Connected_of_ab_gl ∘ qmFamilyGroupLaw_of_dvr`);
  * OpenResearchLeaves28 (TailZ45) and, on this base, also OpenResearchLeaves29 (TailZ46, leaf-fold33's autofold
    generation): field `mumfordGroupLawConn` -> `neronSchemeExtensionDedekind`; TailZ45's conversion supplies
    `mumfordGroupLaw := GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind`.
Textbook side: not in place. G's new OpenTextbookLeaves14 (on c1e4ed1b) becomes a new top module TailZ49 over
leaf-fold33b's TailZ48: `OpenTextbookLeaves16` = `OpenTextbookLeaves15` without `neronSchemeExtensionExists`, supplied
from `r.neronSchemeExtensionDedekind` by `neronSchemeExtensionExists_of_dedekind`; `sixContactMin_of_open42`.

Run from the repository root: python3 scratch/fold33-combine/gm_fold.py  (asserts every edit; writes TailZ49 and
patches Main.lean)."""
import re

H = "ZInQKernel/OneProof/H/"
OLD_T = "  mumfordGroupLaw : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw\n"
NEW_T = "  mumfordGroupLaw : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR\n"
NEW_T_NOTE = ("  -- fold33-combine (goodmodel-iso): narrowed to `MumfordGroupLawDVR` (GIT 6.14 over a DVR), which\n"
              "  -- `GoodModelIso.mumfordGroupLawDVR_of_dedekind` proves from `neronSchemeExtensionDedekind`\n")
DED = "_root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind"
DED_DOC = ("  /-- group-law-dvr + goodmodel-iso, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an "
           "affine Dedekind scheme (existence half; numbers UNVERIFIED). Gives GIT 6.14 over a DVR "
           "(GoodModelIso.mumfordGroupLawDVR_of_dedekind, with the comparison glue NeronGoodModelIso proved) and the "
           "textbook field neronSchemeExtensionExists (its case D = O_L, neronSchemeExtensionExists_of_dedekind). "
           "Replaces mumfordGroupLawConn. -/\n"
           "  neronSchemeExtensionDedekind : " + DED + "\n")
CONN = re.compile(r"  /-- dict-models, printed form: Mumford-Fogarty-Kirwan, GIT, Thm 6\.14 over a connected[^\n]*-/\n"
                  r"  mumfordGroupLawConn : _root_\.DictModels\.MumfordConn\.MumfordGroupLawConn\n")

edits = {}
def add(f, old, new, count=1):
    edits.setdefault(f, []).append((old, new, count))

for f in ["TailZ23", "TailZ25", "TailZ26", "TailZ27", "TailZ28", "TailZ29", "TailZ33", "TailZ34", "TailZ35",
          "TailZ36", "TailZ37", "TailZ38", "TailZ41", "TailZ44"]:
    add(f, OLD_T, NEW_T_NOTE + NEW_T)
add("TailZ23", "import ZInQKernel.OneProof.H.TailZ40\n",
    "import ZInQKernel.OneProof.H.TailZ40\nimport ZInQKernel.Contrib.OneProof.MumfordGroupLawRed\n")
add("TailZ23", "_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw",
    "_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw", 3)
add("TailZ34", "    (_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU)\n",
    "    (_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)\n"
    "      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))\n")
add("TailZ45", "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\n",
    "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\nimport ZInQKernel.Contrib.OneProof.NeronGoodModelIso\n")
add("TailZ45", CONN, DED_DOC)
add("TailZ45", "  mumfordGroupLaw := _root_.DictModels.MumfordConn.mumfordGroupLaw_of_conn n.mumfordGroupLawConn\n",
    "  mumfordGroupLaw := _root_.ZInQ.Contrib.GoodModelIso.mumfordGroupLawDVR_of_dedekind n.neronSchemeExtensionDedekind\n")
add("TailZ46", CONN, DED_DOC)
add("TailZ46", "  mumfordGroupLawConn := n.mumfordGroupLawConn\n",
    "  neronSchemeExtensionDedekind := n.neronSchemeExtensionDedekind\n")

for f, es in edits.items():
    p = H + f + ".lean"
    s = open(p).read()
    for old, new, count in es:
        if isinstance(old, re.Pattern):
            s, k = old.subn(new.replace("\\", "\\\\"), s)
        else:
            k = s.count(old)
            s = s.replace(old, new)
        if k != count:
            raise SystemExit(f"{f}: expected {count}, found {k}: {old if isinstance(old, str) else old.pattern}"[:300])
    open(p, "w").write(s)
    print(f, len(es), "edits")

# ---- TailZ49 (textbook side) ----
z48 = open(H + "TailZ48.lean").read()
m = re.search(r"structure OpenTextbookLeaves15 : Prop where\n((?:  .*\n)+)", z48)
fields = m.group(1)
assert "  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists\n" in fields
f16 = fields.replace("  neronSchemeExtensionExists : _root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists\n", "")
names = re.findall(r"^  (\w+) :", fields, re.M)
conv = "".join(
    f"  {n} := _root_.ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind h\n"
    if n == "neronSchemeExtensionExists" else f"  {n} := n.{n}\n" for n in names)
z49 = f'''import ZInQKernel.OneProof.H.TailZ48
import ZInQKernel.Contrib.OneProof.NeronGoodModelIso

/-! # OneProof H, fold33-combine (goodmodel-iso, fold G): `sixContactMin_of_open42` (written by hand after autofold's pattern)

goodmodel-iso's fold G replaces the research field `mumfordGroupLawConn` (GIT Thm 6.14 over a connected base) and the
textbook field `neronSchemeExtensionExists` (BLR 1.4 Thm 3, number-field case) by the one printed leaf
`neronSchemeExtensionDedekind` (BLR 1.4 Thm 3 over an affine Dedekind scheme, existence half). The research side is in
place (`mumfordGroupLaw` narrowed to `MumfordGroupLawDVR` in `OpenResearchLeaves14`-`27`; the field swapped in
`OpenResearchLeaves28`, `29`; `GoodModelIso.mumfordGroupLawDVR_of_dedekind`). The textbook side is this module:
`OpenTextbookLeaves16` is `OpenTextbookLeaves15` without `neronSchemeExtensionExists`, which
`GroupLawNeron.neronSchemeExtensionExists_of_dedekind` supplies from the research leaf. Net −1, no new glue. -/

namespace HDec

namespace HSyn

/-- `OpenTextbookLeaves15` without `neronSchemeExtensionExists` (fold33-combine, goodmodel-iso). -/
structure OpenTextbookLeaves16 : Prop where
{f16}
/-- `OpenTextbookLeaves15` from `OpenTextbookLeaves16` and BLR 1.4 Thm 3 over Dedekind schemes
(`neronSchemeExtensionExists_of_dedekind`). -/
theorem openTextbookLeaves15_of_OpenTextbookLeaves16 (n : OpenTextbookLeaves16)
    (h : {DED}) : OpenTextbookLeaves15 where
{conv}
/-- **G0 with only the open leaves** (fold33-combine; `mumfordGroupLawConn` and `neronSchemeExtensionExists` replaced
by `neronSchemeExtensionDedekind`). -/
theorem sixContactMin_of_open42 (r : OpenResearchLeaves29) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves20) : ZInQ.SixContactMin :=
  sixContactMin_of_open41 r (openTextbookLeaves15_of_OpenTextbookLeaves16 t r.neronSchemeExtensionDedekind) l

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open42
'''
open(H + "TailZ49.lean", "w").write(z49)

# ---- Main.lean ----
p = "ZInQKernel/OneProof/Main.lean"
s = open(p).read()
for old, new in [
    ("import ZInQKernel.OneProof.H.TailZ48\n", "import ZInQKernel.OneProof.H.TailZ49\n"),
    ("(t : HDec.HSyn.OpenTextbookLeaves15)", "(t : HDec.HSyn.OpenTextbookLeaves16)"),
    ("(HDec.HSyn.sixContactMin_of_open41 r t l)", "(HDec.HSyn.sixContactMin_of_open42 r t l)"),
]:
    if s.count(old) != 1:
        raise SystemExit("Main: " + old)
    s = s.replace(old, new)
open(p, "w").write(s)
print("TailZ49 written, Main patched")
