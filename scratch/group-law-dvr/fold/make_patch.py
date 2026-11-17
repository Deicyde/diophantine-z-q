"""Write the patched sources of fold F1 (narrowing) or F2 (Néron) under OUT/ (mirroring the tree).
usage: make_patch.py ROOT OUT {F1|F2}"""
import sys, os
root, out, variant = sys.argv[1], sys.argv[2], sys.argv[3]
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


for g in gens:
    rep(H + f"TailZ{g}.lean", OLD, NEW)
# TailZ23: import and three sites
rep(H + "TailZ23.lean", "import ZInQKernel.OneProof.H.TailZ40\n",
    "import ZInQKernel.OneProof.H.TailZ40\nimport ZInQKernel.Contrib.OneProof.MumfordGroupLawRed\n")
rep(H + "TailZ23.lean", "qmFamilyGroupLaw_of_groupLaw r.mumfordGroupLaw",
    "qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw", 3)
# TailZ34: one site
rep(H + "TailZ34.lean",
    "(_root_.DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU)",
    "(_root_.DCY3Used.y3Connected_of_ab_gl (_root_.LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr r.mumfordGroupLaw)\n"
    "      (_root_.DCY3Used.y3ConnectedAb_of_U r.shimuraMainThmIDeligneY3AbU))")
# TailZ45: the top bundle
p45 = H + "TailZ45.lean"
s = get(p45)
decl = "  mumfordGroupLawConn : _root_.DictModels.MumfordConn.MumfordGroupLawConn\n"
i = s.index(decl)
j = s.rfind("  /--", 0, i)
oldfield = s[j:i] + decl
if variant == "F1":
    newfield = ("  /-- group-law-dvr (narrowing of dict-models' mumfordGroupLawConn), printed form: Mumford-Fogarty-Kirwan, "
                "GIT, Thm 6.14 at S = Spec R, R a discrete valuation ring (numbers UNVERIFIED): the group law with identity "
                "e on a proper smooth family with a section all of whose field fibres are abelian varieties. The chain's "
                "use (QMFamilyGroupLaw) is proved from it (qmFamilyGroupLaw_of_dvr). Replaces mumfordGroupLawConn. -/\n"
                "  mumfordGroupLawDVR : _root_.ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR\n")
    use = "n.mumfordGroupLawDVR"
else:
    newfield = ("  /-- group-law-dvr, GLUE: a proper smooth model F over a DVR with abelian field fibres maps isomorphically "
                "onto every smooth separated model N under a morphism that is an isomorphism on generic fibres "
                "(van der Waerden purity, EGA IV 21.12.12, numbers UNVERIFIED). With BLR 1.4 Thm 3 over DVRs it gives "
                "GIT 6.14 over a DVR (mumfordGroupLawDVR_of_neron). Replaces mumfordGroupLawConn. -/\n"
                "  neronGoodModelIso : _root_.ZInQ.Contrib.GroupLawNeron.NeronGoodModelIso\n"
                "  /-- group-law-dvr, printed form: Bosch-Lutkebohmert-Raynaud, Neron models, 1.4 Thm 3 over an affine "
                "Dedekind scheme (existence half; numbers UNVERIFIED). Its case D = O_L is the textbook field "
                "neronSchemeExtensionExists (neronSchemeExtensionExists_of_dedekind). -/\n"
                "  neronSchemeExtensionDedekind : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind\n")
    use = ("_root_.ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron "
           "(_root_.ZInQ.Contrib.GroupLawNeron.dvr_of_dedekind n.neronSchemeExtensionDedekind) n.neronGoodModelIso")
rep(p45, oldfield, newfield)
rep(p45, "  mumfordGroupLaw := _root_.DictModels.MumfordConn.mumfordGroupLaw_of_conn n.mumfordGroupLawConn\n",
    "  mumfordGroupLaw := " + use + "\n")
if variant == "F2":
    rep(p45, "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\n",
        "import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn\nimport ZInQKernel.Contrib.OneProof.MumfordGroupLawNeron\n")
for p, s in files.items():
    q = os.path.join(out, p)
    os.makedirs(os.path.dirname(q), exist_ok=True)
    open(q, 'w').write(s)
print(len(files), "files")
