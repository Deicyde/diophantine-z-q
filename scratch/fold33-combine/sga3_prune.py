"""fold33-combine, field 1 (sga3-nbhd): prune the research field `sga3_VIB_3_10` / `sga3_VIB_3_10_Nbhd` in place
from OpenResearchLeaves14..29 and replace its readers by sga3-nbhd's leaf-free variants
(ZInQKernel/Contrib/OneProof/SGA3NbhdDVR.lean, SemistableNeronBaseChangeNoSGA3.lean).

sga3-nbhd's own fold (scratch/sga3-nbhd/fold/FOLD-SPEC.md) copied the research chain; on leaf-fold33b the homfree
reroute copies the textbook chain, and the two copies do not compose. The readers are the same five as in the spec,
replaced in place. TailZ23 cannot import SemistableNeronBaseChangeNoSGA3 (its import closure contains TailZ23 and
TailZ24), so `semistableNeronBaseChange` becomes a binder `hNBC` of `researchLeaves9_of_open14`, threaded through
`sixContactMin_of_open17` (TailZ23) and `sixContactMin_of_open18` (TailZ24) and supplied by `sixContactMin_of_open19`
(TailZ25), which imports the contribution (the pattern of theta-fold2's `hθ`).

Run from the repository root: python3 scratch/fold33-combine/sga3_prune.py  (asserts every edit)."""
import re, sys

H = "ZInQKernel/OneProof/H/"
DOC3 = ("  /-- c-to-printed, printed form: SGA 3 VI_B 3.10 (the identity component `G⁰` of a smooth group scheme is open;\n"
        "  number UNVERIFIED). With the next two and `geomConnOfRationalPoint` replaces `semistableNeronBaseChange`. -/\n")
FIELD3 = "  sga3_VIB_3_10 : _root_.CToPrinted.SGA3_VIB_3_10\n"
PASS3 = "  sga3_VIB_3_10 := n.sga3_VIB_3_10\n"
NBHD_DOC = re.compile(r"  /-- gt-sga3, narrowed: SGA 3 VI_B 3\.10 in neighbourhood form:[^\n]*-/\n"
                      r"  sga3_VIB_3_10_Nbhd : _root_\.SGA3IdComp\.SGA3_VIB_3_10_Nbhd\n")
NBHD_PASS = "  sga3_VIB_3_10_Nbhd := n.sga3_VIB_3_10_Nbhd\n"
NOTE = "  -- fold33-combine (sga3-nbhd): field `sga3_VIB_3_10` deleted (its readers no longer need SGA 3 VI_B 3.10)\n"
NOTEN = "  -- fold33-combine (sga3-nbhd): field `sga3_VIB_3_10_Nbhd` deleted (its readers no longer need SGA 3 VI_B 3.10)\n"

edits = {}  # file -> list of (old, new, count)
def add(f, old, new, count=1):
    edits.setdefault(f, []).append((old, new, count))

def add_import(f, after, imp):
    add(f, after + "\n", after + "\n" + imp + "\n")

# generations 14..26: the field `sga3_VIB_3_10` with its docstring, and the pass-through lines
for f in ["TailZ23", "TailZ25", "TailZ26", "TailZ27", "TailZ28", "TailZ29", "TailZ33", "TailZ34", "TailZ35",
          "TailZ36", "TailZ37", "TailZ38", "TailZ41"]:
    add(f, DOC3 + FIELD3, NOTE)
for f in ["TailZ25", "TailZ26", "TailZ27", "TailZ28", "TailZ29", "TailZ33", "TailZ34", "TailZ35", "TailZ36",
          "TailZ37", "TailZ38", "TailZ41"]:
    add(f, PASS3, "")

# reader 1 (TailZ23, researchLeaves9_of_open14): threaded binder hNBC
NBC = "_root_.ZInQ.HeightSplit.SemistableNeronBaseChange"
add("TailZ23",
    "    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists) :\n"
    "    OpenResearchLeaves9 where\n",
    "    (hSS : _root_.ZInQ.HeightSplit.SemistableReductionThm ∧ _root_.ZInQ.HeightSplit.SemistablePersists)\n"
    "    (hNBC : " + NBC + ") :\n"
    "    OpenResearchLeaves9 where\n")
add("TailZ23",
    "  semistableNeronBaseChange := _root_.CToPrinted.semistableNeronBaseChange_of_printed_full r.blr_1_2_4\n"
    "    r.sga3_VIB_3_10 r.sga7_IX_3_3 r.egaIV_8_10_5_openImm t.geomConnOfRationalPoint\n",
    "  semistableNeronBaseChange := hNBC\n")
add("TailZ23",
    "    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=\n"
    "  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l h6 hSS) t",
    "    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)\n"
    "    (hNBC : " + NBC + ") : ZInQ.SixContactMin :=\n"
    "  sixContactMin_of_open11 (researchLeaves9_of_open14 r t l h6 hSS hNBC) t")
add("TailZ24",
    "    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM) : ZInQ.SixContactMin :=\n"
    "  sixContactMin_of_open17 r t (addedLeaves12_of_open13 l) g hYu h6 hSS hY3 hθ\n",
    "    (hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)\n"
    "    (hNBC : " + NBC + ") : ZInQ.SixContactMin :=\n"
    "  sixContactMin_of_open17 r t (addedLeaves12_of_open13 l) g hYu h6 hSS hY3 hθ hNBC\n")
add("TailZ25",
    "  sixContactMin_of_open18 (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu h6 hSS hY3\n"
    "    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul\n",
    "  sixContactMin_of_open18 (openResearchLeaves14_of_OpenResearchLeaves15 r) t l g hYu h6 hSS hY3\n"
    "    HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul\n"
    "    (_root_.SGA3Nbhd.semistableNeronBaseChange_noSGA3 r.blr_1_2_4 r.sga7_IX_3_3 t.geomConnOfRationalPoint)\n")
add_import("TailZ25", "import ZInQKernel.Contrib.OneProof.ThetaDirect",
           "import ZInQKernel.Contrib.OneProof.SemistableNeronBaseChangeNoSGA3")
# reader 2 (TailZ33)
add("TailZ33",
    "  sga7_IX_3_3 := _root_.SGA7PersistsNF.sga7_IX_3_3_of_SH n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization n.sga3_VIB_3_10 t.geomConnOfRationalPoint\n",
    "  sga7_IX_3_3 := _root_.SGA3Nbhd.NF.sga7_IX_3_3_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint\n")
add_import("TailZ33", "import ZInQKernel.Contrib.OneProof.UnipotentForward", "import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR")
# reader 3 (TailZ41)
add("TailZ41",
    "  semistablePersistsSHcp := _root_.GapPersists.semistablePersistsSHcp_of_SH n.sga3_VIB_3_10 n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint\n",
    "  semistablePersistsSHcp := _root_.SGA3Nbhd.Persists.semistablePersistsSHcp_of_SH' n.sga7_IX_3_3_SH n.neronBaseChangeStrictHenselization t.geomConnOfRationalPoint\n")
add_import("TailZ41", "import ZInQKernel.Contrib.OneProof.PersistsDVR", "import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR")
# generation 27 (TailZ44): the leaf sga3_VIB_3_10_Nbhd and the conversion line (reader 4)
add("TailZ44", NBHD_DOC, NOTEN)
add("TailZ44",
    "  sga3_VIB_3_10 := _root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof\n", "")
add("TailZ44", "Fields added (new leaves): `sga3_VIB_3_10_Nbhd`. -/",
    "Fields added (new leaves): `sga3_VIB_3_10_Nbhd` (pruned again by fold33-combine: sga3-nbhd's readers need neither\n"
    "`sga3_VIB_3_10` nor `sga3_VIB_3_10_Nbhd`). -/")
# generation 28 (TailZ45): reader 5 and the pass-through
add("TailZ45", NBHD_DOC, NOTEN)
add("TailZ45",
    "  sga7_IX_3_3_SH := _root_.DictModels.SGA7Pre.sga7_IX_3_3_SH_of_pre n.sga7_IX_3_3_SHpre (_root_.SGA3IdComp.sga3_VIB_3_10_of_nbhd n.sga3_VIB_3_10_Nbhd _root_.geomConnOfRationalPoint_proof) _root_.geomConnOfRationalPoint_proof\n",
    "  sga7_IX_3_3_SH := _root_.SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre' n.sga7_IX_3_3_SHpre _root_.geomConnOfRationalPoint_proof\n")
add("TailZ45", NBHD_PASS, "")
add_import("TailZ45", "import ZInQKernel.Contrib.OneProof.SGA7IX33SHPre", "import ZInQKernel.Contrib.OneProof.SGA3NbhdDVR")
# generation 29 (TailZ46)
add("TailZ46", NBHD_DOC, NOTEN)
add("TailZ46", NBHD_PASS, "")

for f, es in edits.items():
    p = H + f + ".lean"
    s = open(p).read()
    for old, new, count in es:
        if isinstance(old, re.Pattern):
            s, k = old.subn(new, s)
        else:
            k = s.count(old)
            s = s.replace(old, new)
        if k != count:
            raise SystemExit(f"{f}: expected {count} match(es), found {k}: {old if isinstance(old, str) else old.pattern!r}"[:400])
    open(p, "w").write(s)
    print(f, len(es), "edits")

# docstring of `sga7_IX_3_3_SHpre` in OpenResearchLeaves28/29 (applied after the edits above, 11-16)
old = "With sga3_VIB_3_10 and geomConnOfRationalPoint (idComp_baseChange, SGA 3 VI_B 3.3 proved) replaces sga7_IX_3_3_SH. -/"
new = ("With geomConnOfRationalPoint replaces sga7_IX_3_3_SH (fold33-combine: by sga3-nbhd's "
       "SGA3Nbhd.Pre.sga7_IX_3_3_SH_of_pre', a pointwise SGA 3 VI_B 3.3 without SGA 3 VI_B 3.10). -/")
for f in ["TailZ45", "TailZ46"]:
    p = H + f + ".lean"
    s = open(p).read()
    if s.count(old) != 1:
        raise SystemExit(f + ": docstring")
    open(p, "w").write(s.replace(old, new))

# TailZ25 module docstring note (applied after the edits above, 11-16)
p = H + "TailZ25.lean"
s = open(p).read()
old = "`ZInQKernel.Contrib.OneProof.ThetaDirect` (whose imports reach TailZ24). Its signature is unchanged. -/\n"
new = (old[:-4] + "\n\nfold33-combine (sga3-nbhd): `sixContactMin_of_open19` also supplies `semistableNeronBaseChange` (`hNBC`, threaded from\n"
       "`researchLeaves9_of_open14` through `sixContactMin_of_open17`, `open18`) by sga3-nbhd's\n"
       "`SGA3Nbhd.semistableNeronBaseChange_noSGA3` from `blr_1_2_4`, `sga7_IX_3_3` and `geomConnOfRationalPoint`, without\n"
       "SGA 3 VI_B 3.10; the field `sga3_VIB_3_10` is pruned from `OpenResearchLeaves14` on. Its signature is unchanged. -/\n")
if s.count(old) != 1:
    raise SystemExit("TailZ25 docstring")
open(p, "w").write(s.replace(old, new))
