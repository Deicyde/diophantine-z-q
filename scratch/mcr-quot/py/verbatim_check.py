"""Check that MCRQuot.lean = MCRGlue.lean (verbatim) + the parts listed in build.sh, that the
four targets are defined once (in the prefix), and that the parts contain no sorry/axiom."""
import re, sys, pathlib
here = pathlib.Path(sys.argv[1])
build = (here / "build.sh").read_text()
parts = re.findall(r"(MCRQuot[0-9]+b?\.lean\.part)", build)
prefix = (here.parent / "mcr-glue" / "MCRGlue.lean").read_text()
whole = (here / "MCRQuot.lean").read_text()
expected = prefix + "".join((here / p).read_text() for p in parts)
ok = True
if whole != expected:
    print("MISMATCH: MCRQuot.lean is not prefix + parts"); ok = False
for name in ["FibreAutTame", "GenericQuotientP1", "CMSectionsDisjoint", "CoordinateFromSections",
             "ModelCoordinateResidue"]:
    n = len(re.findall(r"^def %s\b" % name, whole, re.M))
    m = len(re.findall(r"^def %s\b" % name, prefix, re.M))
    if n != 1 or m != 1:
        print("TARGET", name, "defined", n, "times (prefix:", m, ")"); ok = False
for p in parts:
    t = (here / p).read_text()
    if re.search(r"\bsorry\b", t) or re.search(r"^\s*axiom\b", t, re.M):
        print("sorry/axiom in", p); ok = False
print("parts:", len(parts))
print("ALL OK" if ok else "FAILED")
