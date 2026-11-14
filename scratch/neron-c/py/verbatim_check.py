"""neron-c: check that the kernel declarations proved/reduced here appear verbatim (with every
declaration their statements use) in leaf-fold3's flat file and in scratch/neron-c/Check.lean.
Run from the repository root: python3 scratch/neron-c/py/verbatim_check.py"""
import re, sys
def block(path, start_line_pat, nth=0):
    src = open(path).read()
    ms = [m for m in re.finditer(r"^(?:/--(?:(?!-/).)*?-/\n)?" + start_line_pat + r".*?(?=\n\n|\nend |\ntheorem |\nsection )", src, re.S | re.M)]
    return ms[nth].group(0) if len(ms) > nth else None
obj = 'ZInQKernel/HDecomp/Objects.lean'
h5 = 'ZInQKernel/HDecomp/Faltings/H5Neron.lean'
mod = 'ZInQKernel/HDecomp/Faltings/Models.lean'
hei = 'ZInQKernel/HDecomp/Faltings/Height.lean'
items = [
  ("T3  PkgI2.NeronMappingAbelianScheme", obj, r"def NeronMappingAbelianScheme : Prop", 0),
  ("dep PkgI2.IsAbelianScheme", obj, r"class IsAbelianScheme", 0),
  ("T41 ZInQ.H5Neron.NeronModelExists", h5, r"def NeronModelExists : Prop", 0),
  ("dep DefFaltings.GroupModel", mod, r"structure GroupModel", 0),
  ("dep DefFaltings.genericFibre", mod, r"noncomputable def genericFibre", 0),
  ("dep DefFaltings.GroupModel.IsNeronModel", hei, r"def GroupModel.IsNeronModel", 0),
  ("dep PkgI3.AbVar", obj, r"structure AbVar", 0),
]
lf3 = open('scratch/leaf-fold3/Leaves3.lean').read()
chk = open('scratch/neron-c/Check.lean').read()
ok = True
for name, path, pat, n in items:
    b = block(path, pat, n)
    if b is None:
        print(name, ": NOT FOUND in", path); ok = False; continue
    a1 = b in lf3
    a2 = b in chk if name.startswith(("T3", "T41")) else None
    print(f"{name}: {len(b.splitlines())} lines; verbatim in leaf-fold3 Leaves3.lean: {a1}" +
          ("" if a2 is None else f"; verbatim in Check.lean: {a2}"))
    ok = ok and a1 and (a2 is not False)
print("ALL OK" if ok else "MISMATCH")
sys.exit(0 if ok else 1)
