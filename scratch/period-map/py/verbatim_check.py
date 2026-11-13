"""period-map: check that the statements copied into light_base.lean appear verbatim in their sources.
Run from the repository root: python3 scratch/period-map/py/verbatim_check.py"""
import re
lb = open('scratch/period-map/light_base.lean').read()
fqm = open('scratch/fibre-qm-period/part_fqm.lean').read()
tp = open('scratch/g0-thetapoint/ThetaPoint.lean').read()
pkg = '\n'.join(open('scratch/g0-thetapoint/ThetaPoint.lean').read().split('\n')[76:289])
print("PkgI1 block (ThetaPoint lines 77-289) verbatim in light_base:", pkg in lb)
for name in ["QMHauptmodulFn", "QMDenZeroCM3", "IsHolP1At", "GammaStarFibresCM", "IsGammaStarHauptmodul", "HauptmodulUnique"]:
    m = re.search(r"def " + name + r"\b.*?(?=\n\n)", fqm, re.S)
    print(name, "verbatim:", m is not None and m.group(0) in lb)
