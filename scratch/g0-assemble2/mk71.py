# part 71 = g12-det's new parts exactly as its build_int.py appends them to g0-mod-galois (minus the
# ResQ section, proved in g0-assemble as G0AssembleMod.resQFiniteIndex, and part_integrate.lean)
import os
d = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../g12-det')
def rd(f): return open(os.path.join(d, f)).read()
def noprint(s): return '\n'.join(l for l in s.split('\n') if not l.startswith('#print'))
def between(s, a, b):
    i = s.index(a); j = s.index(b, i); return s[i:j]
out = ["/-! ## g0-assemble2: g12-det (its new parts, assembled as in scratch/g12-det/build_int.py, minus ResQ and part_integrate) -/"]
wp = rd('part_wp.lean'); out.append(noprint(wp[wp.index('noncomputable section'):]))
dt = rd('DetTate.lean')
out.append("\nsection G12DetDetSec\nnoncomputable section\nnamespace G0Galois\nopen scoped Matrix\n\n"
           + between(dt, "/-! ## The named pieces -/", "end G0Galois\n\nend\n")
           + "end G0Galois\nend\nend G12DetDetSec\n")
out.append(noprint(rd('part_leaves.lean')))
pw = rd('part_weight.lean')
out.append("\nsection G12DetWeightSec\nnamespace G0Galois\nopen PkgI4 (GaloisRep GaloisChar)\n\n"
           + between(pw, "/-! ### Named pieces -/", "end G0Galois") + "end G0Galois\nend G12DetWeightSec\n")
pt = rd('part_twist.lean')
out.append("\nsection G12DetTwistSec\nnoncomputable section\nnamespace G0Galois\nopen PkgI4 (GaloisRep GaloisChar)\n\n"
           + between(pt, "/-! ### `TwistExists` -/", "end G0Galois") + "end G0Galois\nend\nend G12DetTwistSec\n")
for f in ['part_htconj.lean', 'part_htextend.lean', 'part_final.lean']:
    out.append(noprint(rd(f)))
open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'parts/a35_g12det.lean'), 'w').write('\n'.join(out))
