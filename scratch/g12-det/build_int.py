# Integrate.lean = g0-mod-galois's ModGalois.lean (no #print) + the new parts of g12-det with the
# copied definitions removed (they are already in ModGalois.lean) + part_integrate.lean.
import os
d = os.path.dirname(os.path.abspath(__file__))
def rd(f): return open(os.path.join(d, f)).read()
def noprint(s): return '\n'.join(l for l in s.split('\n') if not l.startswith('#print'))
def between(s, a, b):
    i = s.index(a); j = s.index(b, i); return s[i:j]
out = [noprint(open(os.path.join(d, '../g0-mod-galois/ModGalois.lean')).read())]
wp = rd('part_wp.lean'); out.append(noprint(wp[wp.index('noncomputable section'):]))
dt = rd('DetTate.lean')
out.append("\nsection G12DetDetSec\nnoncomputable section\nnamespace G0Galois\nopen scoped Matrix\n\n"
           + between(dt, "/-! ## The named pieces -/", "end G0Galois\n\nend\n")
           + "end G0Galois\nend\nend G12DetDetSec\n")
out.append(noprint(rd('part_leaves.lean')))
rq = rd('ResQ.lean')
out.append("\nsection G12DetResQSec\nnoncomputable section\nnamespace G0Galois\n\n"
           + between(rq, "/-! ## Proof -/", "end G0Galois") + "end G0Galois\nend\nend G12DetResQSec\n")
pw = rd('part_weight.lean')
out.append("\nsection G12DetWeightSec\nnamespace G0Galois\nopen PkgI4 (GaloisRep GaloisChar)\n\n"
           + between(pw, "/-! ### Named pieces -/", "end G0Galois") + "end G0Galois\nend G12DetWeightSec\n")
pt = rd('part_twist.lean')
out.append("\nsection G12DetTwistSec\nnoncomputable section\nnamespace G0Galois\nopen PkgI4 (GaloisRep GaloisChar)\n\n"
           + between(pt, "/-! ### `TwistExists` -/", "end G0Galois") + "end G0Galois\nend\nend G12DetTwistSec\n")
for f in ['part_htconj.lean', 'part_htextend.lean', 'part_final.lean']:
    out.append(noprint(rd(f)))
out.append(rd('part_integrate.lean'))
open(os.path.join(d, 'Integrate.lean'), 'w').write('\n'.join(out))
