#!/usr/bin/env python3
"""Assemble scratch/hodge-bc2/IntegrationBC.lean (run from the repository root):
  * scratch/infra-stalks/HeightBCGlue.lean, VERBATIM (`#print` lines dropped): imports, StalkPullback
    body, local_structure part, all of scratch/height-bc/Final.lean after its import, infra-stalks'
    proofs of CotangentSpanBC / UniformizationLiftAnalytic and `modelHeightBaseChange_of_two`;
  * scratch/infra-stalks/stalk_tensor.lean.part and cot_bc.lean.part, VERBATIM (`#print` dropped);
  * scratch/hodge-bc2/ExtFrac.lean body, hbc_proof.lean.part, omega_proof.lean.part (new);
  * scratch/height-bc/PartE.lean.part (alias `ZInQ.DefFaltings.AbVar`, VERBATIM) around
    scratch/g0-stablebc/Main.part (VERBATIM, `#print` dropped), as in height-bc's G0WithBC.lean;
  * int_final.lean.part (new): H4a, HodgeLineBaseChange, StableHeightBaseChange as theorems."""
d='scratch/hodge-bc2/'
def noprint(s): return '\n'.join(l for l in s.split('\n') if not l.startswith('#print'))
hg=noprint(open('scratch/infra-stalks/HeightBCGlue.lean').read())
st=noprint(open('scratch/infra-stalks/stalk_tensor.lean.part').read())
cb=noprint(open('scratch/infra-stalks/cot_bc.lean.part').read())
ef=open(d+'ExtFrac.lean').read(); ef=ef[ef.index('/-! # Exterior'):]
hbc=noprint(open(d+'hbc_proof.lean.part').read())
om=noprint(open(d+'omega_proof.lean.part').read())
pe=open('scratch/height-bc/PartE.lean.part').read().split('%%MAINPART%%')
mp=noprint(open('scratch/g0-stablebc/Main.part').read())
fin=open(d+'int_final.lean.part').read()
out='\n\n'.join([hg,st,cb,ef,hbc,om,pe[0]+mp+noprint(pe[1]),fin])
open(d+'IntegrationBC.lean','w').write(out)
