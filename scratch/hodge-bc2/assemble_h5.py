#!/usr/bin/env python3
"""Assemble scratch/hodge-bc2/IntegrationH5.lean (run from the repository root):
imports (Leaves, Mathlib); scratch/h5-glue/H5Final.lean VERBATIM after its import, cut before its
`#print` block (as height-bc's assemble.py); IntegrationBC.lean after its two import lines;
int_h5.lean.part (new)."""
d='scratch/hodge-bc2/'
h5=open('scratch/h5-glue/H5Final.lean').read()
h5=h5[:h5.index("end ZInQ.H5Glue\n\n#print axioms ZInQ.H5Glue.heightAntitone")] + "end ZInQ.H5Glue\n"
h5=h5.split('\n',1)[1]
ib=open(d+'IntegrationBC.lean').read()
assert ib.startswith('import ZInQKernel.HDecomp.Faltings.Leaves\nimport Mathlib\n')
ib=ib.split('\n',2)[2]
out='import ZInQKernel.HDecomp.Faltings.Leaves\nimport Mathlib\n'+h5+'\n'+ib+'\n'+open(d+'int_h5.lean.part').read()
open(d+'IntegrationH5.lean','w').write(out)
