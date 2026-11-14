#!/usr/bin/env python3
"""leaf-fold10: TailZ10 contains dimjac-glue's DimJacGlue.lean after its five import lines as one block, with only the
two `#print axioms` lines and the trailing `example` dropped (run from the repository root)."""
src = open('scratch/dimjac-glue/DimJacGlue.lean').read().split('\n')
assert all(l.startswith('import ') for l in src[:5]) and not src[5].startswith('import ')
body = [l for l in src[5:] if not l.startswith('#print axioms ModularSplit.DimJac.')
        and l != 'example : ZInQ.Contrib.CurvesG.DimJacobianEqGenus := ModularSplit.DimJac.dimJacobianEqGenus']
body = '\n'.join(body).rstrip() + '\n'
tz = open('ZInQKernel/OneProof/H/TailZ10.lean').read()
imports = [l for l in tz.split('\n') if l.startswith('import ')]
print('TailZ10 imports:', imports)
print('source imports present:', all(l in imports for l in src[:5]))
print('body is a suffix block of TailZ10:', tz.endswith(body))
dropped = [l for l in src[5:] if l.startswith('#print') or l.startswith('example')]
print('dropped lines:', dropped)
