"""Manual fixes for TailH.lean (op-dedupe)."""
F = 'ZInQKernel/OneProof/H/TailH.lean'
s = open(F).read()
old = 'open ExteriorAlgebra\n\nattribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt\n'
assert s.count(old) == 1
# the copy `ZInQ.DefFaltings.AbVar` is gone (kernel alias of `PkgI3.AbVar`, whose fields are already instances)
s = s.replace(old, 'open ExteriorAlgebra\n\n-- op-dedupe: `attribute [instance] AbVar.grp ...` dropped: `AbVar` is the kernel alias of `PkgI3.AbVar`,\n-- whose fields are instances already.\n')
open(F, 'w').write(s)
print('TailH fixes applied')
