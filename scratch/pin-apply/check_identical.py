"""pin-apply: the clause block and the Pin block are textually identical in the kernel and in
scratch/h-decomposition/Leaves.lean. Run from the repository root."""
k = open('ZInQKernel/HDecomp/QM/Leaves.lean').read()
s = open('scratch/h-decomposition/Leaves.lean').read()
a, b = '/-- **A family of level-3 QM abelian surfaces', '/-- **R1hecke, clause list**'
kb = k[k.index(a):k.index(b)]
p = open('ZInQKernel/HDecomp/QM/Pin.lean').read()
pb = p[p.index('namespace Pin'):p.index('end Pin')]
print('clause block (QMFamily … R1fpProps) identical:', s.count(kb) == 1)
print('Pin block identical:', s.count(pb) == 1)
