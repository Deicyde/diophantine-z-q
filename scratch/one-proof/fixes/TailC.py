"""Manual fixes for TailC.lean (op-dedupe)."""
F = 'ZInQKernel/OneProof/H/TailC.lean'
s = open(F).read()
def rep(old, new, count=1):
    global s
    assert s.count(old) == count, (old, s.count(old))
    s = s.replace(old, new)
# KEPT `HDec.LeafQM.AV.QML3.goodReduction` vs the kernel's (aliased through `QML3`): name the HDec one
rep('  exact QML3.goodReduction (P := PK) hNOS', '  exact LeafQM.AV.QML3.goodReduction (P := PK) hNOS')
open(F, 'w').write(s)
print('TailC fixes applied')
