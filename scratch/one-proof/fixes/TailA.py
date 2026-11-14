"""Manual fixes for TailA.lean (op-dedupe)."""
F = 'ZInQKernel/OneProof/H/TailA.lean'
s = open(F).read()
def rep(old, new, count=1):
    global s
    assert s.count(old) == count, (old, s.count(old))
    s = s.replace(old, new)
# dot notation on the kernel's `PkgI4.GaloisRep` for the HDec predicate `GaloisRep.HasHTWeightsAtSelf`
rep('r.HasHTWeightsAtSelf ℓ {0, -1}', 'PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) ℓ {0, -1}')
rep('r.HasHTWeightsAtSelf 5 {0, -1}', 'PkgI4.GaloisRep.HasHTWeightsAtSelf (ρ := r) 5 {0, -1}')
open(F, 'w').write(s)
print('TailA fixes applied')
