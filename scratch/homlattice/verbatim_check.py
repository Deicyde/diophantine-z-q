"""Check that the MulRigidity block in HomLattice.lean is a verbatim copy of
scratch/alg-frob-red/src_Rigidity.lean lines 18-183. Run from the repository root."""
import sys
src = open('scratch/alg-frob-red/src_Rigidity.lean').read().split('\n')[17:183]
dst = open('scratch/homlattice/HomLattice.lean').read().split('\n')
i = dst.index('namespace MulRigidity')
ok = dst[i:i + len(src)] == src
print('MulRigidity block verbatim:', 'OK' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
