"""pin-apply: build scratch/h-decomposition/Leaves.lean with qm-pin's full edit + comparison.
Usage (repo root): python3 scratch/pin-apply/apply_hdec.py IN(edited by apply_edit.py full) OUT"""
import sys
s = open(sys.argv[1]).read()
pin = open('scratch/qm-pin/QMPinKernelFull.lean').read().split('\n')
blk = '\n'.join(pin[628:938]) + '\n\n'           # lines 629-938: namespace Pin … end Pin
assert blk.startswith('namespace Pin') and blk.rstrip().endswith('end Pin')
a = '  r5count : R5fpCount\n\nend AV\n'
assert s.count(a) == 1
s = s.replace(a, '  r5count : R5fpCount\n\n' + blk + 'end AV\n')
g = open('scratch/pin-apply/g0split_add.lean').read()
b = '\nend G0Split\n'
assert s.count(b) == 1
s = s.replace(b, g + b)
h = open('scratch/pin-apply/hsyn_add.lean').read()
c = '\n/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/'
assert s.count(c) == 1
s = s.replace(c, h + c)
names = ['LeafQM.AV.Pin.' + n for n in 'r1fpPin_relabel_iff r1fpPin_aut r2fp_aut phi_part sameTripleMor_of_mobius pointwise_of_witness_mor cm_objects_of_R1R2fp'.split()]
names += ['HSyn.G0Split.' + n for n in 'fibreSimple_iff_at thetaPointOfFibre_iff_at modularConstituent_iff_at qmPieces_iff_w'.split()]
names += ['HSyn.gluePieces_of_pin', 'HSyn.gluePiecesPin_of', 'HSyn.sixContactMin_of_leaves_pin']
s = s.rstrip('\n') + '\n-- pin-apply: qm-pin comparison\n' + ''.join(f'#print axioms {n}\n' for n in names)
open(sys.argv[2], 'w').write(s)
print('ok')
