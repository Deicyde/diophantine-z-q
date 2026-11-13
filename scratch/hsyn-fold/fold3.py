p='scratch/h-decomposition/Leaves.lean'; L=open(p).read()
O=open('scratch/obj-bridge/Objects.lean').read().split('\n')
assert O[1128].startswith('/-! # §C') and O[1794].startswith('end ObjBridge')
blk='\n'.join(O[1128:1795])
a='\nsection GlueC10Sec\n'; assert L.count(a)==1
L=L.replace(a, '\nsection ObjBridgeSec\n/-! ### Copied from `scratch/obj-bridge/Objects.lean` §C-§F (lines 1129-1795; its copies of pkg-I3 and pkg-I2, §A-§B, dropped in favour of this file\'s `PkgI3`, `PkgI2`; hsyn-fold). -/\n\nnoncomputable section\n\n'+blk+'\n\nend\n\nend ObjBridgeSec\n'+a)
pr='\n'.join(x for x in O[1797:1810] if x.startswith('#print'))
L=L.rstrip('\n')+'\n-- hsyn-fold: obj-bridge\n'+pr+'\n'
open(p,'w').write(L); print('ok')
