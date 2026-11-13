"""linked-frob: check that the flat file LinkedFrob.lean contains its sources verbatim.
Run from the repository root: python3 scratch/linked-frob/py/verbatim_check.py"""
import re, glob
flat = open('scratch/linked-frob/LinkedFrob.lean').read()
def block(path, start=0):
    return '\n'.join(open(path).read().split('\n')[start:])
leaves = open('scratch/linked-tate/Leaves.lean').read().split('\n')
print("Leaves.lean lines 4-end verbatim:", '\n'.join(leaves[3:]) in flat)
for p in sorted(glob.glob('scratch/linked-tate/parts/*.lean')):
    print("linked-tate", p.split('/')[-1], "verbatim:", open(p).read() in flat)
for p in ['scratch/frob-trace/part_bridge_src.lean', 'scratch/frob-trace/part_frob.lean',
          'scratch/alg-frob-red/part_red.lean', 'scratch/afr-absfrob/part_fext.lean'] + \
         ['scratch/frob-pieces/part_%s.lean' % f for f in ['good', 'neron', 'final', 'full']]:
    print(p, "verbatim:", open(p).read() in flat)
# the two files copied with one deletion each
rig = block('scratch/mul-rigidity/Rigidity.lean', 4)
i = rig.index('/-- **Textbook leaf (rigidity;'); j = rig.index('→ IsMonHom h\n', i) + len('→ IsMonHom h\n')
print("Rigidity.lean minus imports and `def RigidityHom`: verbatim:", (rig[:i] + rig[j:]) in flat)
print("  deleted `def RigidityHom` equals linked-tate part 40's:",
      rig[rig.index('def RigidityHom', i):j] in open('scratch/linked-tate/parts/40_fibresimple.lean').read())
af = block('scratch/afr-absfrob/AbsFrobDef.lean', 1)
i = af.index('/-- **`AbsFrob` (GLUE'); j = af.index('≫ g = g ≫ Fr\n', i) + len('≫ g = g ≫ Fr\n')
print("AbsFrobDef.lean minus import and `def AbsFrob`: verbatim:", (af[:i] + af[j:]) in flat)
print("  deleted `def AbsFrob` equals alg-frob-red part_red's:",
      af[af.index('def AbsFrob', i):j] in open('scratch/alg-frob-red/part_red.lean').read())
# the target Prop: verbatim from its owner
own = open('scratch/linked-tate/parts/97_linkeddata.lean').read()
m = re.search(r"def LinkedFrob : Prop :=.*?(?=\n\n)", own, re.S)
print("def UnramTate.LinkedFrob (owner: linked-tate part 97) verbatim in flat:", m.group(0) in flat,
      "; occurrences:", flat.count("def LinkedFrob : Prop :="))
# frob-trace's AlgFrobRed: one definition, from frob-trace's file
ft = open('scratch/frob-trace/part_frob.lean').read()
m = re.search(r"def AlgFrobRed : Prop :=.*?(?=\n\n)", ft, re.S)
print("def FrobTrace.AlgFrobRed verbatim:", m.group(0) in flat, "; occurrences:", flat.count("def AlgFrobRed : Prop :="))
