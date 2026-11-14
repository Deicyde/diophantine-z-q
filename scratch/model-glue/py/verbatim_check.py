#!/usr/bin/env python3
"""Mechanical checks for scratch/model-glue/ModelGlue6.lean (run from the repo root).
1. The file is `import ZInQKernel.Contrib.Mobius.Main` + scratch/vert-witness/VertWitness.lean
   (verbatim, whole file) + the part files, in order.
2. The target defs `ModelCoordinate`, `ModelComparison` occur exactly once, inside the
   verbatim prefix (so the theorems proved below have exactly the owner's types).
3. The copied smooth-fibre lemma body equals its source (branch wip/smooth-fibre)."""
import subprocess, sys
root = 'scratch/model-glue/'
full = open(root + 'ModelGlue6.lean').read()
vw = open('scratch/vert-witness/VertWitness.lean').read()
parts = [open(root + f).read() for f in
         ['ModelGlue.lean.part', 'ModelGlue2.lean.part', 'ModelGlue3.lean.part',
          'ModelGlue4.lean.part', 'ModelGlue5.lean.part', 'ModelGlue6.lean.part']]
expected = 'import ZInQKernel.Contrib.Mobius.Main\n' + vw + ''.join(parts)
ok = True
print('1. assembly = import + VertWitness.lean + parts:', full == expected); ok &= full == expected
for name in ['def ModelCoordinate : Prop', 'def ModelComparison : Prop']:
    n_full, n_vw = full.count(name), vw.count(name)
    r = n_full == 1 and n_vw == 1
    print('2.', name, 'occurrences (file, prefix):', n_full, n_vw, r); ok &= r
src = subprocess.run(['git', 'show', 'origin/wip/smooth-fibre:ZInQKernel/Contrib/SmoothFibre/Basic.lean'],
                     capture_output=True, text=True).stdout
def body(text, start):
    i = text.index(start); j = text.index('\n\n', i); return text[i:j]
a = body(src, 'theorem isReduced_of_etale_of_isDomain (P S')
b = body(parts[4 - 1], "theorem isReduced_of_etale_of_isDomain' (P S")
b2 = b.replace("isReduced_of_etale_of_isDomain'", 'isReduced_of_etale_of_isDomain') \
      .replace('IsReduced (TensorProduct P K S) := Algebra.FormallyUnramified.isReduced_of_field K _',
               'IsReduced (K ⊗[P] S) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[P] S)') \
      .replace('(f : S →+* TensorProduct P K S)', '(f : S →+* K ⊗[P] S)')
r = a == b2
print('3. isReduced_of_etale_of_isDomain copy equals source (modulo name and ⊗ notation):', r); ok &= r
a = body(src, 'theorem smoothFibreReduced : SmoothFibreReduced')
b = body(parts[5], "theorem smoothFibreReduced' : SmoothFibreReduced")
b2 = b.replace("smoothFibreReduced'", 'smoothFibreReduced').replace(
    'isReduced_of_smooth_of_isDomain (R ⧸ m) _', 'isReduced_of_smooth_of_field (R ⧸ m) _')
r = a == b2
print("3'. smoothFibreReduced copy equals source (modulo name and the field lemma):", r); ok &= r
print('ALL OK' if ok else 'FAILED'); sys.exit(0 if ok else 1)
