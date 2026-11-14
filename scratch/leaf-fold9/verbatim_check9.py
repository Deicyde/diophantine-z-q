"""leaf-fold9: TailZ6 contains scratch/modular-split/R15.lean after its two import lines, unchanged and as one block,
with only the `#print` lines dropped; TailZ5 contains Lemmas.lean.part (= test/R1recT.lean minus imports)."""
r15 = open('scratch/modular-split/R15.lean').read().split('\n')
body = '\n'.join(l for l in r15[2:] if not l.startswith('#print')).strip('\n')
z6 = open('ZInQKernel/OneProof/H/TailZ6.lean').read()
print('R15 body in TailZ6 (one block):', z6.count(body) == 1)
lem = open('scratch/leaf-fold9/Lemmas.lean.part').read().rstrip()
test = open('scratch/leaf-fold9/test/R1recT.lean').read()
z5 = open('ZInQKernel/OneProof/H/TailZ5.lean').read()
print('Lemmas part in TailZ5:', z5.count(lem) == 1, '; Lemmas part = test file minus imports:',
      lem in test and all(l.startswith('import') or not l.strip() for l in test.replace(lem, '').split('\n')))
