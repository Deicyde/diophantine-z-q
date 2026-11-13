"""hodge-bc2: check that the Props proved and the blocks copied into the assembled checks appear
verbatim in their owner files. Run from the repository root:
python3 scratch/hodge-bc2/verbatim_check.py"""
import re, sys
fin = open('scratch/height-bc/Final.lean').read()
ok = True
def blk(src, name):
    m = re.search(r"def " + name + r"\b.*?(?=\n\n)", src, re.S)
    return m.group(0) if m else None
def check(target_file, names, blocks):
    global ok
    t = open(target_file).read()
    for n in names:
        b = blk(fin, n)
        r = b is not None and b in t
        ok &= r
        print(f"{target_file}: def {n} verbatim from scratch/height-bc/Final.lean: {r}")
    for (label, b) in blocks:
        r = b in t
        ok &= r
        print(f"{target_file}: block {label} verbatim: {r}")
cbc = open('scratch/infra-stalks/CotangentBaseChange.lean').read()
cbc = cbc[cbc.index('universe u'):]
bcp = '\n'.join(l for l in open('scratch/infra-stalks/bc_proof.lean.part').read().split('\n')
                if not l.startswith('#print'))
fl = fin.split('\n')
check('scratch/hodge-bc2/HodgeBCInjective.lean', ['HodgeBCInjective', 'CotangentSpanBC'],
      [('infra-stalks CotangentBaseChange.lean body', cbc), ('infra-stalks bc_proof.lean.part', bcp),
       ('Final.lean 590-856', '\n'.join(fl[589:856]))])
check('scratch/hodge-bc2/OmegaBC.lean', ['HodgeBCInjective', 'CotangentSpanBC', 'OmegaBaseChange'],
      [('infra-stalks CotangentBaseChange.lean body', cbc), ('infra-stalks bc_proof.lean.part', bcp),
       ('Final.lean 590-856', '\n'.join(fl[589:856]))])
import os
for extra in sys.argv[1:]:
    exec(open(extra).read())
print("ALL OK" if ok else "MISMATCH")
