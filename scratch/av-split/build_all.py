#!/usr/bin/env python3
"""Concatenate the av-split component files into AvSplitAll.lean (run from scratch/av-split)."""
FINAL = open('final_part.lean.part').read()


def body(fn):
    lines = open(fn).read().split('\n')
    return '\n'.join(l for l in lines if not l.startswith('import ') and not l.startswith('#print'))


imports = set()
for fn in ['HomLatticeAN3.lean', 'T5Isog.lean', 'T35.lean', 'T35AN3.lean', 'T4.lean']:
    for l in open(fn).read().split('\n'):
        if l.startswith('import '):
            imports.add(l)
t35an3 = body('T35AN3.lean')
a = t35an3.index("/-- (Verbatim copy from `T5Isog.lean`.)")
b = t35an3.index("open PkgI3\nopen ZInQ.LeafPush2 (CPts IsUniformization)")
t35an3 = t35an3[:a] + t35an3[b:]
a = t35an3.index("/-- (Verbatim copy from `T35.lean`.)")
b = t35an3.index("namespace AN3")
t35an3 = t35an3[:a] + t35an3[b:]
hdr = open('header_part.lean.part').read()
out = '\n'.join(sorted(imports)) + '\n\n' + hdr
for part in [body('HomLatticeAN3.lean'), body('T5Isog.lean'), body('T35.lean'), t35an3,
             body('T4.lean')]:
    out += '\n' + part + '\n'
out += FINAL
open('AvSplitAll.lean', 'w').write(out)
print(len(out.split('\n')), 'lines')
