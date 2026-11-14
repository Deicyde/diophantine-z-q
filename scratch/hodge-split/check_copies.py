"""Check that the definitions shared by HodgeSplit.lean and Companion.lean have the same text
after writing `ZInQ.Contrib.G9.PkgI4.` for `PkgI4.` and dropping docstrings/whitespace.
Run from the repository root: python3 scratch/hodge-split/check_copies.py"""
import re, sys
main = open('scratch/hodge-split/HodgeSplit.lean').read()
comp = open('scratch/hodge-split/Companion.lean').read()
NAMES = ['HTConj', 'EigenformHTNew', 'IsConj', 'AttachedConj', 'DetFromFrobenius', 'toRingEquivQ', 'cycQ', 'R14Det', 'R14DetConcl',
         'R14DetWt1', 'R14DetWtGe2', 'DSThm965', 'DSThm966', 'Semisimplification2', 'ArtinTransport']
def body(src, name):
    m = re.search(r'\ndef ' + re.escape(name) + r'\b(.*?)(?=\n\n|\n/--|\nend )', src, re.S)
    if not m:
        return None
    t = m.group(1)
    t = t.replace('ZInQ.Contrib.G9.PkgI4.', 'PkgI4.')
    t = re.sub(r'\bPkgI4\.(GaloisRep|GaloisChar)\b', r'\1', t)
    return ' '.join(t.split())
bad = 0
for n in NAMES:
    a, b = body(main, n), body(comp, n)
    status = 'same' if a == b and a is not None else 'DIFFERENT'
    if status != 'same':
        bad += 1
    print(f'{n:22s} {status}')
sys.exit(1 if bad else 0)
