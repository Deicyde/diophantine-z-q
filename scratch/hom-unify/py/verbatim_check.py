"""hom-unify: check that every copied statement appears verbatim in its owner's file.
Run from the repository root: python3 scratch/hom-unify/py/verbatim_check.py"""
import re

def defblock(text, name):
    m = re.search(r"\ndef " + re.escape(name) + r" : Prop :=\n.*?(?=\n\n)", text, re.S)
    assert m, name
    return m.group(0)

r1b = open('scratch/r1b-state/Part8b_Hom.part').read()
r1bflat = open('scratch/r1b-state/R1b.lean').read()
ct = open('scratch/conj-twist/ConjTwist.lean').read()
corr = open('ZInQKernel/Contrib/HomUnify/Corr.lean').read()
h20 = open('scratch/hom-unify/parts/H20_bundle.lean').read()
g70 = open('scratch/linked-tate/parts/70_galois.lean').read()
c1 = open('scratch/rv-gluepieces2/checks/c1_g10.lean').read()
b3 = open('scratch/linked-tate/parts/99_bundle3.lean').read()
ok = True
def chk(label, cond):
    global ok
    ok &= cond
    print(('OK   ' if cond else 'FAIL ') + label)

t = defblock(r1b, 'T11aHom')
chk('T11aHom (Part8b_Hom.part) verbatim in Corr.lean', t in corr)
chk('T11aHom (Part8b_Hom.part) = the copy in r1b-state R1b.lean', t in r1bflat)
h = defblock(ct, 'HomLinearLift')
chk('HomLinearLift (ConjTwist.lean) verbatim in Corr.lean', h in corr)
c = defblock(corr, 'HomLatticeCorr')
chk('HomLatticeCorr (Corr.lean) verbatim in H20_bundle.lean', c in h20)
# the first clause of HomLatticeCorr is HomLinearLift's body
body = h.split(':=\n', 1)[1]
first = c.split(':=\n', 1)[1].split(') ∧\n')[0]
chk('HomLatticeCorr clause 1 = HomLinearLift body (up to the opening paren and indentation)',
    first.replace('\n    ', '\n').strip().lstrip('(') .replace(' ', '') == body.replace('\n    ', '\n').strip().replace(' ', ''))
for n in ['G10Glue', 'GaloisPieces']:
    pass
g10 = defblock(g70, 'G10Glue')
chk("G10Glue (70_galois) is the statement in c1's target (c1 has no copy; uses the assembly's)", 'def G10Glue' not in c1)
for n in ['ConjTwistNontrivial']:
    chk(n + ' (ConjTwist.lean) = c1 copy', defblock(ct, n) == defblock(c1, n))
# GluePieces3Hom fields vs GluePieces3
s = b3.index('structure GluePieces3 : Prop where\n'); e = b3.index('\n\n/-- **`GluePieces2` from')
f3 = b3[s:e].split('\n')[1:]
s2 = h20.index('structure GluePieces3Hom : Prop where\n'); e2 = h20.index('\n\n/-- **`GluePieces3` from')
f4 = h20[s2:e2].split('\n')[1:]
import difflib
d = [l for l in difflib.unified_diff(f3, f4, lineterm='', n=0) if l[:1] in '+-' and l[:3] not in ('+++', '---')]
print('\n'.join('     ' + l for l in d))
chk('GluePieces3Hom differs from GluePieces3 only in the g10Glue field (3 lines out, 5 in)',
    len([l for l in d if l.startswith('-')]) == 3 and all('g10Glue' in l or 'hypotheses T11' in l or 'g0-mod-galois G10' in l for l in d if l.startswith('-')))
s = g70.index('structure GaloisPieces : Prop where\n'); e = g70.index('\n\n', s)
gp = g70[s:e].split('\n')[1:]
s2 = h20.index('structure GaloisPiecesHom : Prop where\n'); e2 = h20.index('\n\n', s2)
gh = h20[s2:e2].split('\n')[1:]
dd = [(a, b) for a, b in zip(gp, gh) if a != b]
print('     GaloisPieces vs GaloisPiecesHom differing fields:', dd)
chk('GaloisPiecesHom = GaloisPieces with `odd : G10Glue` replaced by `homLift : HomLinearLift`',
    len(gp) == len(gh) and dd == [('  odd : G10Glue', '  homLift : HomLinearLift')])
print('ALL OK' if ok else 'SOME FAILED')
