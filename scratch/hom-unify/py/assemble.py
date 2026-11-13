"""hom-unify assembly. Run from the repository root: python3 scratch/hom-unify/py/assemble.py

Generates (all from verbatim sources, with the exact removals listed and asserted below):
  scratch/hom-unify/parts/H10_conjtwist.lean  ConjTwist.lean lines 39-2005 (namespace G0Galois, §1-§16)
      minus the three declarations already in g0-mod-galois' part 70_galois (resQ, qEmbRing, resQ_spec;
      asserted identical there), wrapped in a section.
  scratch/hom-unify/parts/H11_g10new.lean     rv-gluepieces2 checks/c1_g10.lean (g10-odd's reduction for
      g0-assemble's `G10Glue`) minus the four declarations already in H10 (isComplexConj_mul_self,
      one_tmul_injective, baseChange_injective', ConjTwistNontrivial; asserted identical).
  scratch/hom-unify/olean/TailBase.lean        = scratch/linked-tate/olean/Tail.lean (verbatim)
  scratch/hom-unify/olean/HConj.lean           = import TailBase + H10 + H11
  scratch/hom-unify/olean/HBundle.lean         = import HConj + H20_bundle.lean (hand-written)
  scratch/hom-unify/HomUnifyFlat.lean          = scratch/linked-tate/LinkedTate.lean + H10 + H11 + H20
"""
import re, sys
R = 'scratch/hom-unify/'
ct = open('scratch/conj-twist/ConjTwist.lean').read().split('\n')
g70 = open('scratch/linked-tate/parts/70_galois.lean').read()
c1 = open('scratch/rv-gluepieces2/checks/c1_g10.lean').read()

def block(text, start_pat):
    """the declaration (with its docstring) starting at the docstring before `start_pat`, up to the
    next blank line"""
    i = text.index(start_pat)
    j = text.rfind('/--', 0, i)
    if j != -1 and text[j:i].count('\n\n') == 0 and '-/' in text[j:i]:
        i = j
    k = text.index('\n\n', i)
    return text[i:k + 1]

h10 = '\n'.join(ct[38:2005]) + '\n'   # lines 39-2005
assert h10.startswith('namespace G0Galois') and h10.rstrip().endswith('end G0Galois'), (h10[:30], h10[-30:])
for pat in ['def resQ (K', 'def qEmbRing (K', 'lemma resQ_spec (K']:
    b = block(h10, pat)
    assert b in g70, pat
    h10 = h10.replace(b, '-- (hom-unify: `%s` removed here; identical copy in part 70_galois)\n' % pat.split()[1], 1)
H10 = ('/-! ## hom-unify: conj-twist\'s `ConjTwist.lean` lines 39-2005 (§1-§16, namespace `G0Galois`),\n'
       'verbatim except `resQ`, `qEmbRing`, `resQ_spec`, which part 70_galois already declares\n'
       '(identical text). -/\n\nsection HomUnifyConjTwistSec\n\nnoncomputable section\n\n'
       + h10 + '\nend\n\nend HomUnifyConjTwistSec\n')

c1b = c1
for pat in ['theorem isComplexConj_mul_self', 'theorem one_tmul_injective', "theorem baseChange_injective'",
            'def ConjTwistNontrivial']:
    b = block(c1b, pat)
    assert b in h10, pat
    c1b = c1b.replace(b, '-- (hom-unify: `%s` removed here; identical copy in conj-twist\'s part above)\n'
                      % pat.split()[1], 1)
H11 = ('/-! ## hom-unify: rv-gluepieces2\'s `checks/c1_g10.lean` (g10-odd\'s reduction\n'
       '`ConjTwistNontrivial → G10Glue` for g0-assemble\'s `G10Glue`), verbatim except four declarations\n'
       'that conj-twist\'s part above already has (identical text). -/\n\n' + c1b + '\n')
open(R + 'parts/H10_conjtwist.lean', 'w').write(H10)
open(R + 'parts/H11_g10new.lean', 'w').write(H11)
H20 = open(R + 'parts/H20_bundle.lean').read()
open(R + 'olean/TailBase.lean', 'w').write(open('scratch/linked-tate/olean/Tail.lean').read())
open(R + 'olean/HConj.lean', 'w').write('import TailBase\n\n' + H10 + '\n' + H11)
open(R + 'olean/HBundle.lean', 'w').write('import HConj\n\n' + H20)
flat = open('scratch/linked-tate/LinkedTate.lean').read()
open(R + 'HomUnifyFlat.lean', 'w').write(flat + '\n' + H10 + '\n' + H11 + '\n' + H20)
print('ok', sum(1 for _ in open(R + 'HomUnifyFlat.lean')), 'lines in HomUnifyFlat.lean')
