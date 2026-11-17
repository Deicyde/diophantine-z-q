"""[port] Lean v4.35 instance-search repairs for FLT files over presheaves of modules of CommRingCat:
the `instanceSearchTypes` backward flag (as in Mathlib's own Presheaf/Monoidal.lean) and a local CommRing instance on
`(T ⋙ forget₂ CommRingCat RingCat).obj X`.  usage: python3 -I patch_pm.py TAG FILE"""
import sys, re
tag, p = sys.argv[1], sys.argv[2]
s = open(p, encoding='utf-8').read()
opt = ('-- [port] Lean v4.35: instance-search transparency flag (see the adaptation note in '
       'Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal)\n'
       'set_option backward.isDefEq.respectTransparency.instanceSearchTypes false\n')
if 'instanceSearchTypes' not in s:
    m = re.search(r'^set_option autoImplicit false\n', s, re.M)
    i = m.end(); s = s[:i] + opt + s[i:]
inst = ('\n-- [port] Lean v4.35: instance search no longer sees through `(T ⋙ forget₂ CommRingCat RingCat).obj X`\n'
        'noncomputable def commRingCompForget₂Obj_port_%s {E : Type*} [CategoryTheory.Category E]\n'
        '    (T : CategoryTheory.Functor E CommRingCat) (X : E) :\n'
        '    CommRing ((CategoryTheory.Functor.comp T (CategoryTheory.forget₂ CommRingCat RingCat)).obj X) :=\n'
        '  inferInstanceAs (CommRing (T.obj X))\n\n'
        'attribute [local instance] commRingCompForget₂Obj_port_%s\n') % (tag, tag)
if 'commRingCompForget₂Obj_port' not in s:
    key = 'set_option backward.isDefEq.respectTransparency.instanceSearchTypes false\n'
    pos = s.index(key) + len(key)
    s = s[:pos] + inst + s[pos:]
open(p, 'w', encoding='utf-8').write(s); print('patched', p)
