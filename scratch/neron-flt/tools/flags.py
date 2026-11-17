"""[port] add Lean v4.35 backward-compatibility elaboration flags (as CloudW03NeronSurj's port does) to FILEs."""
import sys
FL = ("-- [port] Lean v4.35: backward-compatibility elaboration flags (as in CloudW03NeronSurj's port)\n"
      "set_option backward.isDefEq.respectTransparency false\nset_option backward.defeqAttrib.useBackward true\n")
for p in sys.argv[1:]:
    s = open(p, encoding='utf-8').read()
    if 'backward.defeqAttrib.useBackward true\n' in s and 'respectTransparency false\n' in s: continue
    s = s.replace("set_option autoImplicit false\n", "set_option autoImplicit false\n" + FL, 1)
    open(p, 'w', encoding='utf-8').write(s); print('flags', p.split('/')[-1])
