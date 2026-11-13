"""Apply qm-pin's edit (family clause in R1fpProps) to a file containing leaf-qm-fp's §8 text.
Usage: python3 apply_edit.py IN OUT"""
import sys, re
src = open(sys.argv[1]).read()
ed = open(sys.argv[3] if len(sys.argv) > 3 else 'scratch/qm-pin/QMLeavesEdited.lean').read()
orig = open('ZInQKernel/HDecomp/QM/Leaves.lean').read()
# the old def block and its replacement, taken from the kernel file and its edited copy
i0 = orig.index('/-- **R1fp, clause list**'); i1 = orig.index('/-- **R1hecke, clause list**')
j0 = ed.index('/-- **A family of level-3 QM abelian surfaces'); j1 = ed.index('/-- **R1hecke, clause list**')
old, new = orig[i0:i1], ed[j0:j1]
assert src.count(old) == 1, src.count(old)
s = src.replace(old, new)
n = s.count('obtain ⟨-, -, -, hnat⟩ := h1')
s = s.replace('obtain ⟨-, -, -, hnat⟩ := h1', 'obtain ⟨-, -, -, hnat, -⟩ := h1')
open(sys.argv[2], 'w').write(s)
print('patterns replaced:', n)
