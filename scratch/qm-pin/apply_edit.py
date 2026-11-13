"""Apply qm-pin's edit of leaf-qm-fp's R1fpProps to a file containing the original §8 text.
Usage: python3 apply_edit.py IN OUT [min|full]
  min : family clause R1famProps (5th conjunct)        -- source of the new text: QMLeavesEdited.lean
  full: R1famProps and R1univProps (5th, 6th conjuncts) -- source: QMLeavesFull.lean
Run from the repository root."""
import sys
mode = sys.argv[3] if len(sys.argv) > 3 else 'full'
src = open(sys.argv[1]).read()
ed = open('scratch/qm-pin/QMLeavesEdited.lean' if mode == 'min' else 'scratch/qm-pin/QMLeavesFull.lean').read()
orig = open('ZInQKernel/HDecomp/QM/Leaves.lean').read()   # pre-edit kernel file (unchanged by qm-pin)
i0 = orig.index('/-- **R1fp, clause list**'); i1 = orig.index('/-- **R1hecke, clause list**')
j0 = ed.index('/-- **A family of level-3 QM abelian surfaces'); j1 = ed.index('/-- **R1hecke, clause list**')
old, new = orig[i0:i1], ed[j0:j1]
assert src.count(old) == 1, src.count(old)
s = src.replace(old, new)
pat = 'obtain ⟨-, -, -, hnat⟩ := h1'
rep = 'obtain ⟨-, -, -, hnat, -⟩ := h1' if mode == 'min' else 'obtain ⟨-, -, -, hnat, -, -⟩ := h1'
n = s.count(pat)
s = s.replace(pat, rep)
open(sys.argv[2], 'w').write(s)
print('mode', mode, 'patterns replaced:', n)
