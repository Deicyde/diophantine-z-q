# Generate ZInQKernel/HDecomp/Faltings/H5BaseChange.lean (run from the worktree root):
# h5-neron's part F (scratch/h5-neron/BaseChange.lean at b7c1dc21, saved as
# scratch/hdec-adopt5a/src/BaseChange.lean) without its unfinished comment block, with its two
# copied definitions replaced by the import of `Faltings.H5Neron` (identical text and binders), and
# with the new assembly of task hdec-adopt5a (scratch/hdec-adopt5a/H4bAssembly.part), which proves
# `groupModelBaseChangeExists`.
import subprocess
S = open('scratch/hdec-adopt5a/src/BaseChange.lean', encoding='utf-8').read()
head = S.split('/-! ### Unfinished')[0]
a = head.index('/-- (copied) -/\ndef IsBaseChangeOf')
b = head.index('/-- `(f ≫ g)^* G → f^* g^* G`')
cut = head[a:b]
H = open('ZInQKernel/HDecomp/Faltings/H5Neron.lean', encoding='utf-8').read()
for blk in cut.split('/-- (copied) -/\n')[1:]:
    assert blk.strip() in H, blk[:60]          # verbatim in the imported module
head = head[:a] + head[b:]
head = head.replace('import ZInQKernel.HDecomp.Faltings.Leaves\n',
                    'import ZInQKernel.HDecomp.Faltings.H5Neron\n')
old = '`IsBaseChangeOf` and `GroupModelBaseChangeExists` are copied from `Reduction.lean`. -/'
new = ('`IsBaseChangeOf` and `GroupModelBaseChangeExists` (copied in the draft from\n'
       '`Reduction.lean`) are imported from `ZInQKernel.HDecomp.Faltings.H5Neron`. -/')
assert old in head
head = head.replace(old, new)
t = 'part F: toward the glue `GroupModelBaseChangeExists` (partial)'
assert t in head
head = head.replace(t, 'part F: the glue `GroupModelBaseChangeExists` (H4b)')
DOC = ('\n/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt5a from\n'
       '`scratch/h5-neron/BaseChange.lean` (branch `wip/h5-neron` at b7c1dc21; its compiled part),\n'
       'with the assembly that proves glue H4b added by hdec-adopt5a.\n'
       'The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/\n')
i = head.index('\n') + 1
head = head[:i] + DOC + head[i:]
asm = open('scratch/hdec-adopt5a/H4bAssembly.part', encoding='utf-8').read()
out = head.rstrip('\n') + '\n\n' + asm
P = 'ZInQKernel/HDecomp/Faltings/H5BaseChange.lean'
open(P, 'w', encoding='utf-8').write(out)
subprocess.run(['python3', '-I', 'scratch/hdec-adopt/wrap.py', P])
print(P)
