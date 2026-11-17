"""theta-direct: the manual fold, as a patch (NOT applied to the worktree; the fold stays with the integration lead).

Run from the repository root: `python3 scratch/theta-direct/fold/make_fold.py`. It copies the base's
ZInQKernel/OneProof/H/*.lean, ZInQKernel/OneProof/Main.lean and ZInQKernel/Contrib/OneProof/ThetaDirect/{UseForm,Split}.lean
to /tmp/td_fold_out/{a,b}, edits the copy b, and writes scratch/theta-direct/fold/fold.patch (`diff -ruN a b`) and
fold-deleted.txt. The edits:
1. theta-fold's plumb.py (origin/wip/theta-fold 8e3dbdea, copied as plumb_theta_fold.py), UNCHANGED: moves theta-split's
   `ThetaRatiosAtQM`, `Jmap_ne_zero`, `thetaPointOfFibre_of_qm_atQM` into TailK (namespace
   `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`), gives `gluePieces_of_open4` the binder
   `hθ : PkgI1.QMHauptmodul → ThetaSplit.ThetaRatiosAtQM` (thetaPoint := thetaPointOfFibre_of_qm_atQM … (hθ l.qmHauptmodul)),
   threads `hθ` through `sixContactMin_of_open4`, `_open6` … `_open28`. The moved block's header comment is reworded.
2. `sixContactMin_of_open29` (TailZ35, the top on this base) also takes and passes `hθ`.
3. theta-fold's prune_edit.py (copied as prune_edit_theta_fold.py) with its TailZ41 rows dropped: deletes the fields
   `OpenAddedLeaves4/6/7/8/9/12/13/14/15/16/17.thetaRatiosAlgebraic`, the assignments into them, the element in TailO's
   `openAddedLeaves4_of_Q5`, and the dead readers `addedLeaves5_of_open6` (TailO), `addedLeaves11_of_open12`,
   `sixContactMin_of_open16` (TailZ22).
4. Main.lean: `import ZInQKernel.Contrib.OneProof.ThetaDirect`; frozenTarget's call
   `sixContactMin_of_open29 r t l g` becomes `sixContactMin_of_open29 r t l g HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul`.
   No new hypothesis: `thetaRatiosAtQM_of_qmHauptmodul` is a theorem (`fun _ => thetaRatiosAtQM_proof`).
5. ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean (hX-fold's alternative tops `frozenTarget_of_used/_eta/_theta`,
   l.334, l.363, l.387, found by the fold-check build): the same extra argument, and
   `import ZInQKernel.Contrib.OneProof.ThetaDirect`.
6. Contributor modules: delete ThetaDirect/UseForm.lean (its block is now in TailK); Split.lean imports
   `ZInQKernel.OneProof.H.TailZ19` in place of `…ThetaDirect.UseForm`.
"""
import os, re, shutil, subprocess, sys
ROOT = os.getcwd()
OUT = '/tmp/td_fold_out'
shutil.rmtree(OUT, ignore_errors=True)
for side in ('a', 'b'):
    os.makedirs(f'{OUT}/{side}/ZInQKernel/OneProof/H')
    for f in os.listdir('ZInQKernel/OneProof/H'):
        if f.endswith('.lean'):
            shutil.copy(f'ZInQKernel/OneProof/H/{f}', f'{OUT}/{side}/ZInQKernel/OneProof/H/{f}')
    shutil.copy('ZInQKernel/OneProof/Main.lean', f'{OUT}/{side}/ZInQKernel/OneProof/Main.lean')
    os.makedirs(f'{OUT}/{side}/ZInQKernel/Contrib/OneProof/ThetaDirect')
    shutil.copy('ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean', f'{OUT}/{side}/ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean')
    for f in ('UseForm.lean', 'Split.lean'):
        shutil.copy(f'ZInQKernel/Contrib/OneProof/ThetaDirect/{f}', f'{OUT}/{side}/ZInQKernel/Contrib/OneProof/ThetaDirect/{f}')
B = f'{OUT}/b'
# plumb.py reads theta-split's block from linyang-printed's file (the same text as ThetaDirect/UseForm.lean)
os.makedirs(f'{B}/scratch/theta-fold/src')
src = subprocess.run(['git', 'show', 'origin/wip/linyang-printed:scratch/linyang-printed/LinYangPrintedFull.lean'],
                     capture_output=True, text=True, check=True).stdout
open(f'{B}/scratch/theta-fold/src/LinYangPrintedFull.lean', 'w').write(src)
os.chdir(B)
exec(open(f'{ROOT}/scratch/theta-direct/fold/plumb_theta_fold.py').read(), {'__name__': '__main__'})
shutil.rmtree(f'{B}/scratch')
H = 'ZInQKernel/OneProof/H/'
def sub1(f, old, new):
    s = open(f).read(); assert s.count(old) == 1, (f, old[:70], s.count(old)); open(f, 'w').write(s.replace(old, new))
sub1(H + 'TailK.lean', """linyang-printed prove it from the printed leaves `IgusaThetaExpressions` and `LinYangEx29All` (with `QMHauptmodul`;
`ZInQKernel/Contrib/OneProof/LinYangPrinted.lean`), which replace the universal field `thetaRatiosAlgebraic`. -/""",
"""theta-direct proves it with no hypotheses (`HDec.ThetaDirect.thetaRatiosAtQM_proof`,
`ZInQKernel/Contrib/OneProof/ThetaDirect.lean`), so the universal field `thetaRatiosAlgebraic` is dropped. -/""")
sub1(H + 'TailK.lean', '/-! ### theta-fold: the use form', '/-! ### theta-direct (theta-fold\'s plumbing): the use form')
BINDER = '(hθ : PkgI1.QMHauptmodul → G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM)'
sub1(H + 'TailZ35.lean',
     '(l : OpenAddedLeaves17) (g : OpenGlue7) : ZInQ.SixContactMin :=\n  sixContactMin_of_open28 (openResearchLeaves21_of_OpenResearchLeaves22 r t) t l g\n',
     '(l : OpenAddedLeaves17) (g : OpenGlue7)\n    ' + BINDER + ' : ZInQ.SixContactMin :=\n'
     '  sixContactMin_of_open28 (openResearchLeaves21_of_OpenResearchLeaves22 r t) t l g hθ\n')
# prune (theta-fold's script without its TailZ41 rows)
pr = open(f'{ROOT}/scratch/theta-direct/fold/prune_edit_theta_fold.py').read()
pr = pr.replace(", ('TailZ41', 'OpenAddedLeaves18')]:", "]:")
pr = pr.replace(",\n        ('TailZ41', 'theorem openAddedLeaves17_of_OpenAddedLeaves18 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic')]:", "]:")
assert 'TailZ41' not in pr
import io, contextlib
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    exec(pr, {'__name__': '__main__'})
open(f'{ROOT}/scratch/theta-direct/fold/fold-deleted.txt', 'w').write(buf.getvalue())
M = 'ZInQKernel/OneProof/Main.lean'
sub1(M, 'import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8\n',
     'import ZInQKernel.Contrib.OneProof.ThetaWeierstrass8\nimport ZInQKernel.Contrib.OneProof.ThetaDirect\n')
sub1(M, '(HDec.HSyn.sixContactMin_of_open29 r t l g)',
     '(HDec.HSyn.sixContactMin_of_open29 r t l g HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul)')
X = 'ZInQKernel/Contrib/OneProof/X0ModuliUsed.lean'
sub1(X, 'import ZInQKernel.OneProof.H.TailZ35\n', 'import ZInQKernel.OneProof.H.TailZ35\nimport ZInQKernel.Contrib.OneProof.ThetaDirect\n')
sx = open(X).read()
assert sx.count('(HDec.HSyn.sixContactMin_of_open29 r t l g)') == 3
open(X, 'w').write(sx.replace('(HDec.HSyn.sixContactMin_of_open29 r t l g)',
    '(HDec.HSyn.sixContactMin_of_open29 r t l g HDec.ThetaDirect.thetaRatiosAtQM_of_qmHauptmodul)'))
C = 'ZInQKernel/Contrib/OneProof/ThetaDirect/'
os.remove(C + 'UseForm.lean')
sub1(C + 'Split.lean', 'import ZInQKernel.Contrib.OneProof.ThetaDirect.UseForm\n', 'import ZInQKernel.OneProof.H.TailZ19\n')
os.chdir(OUT)
d = subprocess.run(['diff', '-ruN', 'a', 'b'], capture_output=True, text=True)
open(f'{ROOT}/scratch/theta-direct/fold/fold.patch', 'w').write(d.stdout)
print('patch lines', d.stdout.count('\n'))
