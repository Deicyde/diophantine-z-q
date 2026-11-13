"""assemble-port: parts/z96_ltgoodred.lean = scratch/lt-goodred/integ/99d_proofs.lean (lt-goodred: `GoodRedTorsion` and
`QMEndRank` proved) and parts/z97_linkedram.lean = scratch/linked-ram/olean/Tail.lean at 06e34d44 (the state its
report and flat check describe; copied to src/linked-ram-Tail-06e34d44.lean) L2-944 (linked-ram: KernelFieldBreaks split,
`UpperAbsWild`, `KernelFieldBreaksHigh` proved, `TateRamAtThreeD` and `linkedRam_of'`; its later WIP TateRam section is not used), both verbatim
minus `#print` lines (linked-ram's own bundle L945-end, `GluePieces5`/`sixContactMin_of_leaves5` over `TextbookLeaves`,
is not copied; part z99 has this task's). Both compiled there over g0-assemble3's olean chain (`import TailD`).
Then mk/open_zinq.py. Run from scratch/assemble-port."""
import subprocess, sys
def noprint(L): return [l for l in L if not l.startswith('#print')]
a = open('../lt-goodred/integ/99d_proofs.lean').read().split('\n')
open('parts/z96_ltgoodred.lean', 'w').write('/-! ## assemble-port: lt-goodred, `scratch/lt-goodred/integ/99d_proofs.lean` verbatim minus `#print` (mk/mk_z96.py) -/\n\n' + '\n'.join(noprint(a)) + '\n')
b = open('src/linked-ram-Tail-06e34d44.lean').read().split('\n')
assert b[0] == 'import GoodRedLR' and b[943] == 'end LinkedRamMain', (b[0], b[943])
open('parts/z97_linkedram.lean', 'w').write('/-! ## assemble-port: linked-ram, `scratch/linked-ram/olean/Tail.lean` at 06e34d44 (copied to src/) L2-944 verbatim minus `#print` (mk/mk_z96.py) -/\n' + '\n'.join(noprint(b[1:944])) + '\n')
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/z96_ltgoodred.lean', 'parts/z97_linkedram.lean'], check=True)
