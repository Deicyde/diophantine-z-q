"""assemble-port: parts/z96_ltgoodred.lean = scratch/lt-goodred/integ/99d_proofs.lean (lt-goodred: `GoodRedTorsion` and
`QMEndRank` proved) and parts/z97_linkedram.lean = scratch/linked-ram/olean/Tail.lean at 3cb898bf (its final state,
report and flat check; copied to src/linked-ram-Tail-3cb898bf.lean) L2-1668 (linked-ram: KernelFieldBreaks split,
`UpperAbsWild`, `KernelFieldBreaksHigh` proved, `BetaTrivialAtTwo` reduced to `BetaSignAtTwo`, `TateRamAtThreeD` proved
from R6, T5 and `UpperBreakBound`, `linkedRam_of'`), both verbatim
minus `#print` lines (linked-ram's own bundle L1669-end, `GluePieces5`/`sixContactMin_of_leaves5` over `TextbookLeaves`,
is not copied; part z99 has this task's). Both compiled there over g0-assemble3's olean chain (`import TailD`).
Then mk/open_zinq.py. Run from scratch/assemble-port."""
import subprocess, sys
def noprint(L): return [l for l in L if not l.startswith('#print')]
a = open('../lt-goodred/integ/99d_proofs.lean').read().split('\n')
open('parts/z96_ltgoodred.lean', 'w').write('/-! ## assemble-port: lt-goodred, `scratch/lt-goodred/integ/99d_proofs.lean` verbatim minus `#print` (mk/mk_z96.py) -/\n\n' + '\n'.join(noprint(a)) + '\n')
b = open('src/linked-ram-Tail-3cb898bf.lean').read().split('\n')
assert b[0] == 'import GoodRedLR' and b[1667] == 'end LinkedRamMain', (b[0], b[1667])
open('parts/z97_linkedram.lean', 'w').write('/-! ## assemble-port: linked-ram, `scratch/linked-ram/olean/Tail.lean` at 3cb898bf (its final state; copied to src/) L2-1668 verbatim minus `#print` (mk/mk_z96.py) -/\n' + '\n'.join(noprint(b[1:1668])) + '\n')
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/z96_ltgoodred.lean', 'parts/z97_linkedram.lean'], check=True)
