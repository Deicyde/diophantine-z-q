"""assemble-port: parts/e45_cpts.lean = scratch/cpts-transport/CPtsTransport.lean and BCUnique.lean (task cpts-transport,
compiled there over g0-assemble3's `import TailF`), verbatim minus `import`, `#check`, `#print` lines, plus an `end` closing each file's `noncomputable section`; then mk/open_zinq.py
(`open ZInQ` → `open _root_.ZInQ ZInQ`). Proves `FibreQM.cPtsTransport_proof : CPtsTransport` and
`PeriodMapH.baseChangeClassUnique_proof : BaseChangeClassUnique`. Run from scratch/assemble-port."""
import subprocess, sys
out = ['/-! ## assemble-port: cpts-transport (`CPtsTransport`, `BaseChangeClassUnique` proved). `scratch/cpts-transport/`',
       '`CPtsTransport.lean` + `BCUnique.lean`, verbatim minus `import`/`#check`/`#print` lines (mk/mk_e45.py). -/', '']
for f in ['CPtsTransport.lean', 'BCUnique.lean']:
    for l in open('../cpts-transport/' + f).read().split('\n'):
        if l.startswith('import ') or l.startswith('#check') or l.startswith('#print'): continue
        out.append(l)
    out.append('end  -- assemble-port: closes the file\'s `noncomputable section` (the part is wrapped in a named section)')
    out.append('')
open('parts/e45_cpts.lean', 'w').write('\n'.join(out))
subprocess.run([sys.executable, '-I', 'mk/open_zinq.py', 'parts/e45_cpts.lean'], check=True)
