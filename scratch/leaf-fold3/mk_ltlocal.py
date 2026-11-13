#!/usr/bin/env python3
"""leaf-fold3: part partsF/c85_ltlocal.lean, lt-local's route to `LinkedTateLocal` with its inputs.
Sources, in this order, each with every declaration already present in the chain dropped (by full
name, `HDec.` ignored; anonymous instances by text), `import`/`#print`/`#check` lines dropped and the
HDec edits of mk_lf3.py:
  1. scratch/lt-local/LtLocal4.lean (lg-kerwild's KerWild.lean with g0-assemble3's G7Data fix, which
     contains verbatim copies of local-glue, frob-trace, unram-tate, g14-trace, g0-mod-field, g0-dim; then
     lt-local's parts and its variant part_gp4: `LinkedTateLocal` over the G7Data with `[L:ℚ] ≤ D`);
  2. scratch/unram-roots/UnramRoots.lean (`UnramRoots p ℓ` for all p, ℓ);
  3. scratch/frob-pieces/FrobPiecesFull.lean (alg-frob-red + afr-absfrob + frob-pieces: TateBridge35 from
     I3.M0, AbVarSpreadsOut, ProperSmoothGenConnected, I2-Red, I2-NMP).
The script prints, for each source, the declarations dropped whose text differs from the chain's copy."""
import sys, glob
sys.path.insert(0, 'py'); sys.path.insert(0, '.')
from chunks import chunks, fullnames, text
from mk_lf3 import hdec
idx = {}
def key(n, c):
    return n if c['name'] else ('anon', text(c))
for f in ['olean/LPrefix.lean'] + sorted(glob.glob('parts/*.lean')) + sorted(p for p in glob.glob('partsF/*.lean') if not p.endswith('c85_ltlocal.lean') and not p.endswith('d90_fold3.lean')):
    cs = chunks(open(f).read())
    for n, c in fullnames(cs):
        if n.startswith('HDec.'): n = n[5:]
        idx.setdefault(n, text(c))
    for c in cs:
        if c['kind'] == 'decl' and not c['name']: idx.setdefault(('anon', text(c)), text(c))
def filt(src, tag):
    cs = chunks(open(src).read())
    names = {id(c): n for n, c in fullnames(cs)}
    out = []; nd = 0; diffs = []
    for c in cs:
        if c['kind'] == 'decl':
            k = names.get(id(c)) if c['name'] else ('anon', text(c))
            if k is not None and k in idx:
                if idx[k] != text(c): diffs.append(k)
                nd += 1; continue
            if k is not None: idx[k] = text(c)
        if c['kind'] == 'struct' and (c['lines'][0].startswith('import ') or c['lines'][0].startswith('#')):
            continue
        out.append(text(c))
    print(tag, 'dropped', nd, 'differing', diffs, file=sys.stderr)
    return '/-! ## leaf-fold3: %s, declarations already in the chain dropped -/\n\n' % tag + '\n'.join(out)
body = '\n\n'.join([filt('../lt-local/LtLocal4.lean', 'scratch/lt-local/LtLocal4.lean'),
                    filt('../unram-roots/UnramRoots.lean', 'scratch/unram-roots/UnramRoots.lean'),
                    filt('../frob-pieces/FrobPiecesFull.lean', 'scratch/frob-pieces/FrobPiecesFull.lean')])
open('partsF/c85_ltlocal.lean', 'w').write('-- (leaf-fold3) mk_ltlocal.py: lt-local LtLocal4.lean, unram-roots UnramRoots.lean, frob-pieces FrobPiecesFull.lean, deduplicated against the chain\n' + hdec(body) + '\n')
print('ok')
