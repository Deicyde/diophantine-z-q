"""leaf-fold7: check that each new OneProof module is its source file(s) verbatim, up to the documented changes.

For each module, the source lines (minus `#print axioms` lines and trailing `example` blocks, and minus `import TailK`)
must appear in the module in order and unchanged; the module may add lines (banners, `section`/`end` wrappers,
reopened headers, imports). Lines of the source that are missing from the module are listed: they must be exactly the
documented removals. Run from the repository root."""
import difflib, sys
H = 'ZInQKernel/OneProof/H/'
def src_lines(path, drop_import_tailk=False):
    L = open(path).read().split('\n')
    out = []
    for l in L:
        if l.startswith('#print'):
            continue
        if drop_import_tailk and l == 'import TailK':
            continue
        out.append(l)
    # drop trailing `example` blocks (after the last namespace end) and blank lines
    while out and out[-1].strip() == '':
        out.pop()
    return out
def strip_examples(L):
    # remove `example ...` blocks at column 0 that follow the last `end` of the file (qm-split closing checks)
    i = len(L)
    for k in range(len(L) - 1, -1, -1):
        if L[k].startswith('end '):
            i = k + 1
            break
    tail = [l for l in L[i:] if l.strip()]
    if tail and all(not l.startswith(('def ', 'theorem ', 'namespace ')) for l in tail):
        return L[:i]
    return L
MODS = {
    'TailP': [('scratch/av-glue/Combined.lean', False)],
    'TailQ': [('scratch/av-split/AvSplitAll.lean', False)],
    'TailR': [('scratch/curve-split/CurveBij.lean', False), ('scratch/curve-split/CurvesGSplit.lean', False),
              ('scratch/curve-split/X0Split.lean', False)],
    'TailS+TailT': [('scratch/hodge-split/HodgeSplit.lean', False)],
    'TailU': [('scratch/qm-split/' + f + '.lean', True) for f in
              ['ClassNumberOne', 'YuLeaf', 'QMAut', 'STQM', 'ThetaSplit', 'ModuliSplit']],
    'TailW': [('scratch/mcr-glue/MCRGlue%d.lean.part' % i, False) for i in (1, 2, 3)],
}
ok = True
for mod, srcs in MODS.items():
    if mod == 'TailS+TailT':
        M = open(H + 'TailS.lean').read().split('\n') + open(H + 'TailT.lean').read().split('\n')
    else:
        M = open(H + mod + '.lean').read().split('\n')
    S = []
    for p, dt in srcs:
        S += strip_examples(src_lines(p, dt))
    sm = difflib.SequenceMatcher(None, S, M, autojunk=False)
    removed, added = [], 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag in ('delete', 'replace'):
            removed += S[i1:i2]
        if tag in ('insert', 'replace'):
            added += j2 - j1
    print(f'{mod}: source lines {len(S)}, module lines {len(M)}, added {added}, source lines missing {len(removed)}')
    for l in removed[:12]:
        print('   missing:', l[:110])
    if len(removed) > 12:
        print('   ...')
