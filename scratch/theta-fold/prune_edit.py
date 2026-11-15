"""theta-fold step 2: delete scratch/theta-fold/prune-set-applied.txt's 12 fields `thetaRatiosAlgebraic`, the
assignments into them (13 `field := …` lines and one element of the anonymous constructor in TailO's
`openAddedLeaves4_of_Q5`), and the dead readers of scratch/theta-fold/dead-cascade.txt (generated casesOn/recOn
excluded) with their `#print axioms` lines. Deletions only. yu-prune's script, adapted.
Run from the repository root; prints every deleted line."""
import re
H = 'ZInQKernel/OneProof/H/'
files = {}
def get(f):
    if f not in files:
        files[f] = open(H + f + '.lean').read().split('\n')
    return files[f]
deleted = []
def drop(f, idxs, why):
    ls = get(f)
    for i in sorted(set(idxs), reverse=True):
        assert ls[i] is not None, (f, i)
        deleted.append((f, i + 1, why, ls[i]))
        ls[i] = None
def find(f, pred, start=0, end=None):
    ls = get(f)
    return [i for i in range(start, end if end is not None else len(ls)) if ls[i] is not None and pred(ls[i])]
def doc_start(ls, i):
    """first line of the docstring directly above line i (i itself if none)."""
    if i == 0 or ls[i - 1] is None or not ls[i - 1].rstrip().endswith('-/'):
        return i
    j = i - 1
    while '/-' not in ls[j]:
        j -= 1
    return j if ls[j].lstrip().startswith('/--') else i
def block_of_struct(f, header):
    ls = get(f)
    a = find(f, lambda l: l.startswith(header))
    assert len(a) == 1, (f, header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ')):
        b += 1
    return a, b
def drop_field(f, struct, field):
    a, b = block_of_struct(f, f'structure {struct} ')
    ls = get(f)
    hits = find(f, lambda l: l.startswith(f'  {field} : '), a, b)
    assert len(hits) == 1, (f, struct, field, hits)
    i = hits[0]
    idx = [i]
    if ls[i - 1].rstrip().endswith('-/'):
        j = i - 1
        while '/-' not in ls[j]:
            j -= 1
        assert ls[j].startswith('  /--'), (f, j, ls[j])
        idx += list(range(j, i))
    drop(f, idx, f'field {struct}.{field}')
def drop_assign(f, decl_header, field, exact):
    ls = get(f)
    a = find(f, lambda l: l.startswith(decl_header))
    assert len(a) == 1, (f, decl_header, a)
    a = a[0]
    b = a + 1
    while b < len(ls) and (ls[b] is None or ls[b].startswith(' ')):
        b += 1
    hits = find(f, lambda l: l.startswith(f'  {field} := ') or l.startswith(f'    {field} := '), a, b)
    assert len(hits) == 1, (f, decl_header, field, hits)
    assert ls[hits[0]] == exact, (ls[hits[0]], exact)
    drop(f, hits, f'assignment {field} in {decl_header.split()[1]}')
def drop_decl(f, name):
    ls = get(f)
    hits = find(f, lambda l: re.match(rf'theorem (\S*\.)?{re.escape(name)}(\s|$)', l) is not None)
    assert len(hits) == 1, (f, name, hits)
    i = hits[0]
    j = doc_start(ls, i)
    if j > 0 and ls[j - 1] is not None and ls[j - 1].startswith('open ') and ls[j - 1].rstrip().endswith(' in'):
        j -= 1
    k = i + 1
    while k < len(ls) and ls[k] is not None and ls[k].strip() != '':
        assert ls[k].startswith(' '), (f, name, k, ls[k])
        k += 1
    if k < len(ls) and ls[k] == '':
        k += 1
    drop(f, range(j, k), f'dead reader {name}')
    short = name.split('.')[-1]
    pr = find(f, lambda l: l.startswith('#print axioms ') and l.split()[-1].split('.')[-1] == short)
    drop(f, pr, f'#print of dead reader {name}')
    # `example : ... := HDec.HSyn.NAME` blocks
    for e in find(f, lambda l: l.startswith('example ')):
        k = e
        while ls[k] is not None and ls[k].strip() != '':
            k += 1
        body = ' '.join(l for l in ls[e:k] if l is not None)
        if re.search(rf'\.{re.escape(short)}\s*$', body.strip()):
            end = k + 1 if k < len(ls) and ls[k] == '' else k
            drop(f, range(e, end), f'example of dead reader {name}')

# fields (prune-set-applied.txt)
for f, s in [('TailK', 'OpenAddedLeaves4'), ('TailO', 'OpenAddedLeaves6'), ('TailX', 'OpenAddedLeaves7'),
             ('TailZ4', 'OpenAddedLeaves8'), ('TailZ13', 'OpenAddedLeaves9'), ('TailZ22', 'OpenAddedLeaves12'),
             ('TailZ24', 'OpenAddedLeaves13'), ('TailZ26', 'OpenAddedLeaves14'), ('TailZ30', 'OpenAddedLeaves15'),
             ('TailZ31', 'OpenAddedLeaves16'), ('TailZ34', 'OpenAddedLeaves17'), ('TailZ41', 'OpenAddedLeaves18')]:
    drop_field(f, s, 'thetaRatiosAlgebraic')
# assignments into removed fields
for f, h, ex in [
        ('TailN', 'theorem addedLeaves4_of_open5 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailO', 'theorem addedLeaves4_of_open6 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailX', 'theorem addedLeaves6_of_open7 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ4', 'theorem addedLeaves7_of_open8 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ13', 'theorem addedLeaves8_of_open9 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ17', 'theorem addedLeaves9_of_open10 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ23', 'theorem addedLeaves9_of_open14 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ24', 'theorem addedLeaves12_of_open13 ', '  thetaRatiosAlgebraic := l.thetaRatiosAlgebraic'),
        ('TailZ26', 'theorem openAddedLeaves13_of_OpenAddedLeaves14 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic'),
        ('TailZ30', 'theorem openAddedLeaves14_of_OpenAddedLeaves15 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic'),
        ('TailZ31', 'theorem openAddedLeaves15_of_OpenAddedLeaves16 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic'),
        ('TailZ34', 'theorem openAddedLeaves16_of_OpenAddedLeaves17 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic'),
        ('TailZ41', 'theorem openAddedLeaves17_of_OpenAddedLeaves18 ', '  thetaRatiosAlgebraic := n.thetaRatiosAlgebraic')]:
    drop_assign(f, h, 'thetaRatiosAlgebraic', ex)
# the anonymous constructor of OpenAddedLeaves4 in openAddedLeaves4_of_Q5 (TailO): drop its second element
ls = get('TailO')
a = find('TailO', lambda l: l.startswith('theorem openAddedLeaves4_of_Q5 '))
assert len(a) == 1
i = a[0] + 1
old = '  ⟨l.cmOptimalEmbedding, l.thetaRatiosAlgebraic, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,'
assert ls[i] == old, ls[i]
deleted.append(('TailO', i + 1, 'element thetaRatiosAlgebraic in openAddedLeaves4_of_Q5 (line rewritten)', ls[i]))
ls[i] = '  ⟨l.cmOptimalEmbedding, l.qmHauptmodul, l.qmClassNumberOne, l.senTwist,'
# dead readers (dead-cascade.txt minus generated casesOn/recOn)
for f, n in [('TailO', 'addedLeaves5_of_open6'), ('TailZ22', 'addedLeaves11_of_open12'), ('TailZ22', 'sixContactMin_of_open16')]:
    drop_decl(f, n)
for f, ls in files.items():
    open(H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
