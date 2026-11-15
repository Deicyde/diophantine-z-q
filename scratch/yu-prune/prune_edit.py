"""yu-prune step 2: delete scratch/yu-prune/prune-set-applied.txt's fields from every bundle generation (plus
OpenTextbookLeaves11.yuThm11 in TailZ32, which the open25-rooted scan cannot see), the assignments into them, and the
dead readers (scratch/yu-prune/dead-cascade.txt, generated casesOn/recOn excluded), with their `#print axioms` lines
and `example`s. Deletions only (and the bridge helper that loses its users). sem-prune's script, adapted.
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

# fields (prune-set-applied.txt, plus OpenTextbookLeaves11.yuThm11)
for f, s, fl in [('LPrefix', 'TextbookLeaves', 't27'), ('TailE', 'OpenTextbookLeaves2', 't27'),
                 ('TailI', 'OpenTextbookLeaves3', 't27'), ('TailK', 'OpenTextbookLeaves4', 't27'),
                 ('TailO', 'OpenTextbookLeaves6', 't27'), ('TailX', 'OpenTextbookLeaves7', 'yuThm11'),
                 ('TailZ4', 'OpenTextbookLeaves8', 'yuThm11'), ('TailZ9', 'OpenTextbookLeaves9', 'yuThm11'),
                 ('TailZ11', 'OpenTextbookLeaves10', 'yuThm11'), ('TailZ32', 'OpenTextbookLeaves11', 'yuThm11')]:
    drop_field(f, s, fl)
# assignments into removed fields
for f, h, fl, ex in [
        ('LPrefix', 'theorem textbookLeaves_of_open ', 't27', '  t27 := t.t27'),
        ('TailE', 'theorem textbookLeaves_of_open2 ', 't27', '  t27 := t.t27'),
        ('TailI', 'theorem textbookLeaves2_of_open3 ', 't27', '  t27 := t.t27'),
        ('TailK', 'theorem textbookLeaves3_of_open4 ', 't27', '  t27 := t.t27'),
        ('TailN', 'theorem textbookLeaves4_of_open5 ', 't27', '  t27 := qmDichotomyYu_ofK5 t.t27'),
        ('TailO', 'theorem textbookLeaves4_of_open6 ', 't27', '  t27 := qmDichotomyYu_ofK5 t.t27'),
        ('TailX', 'theorem textbookLeaves6_of_open7 ', 't27', '  t27 := QMSplit.Yu.qmDichotomyYu_of_yu t.yuThm11'),
        ('TailZ4', 'theorem textbookLeaves7_of_open8 ', 'yuThm11', '  yuThm11 := t.yuThm11'),
        ('TailZ9', 'theorem textbookLeaves8_of_open9 ', 'yuThm11', '  yuThm11 := t.yuThm11'),
        ('TailZ11', 'theorem textbookLeaves9_of_open10 ', 'yuThm11', '  yuThm11 := t.yuThm11'),
        ('TailZ32', 'theorem openTextbookLeaves10_of_OpenTextbookLeaves11 ', 'yuThm11', '  yuThm11 := n.yuThm11')]:
    drop_assign(f, h, fl, ex)
# dead readers (dead-cascade.txt minus generated casesOn/recOn), and the bridge helper that loses its users
for f, n in [('TailD', 'fibreComTrivial_of_gp3'), ('TailD', 'fibreSimple_of_gp3'), ('TailD', 'gluePieces_of_gluePieces3'),
             ('TailE', 'gluePieces_of_open2'), ('TailI', 'gluePieces_of_open3'), ('TailA', 'yuB6Alg_of_qmDichotomyYu')]:
    drop_decl(f, n)
for f, ls in files.items():
    open(H + f + '.lean', 'w').write('\n'.join(l for l in ls if l is not None))
for d in sorted(deleted):
    print(f'{d[0]}:{d[1]}  [{d[2]}]  {d[3]}')
