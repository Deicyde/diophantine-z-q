"""Helpers copied from scratch/yu-prune/prune_edit.py (sem-prune/genus-fold lineage); drop_assign also removes
continuation lines indented deeper than the assignment."""
import re
H = "ZInQKernel/OneProof/H/"
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
    i = hits[0]
    ind = len(ls[i]) - len(ls[i].lstrip())
    k = i + 1
    while k < b and ls[k] is not None and ls[k].strip() != '' and (len(ls[k]) - len(ls[k].lstrip())) > ind:
        k += 1
    got = '\n'.join(ls[i:k])
    assert got == exact, (got, exact)
    drop(f, range(i, k), f'assignment {field} in {decl_header.split()[1]}')
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

