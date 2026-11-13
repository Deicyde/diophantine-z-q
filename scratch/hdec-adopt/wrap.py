# Wrap lines longer than 100 characters in the given Lean files (comments: re-prefix; code:
# continuation indented 4 more than the line's indentation). Report lines it could not wrap.
import sys, re
LIM = 100
def ok_cut(line, i):
    return (line[i] == ' ' and line[i-1] not in '←·@(' and line[i+1:i+2] not in ('', ' ')
            and line.count('`', 0, i) % 2 == 0 and line.count('"', 0, i) % 2 == 0)
def split(line, cont_prefix, code=False):
    out = []
    while len(line) > LIM:
        ind = len(line) - len(line.lstrip(' '))
        cut = -1
        if code:
            # a same-line `by` block: break right after `by` (tactics on the next line)
            j = line.find(' by ', ind)
            if 0 < j and j + 3 <= LIM and line[j+4:].strip():
                cut = j + 3
        if cut < 0:
            for i in range(LIM, ind + 8, -1):
                if ok_cut(line, i):
                    cut = i; break
        if cut < 0: break
        out.append(line[:cut].rstrip())
        line = cont_prefix + line[cut+1:]
        if code and cut == j + 3 if code else False:
            cont_prefix = cont_prefix + '    '
    out.append(line)
    return out
for f in sys.argv[1:]:
    L = open(f, encoding='utf-8').read().split('\n')
    res = []; depth = 0
    for l in L:
        incomment_start = depth > 0
        if len(l) > LIM:
            s = l.lstrip(' '); ind = ' ' * (len(l) - len(s))
            if incomment_start or s.startswith('/-'):
                pre = ind + ('  ' if s.startswith('/-') else '')
                if incomment_start: pre = ind
                new = split(l, pre)
            elif s.startswith('--'):
                new = split(l, ind + '-- ')
            elif '--' in s or '/-' in s:
                new = [l]
            else:
                new = split(l, ind + ('        ' if s.startswith('calc ') else '    '), code=True)
            if any(len(x) > LIM for x in new): print('UNWRAPPED', f, l[:70])
            res += new
        else:
            res.append(l)
        depth += len(re.findall(r'/-', l)) - len(re.findall(r'-/', l))
        depth = max(depth, 0)
    open(f, 'w', encoding='utf-8').write('\n'.join(res))
