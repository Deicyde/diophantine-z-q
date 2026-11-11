"""Per-section diff stats between two TeX files, sections matched by title.
usage: secdiff.py A B"""
import sys, re, difflib
def secs(f):
    L = open(f, encoding='utf-8').read().split('\n'); out = []; cur = None
    for i, l in enumerate(L):
        m = re.match(r'\\section\*?(?:\[[^\]]*\])?\{(.*?)\}', l)
        if m:
            cur = [m.group(1), i + 1, []]; out.append(cur)
        elif cur: cur[2].append(l)
    return out
A, B = secs(sys.argv[1]), secs(sys.argv[2])
bd = {}
for t, s, b in B: bd.setdefault(t, (s, b))
for t, s, a in A:
    if t not in bd: print('GONE  A:%d %s' % (s, t)); continue
    s2, b = bd[t]
    sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
    rem = sum(i2 - i1 for op, i1, i2, j1, j2 in sm.get_opcodes() if op != 'equal')
    add = sum(j2 - j1 for op, i1, i2, j1, j2 in sm.get_opcodes() if op != 'equal')
    print('A:%5d(%5d) B:%5d(%5d) -%d +%d  %s' % (s, len(a), s2, len(b), rem, add, t[:70]))
at = {t for t, _, _ in A}
for t, s, b in B:
    if t not in at: print('NEW   B:%d(%d) %s' % (s, len(b), t[:80]))
