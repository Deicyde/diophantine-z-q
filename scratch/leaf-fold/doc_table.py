"""leaf-fold: add a Status column to the §2.2 textbook table of docs/research/h-decomposition.md."""
import re
p = 'docs/research/h-decomposition.md'
L = open(p).read().split('\n')
S = {
 'T1': 'open', 'T2': '**proved** (`HSyn.t2_proved`; t-brauer-purity)',
 'T3': 'open', 'T4': 'open', 'T5': 'open', 'T6': 'open', 'T7': 'open', 'T8': 'open',
 'T9': 'open', 'T10': 'open', 'T11': 'open (both parts)', '~~T12~~': 'glue (target)',
 'T35': 'open', 'T26': 'open', 'T27': 'open', 'T33': 'open',
 '~~T13~~': 'proved (glue)', 'T14': 'open (both parts; reduce to `KummerIndexBound`, `HSyn.t14_of_kummerIndexBound`)',
 'T15': '**proved** (`HSyn.t15_proved`; t1415-tc)',
 'T16': '(a) **proved** (`HSyn.t16a_proved`; lkw); (b) open',
 'T17': '**proved** (`HSyn.t17_proved`; kw-new)', 'T18': '**proved** (`HSyn.t18_proved`; cheb-bridge)',
 '~~T19~~': 'proved (glue)', 'T29': 'open (both parts)', '~~T30~~': 'proved (`HSyn.t30_proved`; lkw)',
 'T31': '**proved** (`HSyn.t31_proved`; t31-unram)', '~~T32~~': 'proved (glue)',
 'T20': '**proved**, global form (`HSyn.t20_proved`; diff-bridge)',
 'T21': '**proved**, global form (`HSyn.t21_proved`; diff-bridge)', '~~T22~~': 'proved (glue)',
 'T23': 'open', 'T24': 'open', 'T25': '**proved** (`HSyn.t25_proved`; t25-newform)', 'T28': 'open',
 'T34': 'open', 'T36': 'open', 'T37': 'open', 'T38': 'open', 'T39': 'open', 'T40': 'open', 'T41': 'open',
}
i0 = next(i for i, l in enumerate(L) if l.startswith('| # | Statement (form used) | Reference (UNVERIFIED) | E/C | Lean | Formalized |'))
assert 'Status' not in L[i0]
L[i0] += ' Status (leaf-fold) |'
L[i0 + 1] += ' --- |'
done = set()
i = i0 + 2
while i < len(L) and L[i].startswith('|'):
    key = L[i].split('|')[1].strip()
    if key.startswith('**('):
        L[i] += ' |'
    else:
        L[i] += ' ' + S[key] + ' |'
        done.add(key)
    i += 1
missing = set(S) - done
assert not missing, missing
open(p, 'w').write('\n'.join(L))
print('rows', len(done))
