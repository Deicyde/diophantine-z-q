"""Compute LaTeX theorem numbers (counter 'theorem' reset per section) for given labels.
usage: thmnum.py FILE label..."""
import sys, re
f = sys.argv[1]; labs = set(sys.argv[2:])
src = open(f, encoding='utf-8').read().split('\n')
shared = set()
for l in src[:200]:
    m = re.match(r'\\newtheorem\{(\w+)\}(?:\[theorem\])?\{', l)
    if m and ('[theorem]' in l or m.group(1) == 'theorem'): shared.add(m.group(1))
sec = 0; n = 0; app = False; out = {}
for i, l in enumerate(src):
    if re.match(r'\\appendix', l): app = True; sec = 0
    if re.match(r'\\section\{', l) or re.match(r'\\section\[', l):
        sec += 1; n = 0
    for m in re.finditer(r'\\begin\{(\w+)\}', l):
        if m.group(1) in shared: n += 1; last = (m.group(1), n, i + 1)
    for lab in labs:
        if '\\label{%s}' % lab in l:
            s = chr(64 + sec) if app else str(sec)
            print('%s: %s %s.%d (env line %d)' % (lab, last[0], s, last[1], last[2]))
