"""For each \\section of a TeX file, list which key labels are referenced (\\ref/\\eqref) inside it.
usage: refmatrix.py FILE label1 label2 ..."""
import sys, re
f = sys.argv[1]; labs = sys.argv[2:]
L = open(f, encoding='utf-8').read().split('\n')
cur = ('preamble', 1); hits = {}
order = []
for i, l in enumerate(L):
    m = re.match(r'\\(section|part)\*?(?:\[[^\]]*\])?\{(.*?)\}', l)
    if m:
        cur = (m.group(2)[:60], i + 1); order.append(cur)
    for lab in labs:
        if re.search(r'ref\{%s\}' % re.escape(lab), l):
            hits.setdefault(cur, {}).setdefault(lab, []).append(i + 1)
for c in order:
    if c in hits:
        print('%6d %s' % (c[1], c[0]))
        for lab, ls in hits[c].items():
            print('        %s: %s' % (lab, ','.join(map(str, ls[:8])) + (' ...' if len(ls) > 8 else '')))
