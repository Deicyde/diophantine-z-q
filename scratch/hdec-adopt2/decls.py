# List (full name, file, line) of top-level declarations; report names declared in several files.
import re, sys, collections, glob
KW = r'(?:noncomputable\s+|private\s+|protected\s+|@\[[^\]]*\]\s*|open [^\n]* in\s+)*'
DECL = re.compile(r'^' + KW + r'(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:({\[]+)')
def decls(path):
    ns = []; out = []
    for i, l in enumerate(open(path), 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(('n', m.group(1))); continue
        m = re.match(r'^(section|noncomputable section)\b\s*(\S*)', l)
        if m: ns.append(('s', m.group(2))); continue
        m = re.match(r'^end\b\s*(\S*)', l)
        if m and ns: ns.pop(); continue
        m = DECL.match(l)
        if m and m.group(1) != 'instance':
            pre = '.'.join(x[1] for x in ns if x[0] == 'n')
            out.append(((pre + '.' if pre else '') + m.group(2), path, i))
    return out
files = sys.argv[1:]
d = collections.defaultdict(list)
for f in files:
    for n, p, i in decls(f): d[n].append((p, i))
for n, v in sorted(d.items()):
    if len({p for p, _ in v}) > 1: print(n, v)
