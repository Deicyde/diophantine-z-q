"""Give HDec code access to the kernel declarations that replaced deleted HDec copies.

Inside `namespace HDec`, an unqualified reference `x` in `namespace HDec.A.B` resolves to `HDec.A.B.x`, `HDec.A.x`,
`HDec.x`, `x`, never to the kernel's `A.B.x`; and `open N` opens `HDec.N` when that namespace exists, not `N`.
After deleting copies, this script adds explicit-list opens (marked `-- op-dedupe`) that alias exactly the deleted
names to the kernel's, so no other kernel name becomes visible:
* after each `namespace P` line inside HDec: `open _root_.Q (r ...)` for each prefix Q of P, listing every deleted
  `Q.r` (r possibly dotted) not already provided by a longer prefix;
* after each `open N₁ N₂ ...` line inside HDec (also `hiding` / `... in` forms): `open _root_.M (r ...)` for the
  HDec namespace M that `Nᵢ` resolves to; an explicit list `open N (a b)` loses its deleted names, which move to
  `open _root_.M (...)`.
Usage: add_opens.py REPO MODULE.lean DELETED_MODULE.lean ...   (the map rows of the listed modules count as deleted,
except names in scratch/one-proof/kept.txt). Run once on a freshly regenerated module.
"""
import re, sys, pathlib, collections
src = open(pathlib.Path(__file__).parent / 'del_decls.py').read()
exec(src[src.index('def in_comment'):src.index('def main')])
repo = pathlib.Path(sys.argv[1]); mod = sys.argv[2]; dels = set(sys.argv[3:])
kept_f = repo / 'scratch/one-proof/kept.txt'
kept = set(l.split()[0] for l in kept_f.read_text().splitlines() if l.strip() and not l.startswith('#')) if kept_f.exists() else set()
rows = [r.split('\t') for r in (repo / 'scratch/one-proof/dedupe_map.tsv').read_text().splitlines() if r.strip()]
orig = repo / 'scratch/one-proof/orig_H'
ROOTMODS = ('LF2Stalks.lean', 'LF3Cot.lean')
DN = set()
for fn in dels:
    if fn in ROOTMODS: continue
    ls = (orig / fn).read_text(encoding='utf-8').split('\n'); inc = in_comment(ls)
    for r in rows:
        if r[0] == fn and not inc[int(r[1]) - 1] and r[3] not in kept: DN.add(r[3])
xf = repo / 'scratch/one-proof/extra_deleted.tsv'  # copies replaced by hand (fixes/*.py) by kernel names
if xf.exists():
    for l in xf.read_text().splitlines():
        if l.strip() and l.split('\t')[0] in dels: DN.add(l.split('\t')[1])
desc = collections.defaultdict(list)  # namespace Q -> deleted names below it, relative
for n in sorted(DN):
    parts = n.split('.')
    for k in range(1, len(parts)):
        desc['.'.join(parts[:k])].append('.'.join(parts[k:]))
# HDec namespaces (full, without HDec.) from the H chain's own declarations
KW = r'(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*(def|abbrev|structure|class|theorem|lemma|instance|inductive|opaque)'
start = re.compile(r'^(?:@\[[^\]]*\]\s*)?' + KW + r'\s+([^\s:({\[]+)')
H = set()
def scan_ns(lines):
    stack = []
    inc = in_comment(lines)
    for l, c in zip(lines, inc):
        if c: continue
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', l)
        if m: stack.append(('sec', m.group(1) or '')); continue
        m = re.match(r'^end(?:\s+(\S+))?\s*$', l)
        if m and stack: stack.pop(); continue
        m = start.match(l)
        if m:
            ns = '.'.join(n for k, n in stack if k == 'ns')
            full = ns + '.' + m.group(2)
            if full.startswith('HDec.'):
                parts = full.split('.')[1:-1]
                for k in range(1, len(parts) + 1): H.add('.'.join(parts[:k]))
for p in orig.glob('*.lean'): scan_ns(p.read_text(encoding='utf-8').split('\n'))
path = repo / 'ZInQKernel/OneProof/H' / mod
lines = path.read_text(encoding='utf-8').split('\n')
out = []; stack = []
TAG = ' -- op-dedupe'
def cur():
    ns = '.'.join(n for k, n in stack if k == 'ns').split('.')
    return ns[1:] if ns[0] == 'HDec' else None
def resolve(tok):
    rel = cur()
    if rel is None: return None
    for k in range(len(rel), -1, -1):
        cand = '.'.join(rel[:k] + [tok])
        if cand in H or cand in desc: return cand
    return None
def openline(M, names, suf=''):
    return f'open _root_.{M} ({" ".join(names)})' + suf + TAG
INC = in_comment(lines)
skipto = -1
for idx, l in enumerate(lines):
    if idx < skipto: continue
    if INC[idx]: out.append(l); continue
    m = re.match(r'^namespace\s+(\S+)', l)
    if m:
        out.append(l); stack.append(('ns', m.group(1)))
        rel = cur()
        if rel:
            seen = set()
            for k in range(len(rel), 0, -1):
                Q = '.'.join(rel[:k])
                names = [x for x in desc.get(Q, []) if x not in seen]
                seen |= set(names)
                if names: out.append(openline(Q, names))
        continue
    m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', l)
    if m: stack.append(('sec', m.group(1) or '')); out.append(l); continue
    m = re.match(r'^end(?:\s+(\S+))?\s*$', l)
    if m and stack: stack.pop(); out.append(l); continue
    if not l.startswith('open ') or l.startswith('open scoped') or cur() is None:
        out.append(l); continue
    # gather a possibly multi-line open command
    e = idx; txt = l
    while txt.count('(') > txt.count(')'): e += 1; txt += ' ' + lines[e].strip()
    while 'hiding' in txt and e + 1 < len(lines) and lines[e + 1].startswith('  ') and not re.search(r'\sin\s*$', txt):
        e += 1; txt += ' ' + lines[e].strip()
    suf = ' in' if re.search(r'\sin\s*$', txt) else ''
    body = re.sub(r'\sin\s*$', '', txt)[len('open '):].strip()
    skipto = e + 1
    mm = re.match(r'^(\S+)\s*\(([^)]*)\)$', body)
    if mm:  # explicit list
        M = resolve(mm.group(1))
        names = mm.group(2).split()
        gone = [x for x in names if M and M + '.' + x in DN]
        if not gone or mm.group(1).startswith('_root_.'):
            out.extend(lines[idx:e + 1]); continue
        stay = [x for x in names if x not in gone]
        out.append('-- op-dedupe was: ' + txt)
        if stay: out.append(f'open {mm.group(1)} ({" ".join(stay)})' + suf + TAG)
        out.append(openline(M, gone, suf)); continue
    out.extend(lines[idx:e + 1])
    if '(' in body or 'renaming' in body: continue
    mh = re.match(r'^(\S+)\s+hiding\s+(.*)$', body)
    toks = [mh.group(1)] if mh else body.split()
    hid = set(mh.group(2).split()) if mh else set()
    for tok in toks:
        if tok.startswith('_root_.'): continue
        M = resolve(tok)
        if M and desc.get(M):
            names = [x for x in desc[M] if x.split('.')[0] not in hid]
            if names: out.append(openline(M, names, suf))
path.write_text('\n'.join(out), encoding='utf-8')
print(mod, 'op-dedupe open lines:', sum(1 for l in out if l.endswith(TAG)))
