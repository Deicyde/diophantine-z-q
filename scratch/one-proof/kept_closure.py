"""Which mapped (same name, same text) H-chain copies must be KEPT because their text refers to a divergent name.

A name n is *divergent* when the H chain declares HDec.n (or n, root) with a text different from the kernel's n
(same full name in ZInQKernel/HDecomp or Contrib, not in the map): the same text then means different things on the
two sides. A mapped copy whose text mentions a divergent name (token t with n == t or n ending in '.t') is KEPT, and
its name becomes divergent too; iterate to a fixpoint. Over-approximation by tokens; manual entries can be added to
scratch/one-proof/kept_manual.txt (name reason...). Writes scratch/one-proof/kept.txt (name reason).
Usage: kept_closure.py REPO
"""
import re, sys, pathlib, collections
repo = pathlib.Path(sys.argv[1])
src = open(repo / 'scratch/one-proof/dedupe_map.py').read()
# reuse scan() and norm() from dedupe_map.py without running its main part
ns = {}
exec(src[:src.index('root = pathlib.Path(sys.argv[1])')], ns)
scan = ns['scan']
kern_names = set()
for p in list((repo / 'ZInQKernel/HDecomp').rglob('*.lean')) + list((repo / 'ZInQKernel/Contrib').rglob('*.lean')):
    for line, kind, full, body in scan(p): kern_names.add(full)
rows = [r.split('\t') for r in (repo / 'scratch/one-proof/dedupe_map.tsv').read_text().splitlines() if r.strip()]
mapped = {(r[0], int(r[1])): r for r in rows}
H = []  # (file, line, name, body)
base = repo / 'scratch/one-proof/orig_H'
for p in sorted(base.glob('*.lean')):
    for line, kind, full, body in scan(p):
        f = full[len('HDec.'):] if full.startswith('HDec.') else full
        H.append((p.name, line, f, body))
mapped_names = set(r[3] for r in rows)
div = set()
for fn, line, f, body in H:
    if (fn, line) not in mapped and f in kern_names and f not in mapped_names: div.add(f)
# resolved by hand (see log): the copy is replaced by the kernel's alias; bogus comment matches
for n in ['ZInQ.DefFaltings.AbVar', 'and']: div.discard(n)
manual = {}
mf = repo / 'scratch/one-proof/kept_manual.txt'
if mf.exists():
    for l in mf.read_text().splitlines():
        if l.strip() and not l.startswith('#'):
            n, _, why = l.partition(' '); manual[n] = why.strip()
print('divergent names (unmapped H decls with a same-named kernel decl):', len(div))
bylast = collections.defaultdict(set)
def add_div(n): div.add(n); bylast[n.split('.')[-1]].add(n)
for n in list(div): add_div(n)
for n in manual: add_div(n)
tok = re.compile(r"[A-Za-z_À-῿℀-⅏𝒜-𝔷][A-Za-z0-9_'!?À-῿₀-ₜ℀-⅏𝒜-𝔷.]*")
mrows = [(fn, line, f, body) for fn, line, f, body in H if (fn, line) in mapped]
toks = {(fn, line): set(t.strip('.') for t in tok.findall(body)) for fn, line, f, body in mrows}
kept = dict((n, 'manual: ' + w) for n, w in manual.items())
changed = True
while changed:
    changed = False
    for fn, line, f, body in mrows:
        if f in kept: continue
        for t in toks[(fn, line)]:
            last = t.split('.')[-1]
            hit = [n for n in bylast.get(last, ()) if n != f and (n == t or n.endswith('.' + t))]
            if hit:
                kept[f] = f'mentions divergent {hit[0]} (token {t})'; add_div(f); changed = True; break
(repo / 'scratch/one-proof/kept.txt').write_text('\n'.join(f'{n} {w}' for n, w in sorted(kept.items())) + '\n')
c = collections.Counter(fn for fn, line, f, body in mrows if f in kept)
print('KEPT mapped copies:', len(kept), dict(c))
print('divergent seeds sample:', sorted(div)[:40])
