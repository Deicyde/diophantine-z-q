"""Namespace-aware map of H-chain declarations that duplicate a kernel/Contrib declaration.

For each declaration in ZInQKernel/OneProof/H/*.lean, full name with a leading `HDec.` removed; it is a duplicate when a
declaration with that full name exists in ZInQKernel/HDecomp or ZInQKernel/Contrib with the same normalized source text.
Writes TSV: hchain_file line kind fullname kernel_file. Usage: dedupe_map.py REPO OUT.tsv
"""
import re, sys, pathlib, collections
KW = r'(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*(def|abbrev|structure|class|theorem|lemma|instance|inductive|opaque)'
start = re.compile(r'^(?:@\[[^\]]*\]\s*)?' + KW + r'\s+([^\s:({\[]+)')
stop = re.compile(r'^(?:/--|/-!|end\b|namespace\b|section\b|open\b|set_option\b|attribute\b|#|variable\b|universe\b|noncomputable section)')
def norm(s): return re.sub(r'\s+', ' ', re.sub(r'--[^\n]*', '', s)).strip()
def scan(path):
    lines = path.read_text(encoding='utf-8', errors='ignore').split('\n')
    stack = []  # (kind, name)
    out = []
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: stack.append(('ns', m.group(1))); i += 1; continue
        m = re.match(r'^(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', l)
        if m: stack.append(('sec', m.group(1) or '')); i += 1; continue
        m = re.match(r'^end(?:\s+(\S+))?\s*$', l)
        if m and stack: stack.pop(); i += 1; continue
        m = start.match(l)
        if m:
            j = i + 1
            while j < len(lines) and not start.match(lines[j]) and not stop.match(lines[j]): j += 1
            ns = '.'.join(n for k, n in stack if k == 'ns')
            name = m.group(2)
            full = name[len('_root_.'):] if name.startswith('_root_.') else (ns + '.' + name if ns else name)
            out.append((i + 1, m.group(1), full, norm('\n'.join(lines[i:j]))))
            i = j; continue
        i += 1
    return out
root = pathlib.Path(sys.argv[1])
kern = {}
for p in list((root / 'ZInQKernel/HDecomp').rglob('*.lean')) + list((root / 'ZInQKernel/Contrib').rglob('*.lean')):
    for line, kind, full, body in scan(p):
        kern.setdefault((full, body), str(p.relative_to(root)))
rows = []; tot = collections.Counter(); dup = collections.Counter()
for p in sorted((root / 'ZInQKernel/OneProof/H').glob('*.lean')):
    for line, kind, full, body in scan(p):
        f = full[len('HDec.'):] if full.startswith('HDec.') else full
        tot[p.name] += 1
        # the body text contains the declared name; compare with the HDec-free name substituted back
        k = kern.get((f, body))
        if k: dup[p.name] += 1; rows.append(f'{p.name}\t{line}\t{kind}\t{f}\t{k}')
pathlib.Path(sys.argv[2]).write_text('\n'.join(rows) + '\n')
for n in tot: print(f'{n}: {dup[n]} of {tot[n]} declarations duplicate a kernel/Contrib declaration (same full name and text)')
mods = collections.Counter(r.split('\t')[4] for r in rows)
print('kernel modules supplying duplicates:', len(mods)); print('\n'.join(f'  {c} {m}' for m, c in mods.most_common(15)))
