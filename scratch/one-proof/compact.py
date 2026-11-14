"""op-compact: replace op-dedupe's repeated alias opens by `export` aliases at the deleted copies' names.

For each H module M (import order), the tagged lines `open _root_.Q (r ...) -- op-dedupe` alias `r` to the
kernel's `Q.r`, where `HDec.Q.r` was a deleted copy. This script removes these lines and puts, once, after M's
imports, for each top component T of the names first aliased in M:
    namespace HDec.T export _root_.T (rest ...) end HDec.T
which re-creates `HDec.T.rest` as an alias of the kernel's `T.rest`, so every reference resolves as it did to the
copy. The tagged lines that replace an original explicit-list open (below a `-- op-dedupe was:` comment)
are kept. Names aliased by an earlier module are not repeated (aliases persist through imports).
Usage: compact.py REPO [--dry]
"""
import re, sys, pathlib
repo = pathlib.Path(sys.argv[1]); dry = '--dry' in sys.argv
ORDER = 'LPrefix TailA TailB TailC TailD LF2Stalks LF2UnifRoot LF2SmoothDim LF2UnramConj LF3Cot TailE TailF TailG TailH TailI LF4T5 TailJ TailK'.split()
TAGRE = re.compile(r'^\s*open _root_\.(\S+) \(([^)]*)\)( in)? -- op-dedupe$')
seen = set(); tot = [0, 0, 0, 0]
for mod in ORDER:
    p = repo / 'ZInQKernel/OneProof/H' / (mod + '.lean')
    lines = p.read_text(encoding='utf-8').split('\n')
    new = []; names = []; nrm = 0
    for i, l in enumerate(lines):
        m = TAGRE.match(l)
        # keep the lines that replace an original explicit-list open (op-dedupe `was:` comment just above)
        if m and any(x.startswith('-- op-dedupe was:') for x in lines[max(0, i - 2):i]): m = None
        if m:
            nrm += 1
            for r in m.group(2).split():
                full = m.group(1) + '.' + r
                if full not in seen: seen.add(full); names.append(full)
            continue
        new.append(l)
    if names:
        groups = {}
        for n in names:
            t, rest = n.split('.', 1); groups.setdefault(t, []).append(rest)
        block = ['', '-- op-compact: aliases `HDec.T.x := T.x` for the copies deleted by op-dedupe (first used here)']
        for t, rs in groups.items():
            block.append(f'namespace HDec.{t} export _root_.{t} ({" ".join(rs)}) end HDec.{t}')
        # insert after the last leading import line
        k = 0
        while k < len(new) and (new[k].startswith('import ') or new[k].strip() == ''): k += 1
        j = max(i for i in range(k) if new[i].startswith('import ')) + 1
        new[j:j] = block
    out = '\n'.join(new)
    b0, b1 = len('\n'.join(lines).encode()), len(out.encode())
    print(f'{mod}\t{len(lines)}\t{b0}\t{len(new)}\t{b1}\t-{nrm} open lines\t+{len(names)} aliases')
    tot = [tot[0] + len(lines), tot[1] + b0, tot[2] + len(new), tot[3] + b1]
    if not dry: p.write_text(out, encoding='utf-8')
print('TOTAL', *tot, sep='\t')
