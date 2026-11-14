"""Delete H-chain declarations listed in dedupe_map.tsv from one module and import their kernel modules.

Usage: del_decls.py REPO MODULE.lean [--only LINE,LINE,...] [--skip NAME,NAME,...] [--dry]
Extents are computed exactly as dedupe_map.py does (declaration start up to the next declaration start or stop line),
extended backwards over an attached docstring and `@[..]` / `open .. in` / `set_option .. in` lines, and truncated
before a column-0 non-declaration command (notation, example, ...) swallowed by the extent.
Line numbers refer to the file as it is when the map was generated; regenerate the map after each edit.
"""
import re, sys, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).parent))
KW = r'(?:noncomputable\s+|private\s+|protected\s+|partial\s+|unsafe\s+)*(def|abbrev|structure|class|theorem|lemma|instance|inductive|opaque)'
start = re.compile(r'^(?:@\[[^\]]*\]\s*)?' + KW + r'\s+([^\s:({\[]+)')
stop = re.compile(r'^(?:/--|/-!|end\b|namespace\b|section\b|open\b|set_option\b|attribute\b|#|variable\b|universe\b|noncomputable section)')
other_cmd = re.compile(r'^(?:@\[|include\s|omit\s|local\s|scoped\s|notation|infix|infixl|infixr|prefix|postfix|macro|syntax|elab|alias|example|deriving|initialize|export|add_decl_doc|unif_hint|run_cmd|termination_by|decreasing_by|/-[^-!])')

def in_comment(lines):
    """inc[i] = line i starts inside a block comment (Lean block comments nest)."""
    inc = []; depth = 0
    for l in lines:
        inc.append(depth > 0)
        i = 0
        while i < len(l):
            if depth == 0 and l.startswith('--', i): break
            if depth == 0 and l[i] == '"':
                j = l.find('"', i + 1)
                while j > 0 and l[j - 1] == '\\': j = l.find('"', j + 1)
                i = (j + 1) if j > 0 else len(l); continue
            if l.startswith('/-', i): depth += 1; i += 2; continue
            if l.startswith('-/', i) and depth > 0: depth -= 1; i += 2; continue
            i += 1
    return inc

def main():
    repo = pathlib.Path(sys.argv[1]); mod = sys.argv[2]
    args = sys.argv[3:]
    only = skip = None; dry = '--dry' in args
    if '--only' in args: only = set(int(x) for x in args[args.index('--only') + 1].split(','))
    if '--skip' in args: skip = set(args[args.index('--skip') + 1].split(','))
    path = repo / 'ZInQKernel/OneProof/H' / mod
    rows = [r.split('\t') for r in (repo / 'scratch/one-proof/dedupe_map.tsv').read_text().splitlines() if r.strip()]
    rows = [r for r in rows if r[0] == mod]
    if only is not None: rows = [r for r in rows if int(r[1]) in only]
    if skip is not None: rows = [r for r in rows if r[3] not in skip]
    kf = repo / 'scratch/one-proof/kept.txt'
    kept = set(l.split()[0] for l in kf.read_text().splitlines() if l.strip() and not l.startswith('#')) if kf.exists() else set()
    for r in rows:
        if r[3] in kept: print('  KEPT:', r[1], r[3])
    rows = [r for r in rows if r[3] not in kept]
    lines = path.read_text(encoding='utf-8').split('\n')
    inc = in_comment(lines)
    bad = [r for r in rows if inc[int(r[1]) - 1]]
    for r in bad: print('  skip (inside a comment):', r[1], r[2], r[3])
    rows = [r for r in rows if not inc[int(r[1]) - 1]]
    kill = [False] * len(lines)
    kmods = []
    for r in rows:
        i = int(r[1]) - 1
        m = start.match(lines[i])
        assert m, (r, lines[i])
        j = i + 1
        while j < len(lines) and not start.match(lines[j]) and not stop.match(lines[j]): j += 1
        for t in range(i + 1, j):
            if other_cmd.match(lines[t]):
                print(f'  truncate {r[3]} at line {t+1}: {lines[t][:60]}'); j = t; break
        a = i
        while True:
            p = a - 1
            if p < 0: break
            if re.match(r'^(?:@\[.*\]|(?:open|set_option|include|omit|variable|attribute)\s.*\sin)\s*$', lines[p]): a = p; continue
            if re.search(r'\sin\s*$', lines[p]) and lines[p][:1].isspace():
                q = p
                while q > 0 and lines[q][:1].isspace(): q -= 1
                if re.match(r'^(?:omit|include|variable|open|set_option|attribute)\b', lines[q]): a = q; continue
            if lines[p].rstrip().endswith('-/'):
                q = p; ok = False
                while q >= 0:
                    if '/-' in lines[q]:
                        ok = lines[q].startswith('/--'); break
                    if q < p and '-/' in lines[q]: break
                    q -= 1
                if ok: a = q; continue
            break
        for t in range(a, j): kill[t] = True
        km = r[4][:-len('.lean')].replace('/', '.')
        if km not in kmods: kmods.append(km)
    print(f'{mod}: deleting {len(rows)} declarations, {sum(kill)} lines; kernel modules: {len(kmods)}')
    if dry: return
    out = [l for l, k in zip(lines, kill) if not k]
    have = set(l.strip() for l in out if l.startswith('import '))
    last_imp = max(n for n, l in enumerate(out) if l.startswith('import '))
    new = [f'import {m}' for m in kmods if f'import {m}' not in have]
    out = out[:last_imp + 1] + new + out[last_imp + 1:]
    path.write_text('\n'.join(out), encoding='utf-8')
    print('added imports:', *new, sep='\n  ')

main()
