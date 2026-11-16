#!/usr/bin/env python3
"""pi0-prune generator: copy declarations (by line range) from chain files into a new file, keeping each source
file's namespace/section/open skeleton, and rename (W/P suffixes, R1R2fpRep -> R1R2fpRepW).
Usage: gen.py CONFIG.py   (CONFIG defines OUT, HEADER, SEGMENTS=[(file, [(a,b) or (a,b,{'drop':[...]}) ...]) ...],
RENAME dict old->new (whole-word), FOOTER)."""
import re, sys
H = '/home/jackmccarthy/dzq-wt/pi0-prune/ZInQKernel/OneProof/H/'
cfg = {}
exec(open(sys.argv[1]).read(), cfg)

def lex_comment_state(lines):
    """For each line, whether it starts inside a block comment."""
    depth = 0; res = []
    for l in lines:
        res.append(depth > 0)
        i = 0
        while i < len(l):
            if depth == 0 and l.startswith('--', i): break
            if l.startswith('/-', i): depth += 1; i += 2; continue
            if depth > 0 and l.startswith('-/', i): depth -= 1; i += 2; continue
            if depth == 0 and l[i] == '"':
                j = l.find('"', i + 1); i = (j + 1) if j > 0 else len(l); continue
            i += 1
    return res

STRUCT = re.compile(r'^(noncomputable\s+)?(namespace|section|end)\b|^(open|set_option|attribute|variable|universe)\b')

def find_decl(lines, name, nodoc, fname):
    pat = re.compile(r'^(private |protected |noncomputable )*(theorem|def|structure|lemma|abbrev) ' + re.escape(name) + r'(?![\w\'.])')
    hits = [k for k, l in enumerate(lines) if pat.match(l)]
    assert len(hits) == 1, (fname, name, hits)
    k = hits[0]
    a = k
    j = k
    while j > 0 and lines[j - 1].startswith('--'): j -= 1
    if not nodoc and j > 0 and lines[j - 1].rstrip().endswith('-/'):
        t = j - 1
        while '/--' not in lines[t]: t -= 1
        a = t
    e = k
    while e + 1 < len(lines) and lines[e + 1].strip() != '': e += 1
    return a + 1, e + 1

def rename(text, ren):
    for old, new in sorted(ren.items(), key=lambda kv: -len(kv[0])):
        text = re.sub(r"(?<![\w'])" + re.escape(old) + r"(?![\w'])", new, text)
    return text

out = [cfg['HEADER']]
for fname, ranges in cfg['SEGMENTS']:
    lines = open(H + fname).read().split('\n')
    inc = lex_comment_state(lines)
    sel = {}
    for r in ranges:
        if isinstance(r[0], str):
            a, b = find_decl(lines, r[0], (r[1] if len(r) > 1 else {}).get('nodoc', False), fname)
            opts = r[1] if len(r) > 1 else {}
        else:
            a, b = r[0], r[1]
            opts = r[2] if len(r) > 2 else {}
        sel[a] = (b, opts)
    out.append(f'\n/-! ## Copied from `ZInQKernel/OneProof/H/{fname}` (base 43513d87) -/\n')
    i = 1
    n = len(lines)
    while i <= n:
        l = lines[i - 1]
        if i in sel:
            b, opts = sel[i]
            # prefix '... in' lines
            body = lines[i - 1:b]
            # drop listed fields/assignments (each a regex matching the first line; its doc comment above is dropped too)
            for pat in opts.get('drop', []):
                k = 0
                while k < len(body):
                    if re.match(pat, body[k]):
                        # remove preceding docstring lines belonging to it
                        s = k
                        if s > 0 and body[s - 1].rstrip().endswith('-/'):
                            t = s - 1
                            while t >= 0 and '/--' not in body[t]: t -= 1
                            s = t
                        e = k + 1
                        while e < len(body) and body[e].startswith('    ') : e += 1
                        del body[s:e]; k = s
                    else:
                        k += 1
            txt = '\n'.join(body)
            txt = rename(txt, cfg['RENAME'])
            for so, sn in opts.get('subs', []):
                assert so in txt, (fname, i, so)
                txt = txt.replace(so, sn)
            if 'prefix' in opts: txt = opts['prefix'] + '\n' + txt
            out.append(f'-- pi0-prune: copied from {fname}:{i}-{b}' + (f" ({opts['note']})" if 'note' in opts else ''))
            out.append(txt + '\n')
            i = b + 1
            continue
        if re.match(r'^namespace .* end ', l):
            i += 1; continue
        if not inc[i - 1] and STRUCT.match(l):
            if l.rstrip().endswith(' in') and l.startswith(('open', 'set_option', 'variable', 'attribute', 'include', 'omit')):
                # keep only if it prefixes a selected range
                if (i + 1) in sel:
                    out.append(l)
                i += 1; continue
            cmd = [l]
            j = i
            while j < n and lines[j].startswith('  ') and not inc[j] and l.startswith(('open', 'variable')):
                cmd.append(lines[j]); j += 1
            out.append('\n'.join(cmd))
            i = j + 1
            continue
        i += 1
def prune_empty(chunks):
    # chunks: list of strings; structural single entries vs content. Remove blocks with no content.
    items = []
    for c in chunks:
        first = c.split('\n')[0]
        if re.match(r'^(noncomputable\s+)?(namespace|section)\b', first): items.append(('open_blk', c))
        elif re.match(r'^end\b', first): items.append(('end', c))
        elif re.match(r'^(open|set_option|attribute|variable|universe)\b', first) and not first.rstrip().endswith(' in'): items.append(('cmd', c))
        else: items.append(('content', c))
    changed = True
    while changed:
        changed = False
        stack = []
        keep = [True] * len(items)
        for idx, (k, c) in enumerate(items):
            if k == 'open_blk': stack.append([idx, False])
            elif k == 'end':
                if stack:
                    st = stack.pop()
                    if not st[1]:
                        for j in range(st[0], idx + 1):
                            if keep[j]: keep[j] = False; changed = True
                    elif stack: stack[-1][1] = True
            elif k == 'content':
                if stack: stack[-1][1] = True
        items = [it for it, kp in zip(items, keep) if kp]
    # drop leading top-level cmds directly followed by nothing useful? keep.
    return [c for k, c in items]
head = out[0]
out = [head] + prune_empty(out[1:])
out.append(cfg.get('FOOTER', ''))
txt = '\n'.join(out)
txt = re.sub(r'\n{3,}', '\n\n', txt)
open(cfg['OUT'], 'w').write(txt)
print(cfg['OUT'], len(txt), 'bytes')
