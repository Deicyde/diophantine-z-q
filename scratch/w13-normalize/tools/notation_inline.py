"""Inline file-local notations (offline tool).

Driven by NotationUses.lean (Lean's own parser locates every use of a notation declared in the file,
with exact argument spans).  Each use is replaced by the notation's right-hand side with its
arguments substituted, parenthesised; the notation command is then deleted.  Uses nested in
arguments or in later notation right-hand sides are expanded recursively.

Also reports possible variable-capture hazards: an atomic identifier of the right-hand side that the
enclosing declaration may bind (Lean notations are hygienic; textual inlining is not).
"""
import os, sys, json, re, collections, subprocess
sys.path.insert(0, os.path.dirname(__file__))
import cmdparse, leanlex
from graph import ROOT, path_of

WORK = '/home/jackmccarthy/cloud-b3/w13/normalize/work'
TOOLS = os.path.dirname(os.path.abspath(__file__))


def run_lean_tool(files, mods_file, out):
    cmd = ['lake', 'env', 'lean', '--run', os.path.join(TOOLS, 'NotationUses.lean'), mods_file, out] + files
    env = dict(os.environ, LEAN_NUM_THREADS='2')
    r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr[-3000:])
    res = {}
    for line in open(out):
        d = json.loads(line)
        res[d['file']] = d
    return res


def byte_to_char_map(src):
    b2c = {}
    bpos = 0
    for i, ch in enumerate(src):
        b2c[bpos] = i
        bpos += len(ch.encode('utf-8'))
    b2c[bpos] = len(src)
    return b2c


class NotationDef:
    def __init__(self, c, src):
        self.c = c
        self.a, self.b = c.toks[0].a, c.toks[-1].b
        toks = c.toks
        texts = [t.text for t in toks]
        kw = c.info.get('kw')
        self.kw = kw
        self.items = []  # ('atom', s) | ('var', name)
        self.rhs_a = None
        k = next(i for i, t in enumerate(toks) if t.text == kw and t.kind == 'ident')
        j = k + 1
        if j < len(toks) and toks[j].text == ':':
            j += 2
        if kw == 'notation':
            while j < len(toks) and toks[j].text != '=>':
                t = toks[j]
                if t.kind == 'str':
                    self.items.append(('atom', cmdparse.strval(src, t).strip()))
                elif t.kind == 'ident':
                    self.items.append(('var', t.text))
                    if j + 1 < len(toks) and toks[j + 1].text == ':':
                        j += 2
                j += 1
        elif kw in ('infixl', 'infixr', 'infix', 'prefix', 'postfix'):
            t = toks[j]
            op = cmdparse.strval(src, t).strip()
            if kw == 'prefix':
                self.items = [('atom', op), ('var', '__x')]
            elif kw == 'postfix':
                self.items = [('var', '__x'), ('atom', op)]
            else:
                self.items = [('var', '__lhs'), ('atom', op), ('var', '__rhs')]
            j += 1
        elif kw == 'macro':
            self.items = []
        self.arrow = j
        self.rhs_a = toks[j + 1].a if j + 1 < len(toks) else None
        self.rhs_b = self.b
        self.vars = [x[1] for x in self.items if x[0] == 'var']
        self.atoms = [x[1] for x in self.items if x[0] == 'atom']


def subst_rhs(rhs, kw, vars_, args):
    """substitute argument texts into the rhs text"""
    if kw in ('infixl', 'infixr', 'infix'):
        return '%s (%s) (%s)' % (rhs.strip(), args[0], args[1])
    if kw in ('prefix', 'postfix'):
        return '%s (%s)' % (rhs.strip(), args[0])
    if not vars_:
        return rhs.strip()
    toks = leanlex.lex(rhs)
    out = []
    m = dict(zip(vars_, args))
    for k, a, b in toks:
        seg = rhs[a:b]
        if k == 'ident' and seg in m:
            out.append('(' + m[seg] + ')')
        else:
            out.append(seg)
    return ''.join(out).strip()


def capture_risk(decl_text, ident):
    """does the enclosing declaration possibly bind `ident` (so that textual inlining would capture it)?
    Checks: binder groups of the signature, fun/∀/∃/λ binders, let/have names, tactic binders."""
    x = re.escape(ident)
    NB = r"(?![\w'.!?\u2080-\u2089])"
    # binder groups live before the declaration's type colon (depth-0 ':' not followed by '=')
    depth = 0
    cut = len(decl_text)
    for i, ch in enumerate(decl_text):
        if ch in '([{⦃⟨':
            depth += 1
        elif ch in ')]}⦄⟩':
            depth -= 1
        elif ch == ':' and depth == 0 and not decl_text.startswith(':=', i):
            cut = i
            break
    sig = decl_text[:cut]
    pats = [
        (sig, r'[(\{⦃\[]\s*(?:[\w\'.!?₀-₉]+\s+)*' + x + NB + r'(?:\s+[\w\'.!?₀-₉]+)*\s*:(?!=)'),
        (decl_text, r'\bfun\s+(?:[\w\'.!?₀-₉⟨⟩,()\s]*\s)?' + x + NB + r'[\w\'.!?₀-₉⟨⟩,()\s:]*=>'),
        (decl_text, r'[∀∃λ]\s*(?:[\w\'.!?₀-₉]+\s+)*' + x + NB + r'[^,]*,'),
        (decl_text, r'\b(?:intro|rintro|obtain|rcases|cases|induction|set|generalize|ext|funext|choose|by_cases)\b[^\n]*?(?<![\w.])' + x + NB),
        (decl_text, r'\b(?:let|have|haveI|letI)\s+' + x + NB),
    ]
    for text, p in pats:
        if re.search(p, text):
            return p
    return None


def inline_file(path, info, src=None):
    if src is None:
        src = open(os.path.join(ROOT, path), encoding='utf-8').read()
    b2c = byte_to_char_map(src)
    toks, cmds = cmdparse.parse(src)
    defs = []

    def walk(cs):
        for x in cs:
            yield x
            if x.inner is not None:
                yield from walk([x.inner])
    allcmds = list(walk(cmds))
    for c in allcmds:
        if c.kind == 'notation':
            defs.append(NotationDef(c, src))
    kind2def = {}
    uses = []
    for u in info['uses']:
        if 'defn' in u:
            a = b2c[u['defn'][0]]
            d = next((d for d in defs if d.a <= a < d.b or d.c.toks[0].a == a), None)
            if d is None:
                raise RuntimeError('definition not matched at %d in %s' % (a, path))
            for k in u['kinds']:
                kind2def[k] = d
        else:
            if u['range'] is None:
                continue
            uses.append({'kind': u['kind'], 'a': b2c[u['range'][0]], 'b': b2c[u['range'][1]],
                         'atoms': u['atoms'],
                         'args': [(b2c[x[0]], b2c[x[1]]) if x else None for x in u['args']]})
    uses.sort(key=lambda u: (u['a'], -u['b']))
    report = {'uses': 0, 'defs': len(defs), 'risks': [], 'unmatched': []}
    # map each use to its definition
    for u in uses:
        d = kind2def.get(u['kind'])
        if d is None:
            report['unmatched'].append(u)
        u['def'] = d

    def render(a, b, inside=None):
        """source text [a,b) with all uses fully inside replaced"""
        out = []
        pos = a
        i = 0
        while i < len(uses):
            u = uses[i]
            if u['a'] >= a and u['b'] <= b and u['a'] >= pos and (u['a'], u['b']) != (a, b) and u['def'] is not None:
                out.append(src[pos:u['a']])
                out.append(expand(u))
                pos = u['b']
                # skip uses nested inside u
                j = i + 1
                while j < len(uses) and uses[j]['a'] < u['b']:
                    j += 1
                i = j
                continue
            i += 1
        out.append(src[pos:b])
        return ''.join(out)

    rhs_cache = {}

    def rhs_text(d):
        if id(d) not in rhs_cache:
            if d.kw == 'macro':
                body = src[d.rhs_a:d.rhs_b]
                m = re.match(r'\s*`\((?:tactic|term)\|\s*(.*)\)\s*$', body, re.S)
                if not m:
                    raise RuntimeError('macro rhs form not recognised: %r' % body[:200])
                rhs_cache[id(d)] = m.group(1).rstrip()
            else:
                rhs_cache[id(d)] = render(d.rhs_a, d.rhs_b)
        return rhs_cache[id(d)]

    def expand(u):
        d = u['def']
        args = [render(x[0], x[1]) for x in u['args'] if x is not None]
        report['uses'] += 1
        body = subst_rhs(rhs_text(d), d.kw, d.vars, args)
        if d.kw == 'macro':
            return '(' + body + ')'
        return '(' + body + ')'

    # build output: replace uses outside notation definitions; delete definitions
    out = []
    pos = 0
    def_spans = sorted((d.c.toks[0].a, d.b) for d in defs)
    # extend def spans to whole lines
    spans = []
    for a, b in def_spans:
        ls = src.rfind('\n', 0, a) + 1
        le = src.find('\n', b)
        le = len(src) if le < 0 else le + 1
        if src[ls:a].strip() == '' and src[b:le].strip() == '':
            spans.append((ls, le))
        else:
            spans.append((a, b))
    # capture-risk check per use
    cmd_spans = [(c.toks[0].a, c.toks[-1].b, c) for c in cmds]
    for u in uses:
        if u['def'] is None:
            continue
        d = u['def']
        rhs = rhs_text(d)
        idents = set(src2 for k, a, b in leanlex.lex(rhs) if k == 'ident' for src2 in [rhs[a:b]] if '.' not in src2)
        idents -= set(d.vars)
        enc = next((c for a, b, c in cmd_spans if a <= u['a'] < b), None)
        if enc is None or enc.kind == 'notation':
            continue
        dt = src[enc.toks[0].a:enc.toks[-1].b]
        for x in sorted(idents):
            p = capture_risk(dt, x)
            if p:
                report['risks'].append({'line': src.count('\n', 0, u['a']) + 1, 'ident': x, 'pattern': p,
                                        'decl_line': enc.line})
    # render whole file, skipping definition spans
    res = []
    pos = 0
    for a, b in spans:
        res.append(render(pos, a))
        pos = b
    res.append(render(pos, len(src)))
    return ''.join(res), report


if __name__ == '__main__':
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('files', nargs='+')
    ap.add_argument('--mods', default=os.path.join(WORK, 'mods_mathlib.txt'))
    ap.add_argument('--write', action='store_true')
    args = ap.parse_args()
    info = run_lean_tool(args.files, args.mods, os.path.join(WORK, 'nuses.jsonl'))
    for f in args.files:
        d = info[f]
        if d['errors']:
            print('TOOL ERRORS', f, d['errors'][:5])
        new, rep = inline_file(f, d)
        print(json.dumps({'file': f, 'uses': rep['uses'], 'defs': rep['defs'], 'unmatched': len(rep['unmatched']),
                          'risks': rep['risks'][:20]}, ensure_ascii=False))
        if args.write:
            open(os.path.join(ROOT, f), 'w', encoding='utf-8').write(new)
