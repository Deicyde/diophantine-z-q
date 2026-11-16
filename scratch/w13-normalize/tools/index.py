"""Static declaration index of the staged W13 Lean files (offline analysis tool).

For each file: namespaces registered, declarations (full names, private/protected flags),
instances (named, or anonymous with namespace + class head), simp-tagged names, structure/inductive
generated names.  Scope tracking follows Lean 4.35 (`namespace`/`section`/`end`, `_root_` names,
registerNamePrefixes on user-facing names).
"""
import os, sys, json, pickle, re, collections
sys.path.insert(0, os.path.dirname(__file__))
import cmdparse
from graph import ROOT, staged_files, mod_of

FLT = 'ZInQ.Contrib.CloudW03NeronSurj.FLT'
INDEX_CACHE = '/home/jackmccarthy/cloud-b3/w13/normalize/work/index.pickle'


def join(a, b):
    if not a:
        return b
    if not b:
        return a
    return a + '.' + b


def split_name(n):
    # split on '.' outside «»
    out = []
    cur = ''
    depth = 0
    for ch in n:
        if ch == '«':
            depth += 1
        elif ch == '»':
            depth -= 1
        if ch == '.' and depth == 0:
            out.append(cur); cur = ''
        else:
            cur += ch
    out.append(cur)
    return out


def parent(n):
    p = split_name(n)
    return '.'.join(p[:-1])


def name_prefixes(n):
    """registerNamePrefixes: prefixes registered for a constant n (user-facing)."""
    parts = split_name(n)
    if not parts or parts[-1].startswith('_'):
        return []
    out = []
    for k in range(len(parts) - 1, 0, -1):
        p = parts[:k]
        if any(x and x[0].isdigit() for x in p):
            break
        out.append('.'.join(p))
    return out


def full_decl_name(cur_ns, name):
    if name.startswith('_root_.'):
        return name[len('_root_.'):]
    return join(cur_ns, name)


def attr_names(items):
    """normalize attribute items: list of (kind, name, extra) with kind in global/scoped/local"""
    out = []
    for it in items:
        if not it:
            continue
        kind = 'global'
        k = 0
        if it[0] in ('scoped', 'local'):
            kind = it[0]; k = 1
        if k >= len(it):
            continue
        out.append((kind, it[k], it[k + 1:]))
    return out


class FileIndex:
    def __init__(self, path):
        self.path = path
        self.mod = mod_of(path)
        self.imports = []
        self.ns = set()            # namespaces registered
        self.consts = {}           # full name -> dict(private, protected, kind)
        self.inst = {}             # instance full name -> kind (global/scoped:NS/local)
        self.anon_inst = []        # (namespace, class head, kind, line)
        self.simp = {}             # name -> kind
        self.simps_prefix = []     # (full name, attr text) for @[simps] etc.
        self.notations = []        # (line, kind)
        self.errors = []


def class_head(c, src):
    """class head of an instance declaration: first identifier after the top-level ':' """
    toks = c.toks
    depth = 0
    k = c.info.get('name_tok') or 0
    # find kw index
    started = False
    for i, t in enumerate(toks):
        if t.kind == 'ident' and t.text == 'instance':
            started = True
            k = i + 1
            break
    if not started:
        return None
    for i in range(k, len(toks)):
        x = toks[i].text
        if x in ('(', '[', '{', '⦃', '⟨'):
            depth += 1
        elif x in (')', ']', '}', '⦄', '⟩'):
            depth -= 1
        elif x == ':' and depth == 0:
            for j in range(i + 1, min(i + 6, len(toks))):
                if toks[j].kind == 'ident':
                    return toks[j].text
                if toks[j].text in ('(', '@'):
                    continue
            return None
        elif x in (':=', 'where') and depth == 0:
            return None
    return None


def structure_fields(c, src):
    """(ctor name, [fields], [parents]) for a structure/class declaration (best effort)."""
    toks = c.toks
    # locate 'where'
    wi = None
    ext = []
    depth = 0
    kwi = None
    for i, t in enumerate(toks):
        if t.kind == 'ident' and t.text in ('structure', 'class') and kwi is None:
            kwi = i
            continue
        if kwi is None:
            continue
        x = t.text
        if x in ('(', '[', '{', '⦃'):
            depth += 1
        elif x in (')', ']', '}', '⦄'):
            depth -= 1
        elif depth == 0 and x == 'extends':
            # parents until 'where' or ':'
            j = i + 1
            d2 = 0
            curp = None
            while j < len(toks) and not (d2 == 0 and toks[j].text in ('where', ':=')):
                y = toks[j].text
                if y in ('(', '[', '{'):
                    d2 += 1
                elif y in (')', ']', '}'):
                    d2 -= 1
                elif d2 == 0 and y == ',':
                    curp = None
                elif d2 == 0 and toks[j].kind == 'ident' and curp is None:
                    curp = y
                    ext.append(y)
                j += 1
        elif depth == 0 and x == 'where':
            wi = i
            break
    ctor = 'mk'
    fields = []
    if wi is not None:
        body = toks[wi + 1:]
        if len(body) >= 2 and body[0].kind == 'ident' and body[1].text == '::':
            ctor = body[0].text
            body = body[2:]
        if body:
            # field lines: tokens that start a line, at the minimal indentation
            line_first = {}
            for t in body:
                if t.line not in line_first:
                    line_first[t.line] = t
            firsts = list(line_first.values())
            # also first token right after where on the same line
            if firsts:
                col = min(t.col for t in firsts if t.kind in ('ident', 'sym'))
                for t in firsts:
                    if t.col == col:
                        if t.kind == 'ident' and t.text not in ('deriving',):
                            fields.append(t.text)
                        elif t.text == '(':
                            pass
    return ctor, fields, ext


def inductive_ctors(c):
    toks = c.toks
    out = []
    for i, t in enumerate(toks):
        if t.text == '|' and i + 1 < len(toks) and toks[i + 1].kind == 'ident':
            # only constructor bars at line start
            if i == 0 or toks[i - 1].line != t.line:
                out.append(toks[i + 1].text)
    return out


def decl_events(c, ns, src):
    """events of one declaration command in namespace ns:
    ('const', name, private, protected, kind) | ('ns', name) | ('inst', name, kind) |
    ('anon_inst', ns, head, kind, line, private) | ('simp', name, kind) | ('simps', name, attr, extra)"""
    ev = []

    def add_const(n, private=False, protected=False, kind=''):
        ev.append(('const', n, private, protected, kind))

    def add_ns(n):
        if n:
            ev.append(('ns', n))

    kw = c.info['kw']
    mods = c.info['mods']
    private = 'private' in mods
    protected = 'protected' in mods
    attrs = attr_names(c.info['attrs'])
    name = c.info.get('name')
    if kw == 'alias':
        names = c.info.get('alias_names') or ([name] if name else [])
        for nm in names:
            add_const(full_decl_name(ns, nm), private, protected, 'alias')
        return ev
    if kw == 'example':
        return ev
    if kw == 'instance':
        ikind = 'global'
        if 'scoped' in mods:
            ikind = 'scoped:' + ns
        elif 'local' in mods:
            ikind = 'local'
        if name:
            fn = full_decl_name(ns, name)
            add_const(fn, private, protected, 'instance')
            ev.append(('inst', fn, ikind))
            for k2, an, extra in attrs:
                if an == 'simp':
                    ev.append(('simp', fn, k2))
        else:
            ev.append(('anon_inst', ns, class_head(c, src), ikind, c.line, private))
        return ev
    if not name:
        return ev
    fn = full_decl_name(ns, name)
    add_const(fn, private, protected, kw)
    for k2, an, extra in attrs:
        if an == 'simp':
            ev.append(('simp', fn, k2))
        elif an == 'instance':
            ev.append(('inst', fn, k2 if k2 != 'scoped' else 'scoped:' + ns))
        elif an in ('simps', 'simps!', 'reassoc', 'elementwise', 'to_additive', 'ext', 'mk_iff'):
            ev.append(('simps', fn, an, ' '.join(extra)))
            if an == 'reassoc':
                add_const(fn + '_assoc', private, protected, 'reassoc')
                if 'simp' in extra:
                    ev.append(('simp', fn + '_assoc', 'global'))
            if an == 'ext' and kw in ('structure', 'class'):
                add_const(fn + '.ext', private, False, 'ext')
                add_const(fn + '.ext_iff', private, False, 'ext')
    if kw in ('structure', 'class'):
        ctor, fields, parents = structure_fields(c, src)
        add_ns(fn)
        for aux in ('rec', 'casesOn', 'recOn', 'noConfusion', 'noConfusionType', ctor,
                    ctor + '.injEq', ctor + '.inj', ctor + '.sizeOf_spec', ctor + '.noConfusion'):
            add_const(fn + '.' + aux, private, aux in ('rec', 'casesOn', 'recOn', 'noConfusion',
                                                       'noConfusionType'), 'aux')
        ev.append(('simp', fn + '.' + ctor + '.injEq', 'global'))
        ev.append(('simp', fn + '.' + ctor + '.sizeOf_spec', 'global'))
        for fl in fields:
            add_const(fn + '.' + fl, private, False, 'proj')
        for p in parents:
            last = split_name(p)[-1]
            add_const(fn + '.to' + last, private, False, 'parentproj')
            if kw == 'class':
                ev.append(('inst', fn + '.to' + last, 'global'))
    elif kw in ('inductive', 'class inductive'):
        add_ns(fn)
        for aux in ('rec', 'casesOn', 'recOn', 'noConfusion', 'noConfusionType', 'below', 'brecOn'):
            add_const(fn + '.' + aux, private, True, 'aux')
        for ct in inductive_ctors(c):
            add_const(fn + '.' + ct, private, False, 'ctor')
            add_const(fn + '.' + ct + '.injEq', private, False, 'aux')
            add_const(fn + '.' + ct + '.inj', private, False, 'aux')
            add_const(fn + '.' + ct + '.sizeOf_spec', private, False, 'aux')
            ev.append(('simp', fn + '.' + ct + '.injEq', 'global'))
            ev.append(('simp', fn + '.' + ct + '.sizeOf_spec', 'global'))
    return ev


def index_file(path):
    src = open(os.path.join(ROOT, path), encoding='utf-8').read()
    fi = FileIndex(path)
    toks, cmds = cmdparse.parse(src)
    stack = []  # list of (kind, header, ns)

    def cur_ns():
        return stack[-1][2] if stack else ''

    def add_ns(n):
        if n:
            fi.ns.add(n)

    def add_const(n, private=False, protected=False, kind=''):
        fi.consts[n] = {'private': private, 'protected': protected, 'kind': kind}
        for p in name_prefixes(n):
            add_ns(p)

    def walk(c):
        if c.kind == 'import':
            fi.imports.append(c.info['mod'])
        elif c.kind == 'namespace':
            for comp in split_name(c.info['name']):
                ns = join(cur_ns(), comp)
                stack.append(('namespace', comp, ns))
                add_ns(ns)
        elif c.kind == 'section':
            if c.info['name']:
                for comp in split_name(c.info['name']):
                    stack.append(('section', comp, cur_ns()))
            else:
                stack.append(('section', '', cur_ns()))
        elif c.kind == 'end':
            n = c.info['name']
            k = len(split_name(n)) if n else 1
            for _ in range(k):
                if stack:
                    stack.pop()
                else:
                    fi.errors.append(('end-underflow', c.line))
        elif c.kind == 'decl':
            decl(c)
        elif c.kind == 'attribute':
            for kind, an, extra in attr_names(c.info['attrs']):
                for nm in c.info['names']:
                    if an == 'simp':
                        fi.simp.setdefault(('?', cur_ns(), nm), kind)
                    elif an == 'instance':
                        fi.inst.setdefault(('?', cur_ns(), nm), kind)
        elif c.kind == 'notation':
            fi.notations.append((c.line, c.info.get('kw'), c.info.get('mods')))
        if c.inner is not None:
            walk(c.inner)

    def decl(c):
        for e in decl_events(c, cur_ns(), src):
            if e[0] == 'const':
                fi.consts[e[1]] = {'private': e[2], 'protected': e[3], 'kind': e[4]}
                for p in name_prefixes(e[1]):
                    add_ns(p)
            elif e[0] == 'ns':
                add_ns(e[1])
            elif e[0] == 'inst':
                fi.inst[e[1]] = e[2]
            elif e[0] == 'simp':
                fi.simp[e[1]] = e[2]
            elif e[0] == 'anon_inst':
                fi.anon_inst.append(e[1:])
            elif e[0] == 'simps':
                fi.simps_prefix.append(e[1:])

    for c in cmds:
        walk(c)
    if stack:
        fi.errors.append(('unclosed', [s[1] for s in stack]))
    return fi


def build_index(force=False):
    if not force and os.path.exists(INDEX_CACHE):
        return pickle.load(open(INDEX_CACHE, 'rb'))
    idx = {}
    for p in staged_files():
        idx[mod_of(p)] = index_file(p)
    pickle.dump(idx, open(INDEX_CACHE, 'wb'))
    return idx


if __name__ == '__main__':
    import time
    t = time.time()
    import index as _ix; idx = _ix.build_index(force=True)
    print('indexed', len(idx), time.time() - t)
    errs = [(m, fi.errors) for m, fi in idx.items() if fi.errors]
    print('files with scope errors', len(errs))
    for e in errs[:10]:
        print(e)
    print('consts', sum(len(fi.consts) for fi in idx.values()), 'anon inst', sum(len(fi.anon_inst) for fi in idx.values()),
          'named inst', sum(len(fi.inst) for fi in idx.values()), 'ns', sum(len(fi.ns) for fi in idx.values()))
