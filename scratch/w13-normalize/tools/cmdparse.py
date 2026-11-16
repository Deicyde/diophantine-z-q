"""Command-level parser for the W13 staged Lean sources (offline analysis tool).

Splits a Lean 4 file into top-level commands using the lexer in leanlex.py.  A command starts
at a column-0 token that is a command keyword (or `@[`, `#cmd`, a doc comment), or directly after a
structural one-line command (namespace/end/section/open/export/port command) on the same line.
For structural commands the arguments are parsed exactly as Lean's grammar would (with the
checkColGt rule for `open`); declarations are parsed only far enough to learn their names,
modifiers and attributes.
"""
import re
from leanlex import lex, is_id_first

STRUCT_KW = {'namespace', 'section', 'end', 'open', 'export', 'universe', 'variable', 'set_option',
             'attribute', 'import', 'include', 'omit', 'mutual', 'deriving', 'initialize', 'module',
             'suppress_compilation', 'unseal', 'seal'}
DECL_MOD = {'private', 'protected', 'public', 'noncomputable', 'unsafe', 'partial', 'nonrec', 'scoped', 'local',
            'meta'}
DECL_KW = {'theorem', 'lemma', 'def', 'abbrev', 'instance', 'structure', 'class', 'inductive', 'example',
           'opaque', 'axiom', 'irreducible_def', 'alias'}
NOTATION_KW = {'notation', 'infix', 'infixl', 'infixr', 'prefix', 'postfix', 'macro', 'macro_rules', 'syntax',
               'elab', 'elab_rules', 'declare_syntax_cat'}
SHIM_KW = {'r2nos_open_dual', 'r2nos_namespace_dual', 'r2nos_open_scoped_dual', 'r2nos_open_scoped',
           'r2nos_erase_attr', 'r2nos_alias', 'w03_open', 'w03_export', 'w03_export_all', 'w03_reactivate',
           'w03_ns', 'w03_alias', 'p2m_open', 'p2m_export', 'p2m_alias', 'p2m_reactivate', 'p2m_open_scoped',
           'p2m_ns', 'p2m_export_all'}
HASH_CMDS = {'#print', '#check', '#eval', '#r2nos_type_eq_warn', '#p2m_type_eq', '#p2m_type_eq_warn', '#exit',
             '#guard_msgs', '#lint', '#synth', '#reduce', '#help', '#where', '#time', '#find'}
START_KW = STRUCT_KW | DECL_MOD | DECL_KW | NOTATION_KW | SHIM_KW


class Tok:
    __slots__ = ('kind', 'a', 'b', 'text', 'line', 'col')

    def __init__(self, kind, a, b, text, line, col):
        self.kind, self.a, self.b, self.text, self.line, self.col = kind, a, b, text, line, col

    def __repr__(self):
        return 'Tok(%s,%r,%d:%d)' % (self.kind, self.text, self.line, self.col)


def tokens(src):
    """code tokens (no ws/comments) with line/col, plus doc comments as kind 'doc'.
    Merges `@[`, `#name`, `:=`, `=>` into single symbol tokens."""
    raw = lex(src)
    out = []
    line = 1
    lstart = 0
    pos = 0
    nraw = len(raw)
    idx = 0
    while idx < nraw:
        k, a, b = raw[idx]
        seg = src[pos:a]
        nl = seg.count('\n')
        if nl:
            line += nl
            lstart = pos + seg.rfind('\n') + 1
        pos = a
        idx += 1
        if k in ('ws', 'comment', 'moddoc'):
            continue
        text = src[a:b]
        if k == 'sym' and idx < nraw:
            k2, a2, b2 = raw[idx]
            if a2 == b:
                t2 = src[a2:b2]
                if (text == '@' and t2 == '[') or (text == ':' and t2 == '=') or (text == '=' and t2 == '>') \
                        or (text == '#' and k2 == 'ident') or (text == '#' and t2 == '['):
                    text = text + t2
                    b = b2
                    idx += 1
        out.append(Tok(k, a, b, text, line, a - lstart))
    return out


class Cmd:
    def __init__(self, kind, toks, i0, i1):
        self.kind = kind        # e.g. 'namespace', 'decl', 'shim', 'open', ...
        self.toks = toks[i0:i1]
        self.i0, self.i1 = i0, i1
        self.info = {}
        self.inner = None       # for `... in` combinators: the wrapped command

    @property
    def a(self):
        return self.toks[0].a

    @property
    def b(self):
        return self.toks[-1].b

    @property
    def line(self):
        return self.toks[0].line

    def __repr__(self):
        return 'Cmd(%s,L%d,%r)' % (self.kind, self.line, self.info)


def is_cmd_start(t, prev):
    if t.kind == 'doc':
        return t.col == 0
    if t.col != 0:
        return False
    if t.kind == 'ident':
        return t.text in START_KW
    if t.kind == 'sym':
        return t.text == '@[' or t.text in HASH_CMDS or t.text.startswith('#')
    return False


def strval(src, t):
    """value of a simple string literal token (no escapes beyond \\\" and \\\\)."""
    s = src[t.a:t.b]
    assert s[0] == '"' and s[-1] == '"', s
    body = s[1:-1]
    return body.replace('\\"', '"').replace('\\\\', '\\')


def parse(src):
    toks = tokens(src)
    n = len(toks)
    # 1. find column-0 command starts
    starts = [i for i, t in enumerate(toks) if is_cmd_start(t, toks[i - 1] if i else None)]
    # doc comments attach to the following command start
    cmds = []
    si = 0
    i = 0
    boundaries = starts + [n]
    for k in range(len(starts)):
        i0, i1 = boundaries[k], boundaries[k + 1]
        cmds.extend(split_chunk(src, toks, i0, i1))
    # merge attribute-/modifier-only chunks (e.g. `@[simp]` on its own line) into the next command
    cmds2 = []
    carry = None
    for c in cmds:
        if carry is not None:
            if c.kind in ('decl', 'notation', 'other'):
                c.toks = carry.toks + c.toks
                c.i0 = carry.i0
                c.info['attrs'] = carry.info.get('attrs', []) + c.info.get('attrs', [])
                c.info['mods'] = carry.info.get('mods', []) + c.info.get('mods', [])
                if c.kind == 'decl' and c.info.get('name_tok') is not None:
                    c.info['name_tok'] += len(carry.toks)
                if 'doc' in carry.info:
                    c.info['doc'] = carry.info['doc']
            else:
                cmds2.append(carry)
            carry = None
            if c.kind == 'other' and c.info.get('attr_only'):
                carry = c
                continue
            cmds2.append(c)
            continue
        if c.kind == 'other' and c.info.get('attr_only'):
            carry = c
            continue
        cmds2.append(c)
    if carry is not None:
        cmds2.append(carry)
    cmds = cmds2
    # merge doc comments into following command
    merged = []
    pend = None
    for c in cmds:
        if c.kind == 'doc':
            if pend is not None:
                merged.append(pend)
            pend = c
            continue
        if pend is not None:
            if c.kind in ('decl', 'notation', 'other'):
                c.info['doc'] = (pend.a, pend.b)
                c.toks = pend.toks + c.toks
                c.i0 = pend.i0
            else:
                merged.append(pend)
            pend = None
        merged.append(c)
    if pend is not None:
        merged.append(pend)
    # attach `in` combinators (right-nested: `open A in` `shim "A" in` `theorem ...`)
    out = []
    j = len(merged) - 1
    stack = []
    for c in reversed(merged):
        if c.info.get('in') and stack:
            c.inner = stack.pop()
        stack.append(c)
    out = list(reversed(stack))
    return toks, out


def ident_ok(t):
    return t.kind == 'ident'


def split_chunk(src, toks, i0, i1):
    """parse the chunk toks[i0:i1] (a column-0 command start up to the next one) into commands."""
    res = []
    i = i0
    while i < i1:
        c, j = parse_one(src, toks, i, i1)
        res.append(c)
        if j <= i:
            j = i + 1
        i = j
    return res


def parse_one(src, toks, i, i1):
    t = toks[i]
    w = t.text
    if t.kind == 'doc':
        c = Cmd('doc', toks, i, i + 1)
        return c, i + 1
    if t.kind == 'ident' and w == 'namespace' and i + 1 < i1 and toks[i + 1].kind == 'ident':
        c = Cmd('namespace', toks, i, i + 2)
        c.info['name'] = toks[i + 1].text
        return c, i + 2
    if t.kind == 'ident' and w == 'end':
        j = i + 1
        if j < i1 and toks[j].kind == 'ident' and toks[j].line == t.line and toks[j].text not in START_KW:
            c = Cmd('end', toks, i, j + 1)
            c.info['name'] = toks[j].text
            return c, j + 1
        c = Cmd('end', toks, i, i + 1)
        c.info['name'] = None
        return c, i + 1
    if t.kind == 'ident' and w in ('section', 'noncomputable', 'public') and (
            w == 'section' or (i + 1 < i1 and toks[i + 1].text == 'section')):
        j = i + 1 if w == 'section' else i + 2
        c_nc = (w == 'noncomputable')
        c_pub = (w == 'public')
        name = None
        if j < i1 and toks[j].kind == 'ident' and toks[j].line == toks[j - 1].line and toks[j].text not in START_KW:
            name = toks[j].text
            j += 1
        c = Cmd('section', toks, i, j)
        c.info.update(name=name, noncomputable=c_nc, public=c_pub)
        return c, j
    if t.kind == 'ident' and w == 'open':
        return parse_open(src, toks, i, i1)
    if t.kind == 'ident' and w == 'export':
        # export NS (ids*)
        j = i + 1
        ns = toks[j].text
        j += 1
        assert toks[j].text == '(', (src[t.a:t.a + 200])
        j += 1
        ids = []
        while toks[j].text != ')':
            ids.append(toks[j].text)
            j += 1
        c = Cmd('export', toks, i, j + 1)
        c.info.update(ns=ns, ids=ids)
        return c, j + 1
    if t.kind == 'ident' and w in SHIM_KW:
        j = i + 1
        args = []
        while j < i1 and toks[j].kind == 'str' and toks[j].line == t.line:
            args.append(strval(src, toks[j]))
            j += 1
        c = Cmd('shim', toks, i, j)
        c.info.update(name=w, args=args)
        if j < i1 and toks[j].text == 'in' and toks[j].line == t.line:
            c.info['in'] = True
            c.toks = toks[i:j + 1]
            c.i1 = j + 1
            return c, j + 1
        return c, j
    if t.kind == 'sym' and w.startswith('#'):
        c = Cmd('hash', toks, i, i1)
        c.info['name'] = w
        return c, i1
    if t.kind == 'ident' and w == 'import':
        c = Cmd('import', toks, i, i + 2)
        c.info['mod'] = toks[i + 1].text
        return c, i + 2
    if t.kind == 'ident' and w == 'public' and i + 1 < i1 and toks[i + 1].text == 'import':
        c = Cmd('import', toks, i, i + 3)
        c.info['mod'] = toks[i + 2].text
        c.info['public'] = True
        return c, i + 3
    if t.kind == 'ident' and w == 'module' and i + 1 == i1:
        c = Cmd('module', toks, i, i + 1)
        return c, i + 1
    if t.kind == 'ident' and w in ('universe', 'variable', 'set_option', 'include', 'omit', 'attribute',
                                   'mutual', 'deriving', 'initialize', 'suppress_compilation', 'unseal', 'seal'):
        c = Cmd(w, toks, i, i1)
        if w == 'set_option' or w == 'attribute' or w == 'variable' or w == 'omit' or w == 'include':
            # `... in` combinator?  (the `in` keyword ends the chunk line)
            last = toks[i1 - 1]
            if last.text == 'in' and last.kind == 'ident':
                c.info['in'] = True
        if w == 'attribute':
            parse_attribute(src, c)
        return c, i1
    # declarations / notation / other
    return parse_decl(src, toks, i, i1)


def parse_open(src, toks, i, i1):
    t = toks[i]
    j = i + 1
    info = {}
    if j < i1 and toks[j].text == 'scoped' and toks[j].kind == 'ident':
        info['form'] = 'scoped'
        j += 1
    else:
        info['form'] = 'simple'
    names = []
    # checkColGt: tokens must be at column > column of `open`
    while j < i1 and toks[j].kind == 'ident' and (toks[j].line == t.line or toks[j].col > t.col) and toks[j].text not in ('in', 'hiding', 'renaming') and toks[j].text not in START_KW:
        names.append(toks[j].text)
        j += 1
    info['names'] = names
    if j < i1 and toks[j].text == 'hiding':
        info['form'] = 'hiding'
        j += 1
        hid = []
        while j < i1 and toks[j].kind == 'ident' and (toks[j].line == t.line or toks[j].col > t.col) and toks[j].text not in ('in',) and toks[j].text not in START_KW:
            hid.append(toks[j].text)
            j += 1
        info['hiding'] = hid
    elif j < i1 and toks[j].text == '(' and info['form'] == 'simple' and len(names) == 1:
        info['form'] = 'explicit'
        j += 1
        ids = []
        while toks[j].text != ')':
            ids.append(toks[j].text)
            j += 1
        j += 1
        info['ids'] = ids
    elif j < i1 and toks[j].text == 'renaming':
        info['form'] = 'renaming'
        j += 1
        ren = []
        while j < i1 and (toks[j].line == t.line or toks[j].col > t.col) and toks[j].text != 'in':
            ren.append(toks[j].text)
            j += 1
        info['renaming'] = ren
    if j < i1 and toks[j].text == 'in' and toks[j].kind == 'ident':
        info['in'] = True
        j += 1
    c = Cmd('open', toks, i, j)
    c.info.update(info)
    return c, j


def skip_balanced(toks, j, i1, open_='[', close=']'):
    depth = 0
    while j < i1:
        x = toks[j].text
        if x in ('[', '@[', '(', '{', '⟨', '⦃', '#['):
            depth += 1
        elif x in (']', ')', '}', '⟩', '⦄'):
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return j


def attr_items(src, toks, j, i1):
    """toks[j] is '@[' or '['; return (items, next) where items are lists of token texts."""
    k = skip_balanced(toks, j, i1)
    inner = toks[j + 1:k - 1]
    items = []
    cur = []
    depth = 0
    for t in inner:
        x = t.text
        if x in ('[', '(', '{', '⟨', '#['):
            depth += 1
        elif x in (']', ')', '}', '⟩'):
            depth -= 1
        if x == ',' and depth == 0:
            items.append(cur); cur = []
            continue
        cur.append(x)
    if cur:
        items.append(cur)
    return items, k


def parse_attribute(src, c):
    toks = c.toks
    j = 1
    items, k = attr_items(src, toks, j, len(toks))
    names = []
    while k < len(toks) and toks[k].kind == 'ident' and toks[k].text != 'in':
        names.append(toks[k].text)
        k += 1
    c.info.update(attrs=items, names=names)


def parse_decl(src, toks, i, i1):
    j = i
    attrs = []
    mods = []
    while j < i1:
        t = toks[j]
        if t.text == '@[':
            items, j = attr_items(src, toks, j, i1)
            attrs.extend(items)
            continue
        if t.kind == 'ident' and t.text in DECL_MOD:
            mods.append(t.text)
            j += 1
            continue
        break
    if j >= i1:
        c = Cmd('other', toks, i, i1)
        c.info.update(mods=mods, attrs=attrs, attr_only=True)
        return c, i1
    t = toks[j]
    kw = t.text
    if kw == 'class' and j + 1 < i1 and toks[j + 1].text == 'inductive':
        kw = 'class inductive'
        j += 1
    if t.kind == 'ident' and (kw in DECL_KW or kw == 'class inductive'):
        c = Cmd('decl', toks, i, i1)
        c.info.update(mods=mods, attrs=attrs, kw=kw)
        k = j + 1
        name = None
        if kw == 'instance':
            if k < i1 and toks[k].text == '(' and k + 1 < i1 and toks[k + 1].text == 'priority':
                k = skip_balanced(toks, k, i1)
            if k < i1 and toks[k].kind == 'ident' and toks[k].text not in ('where',):
                name = toks[k].text
        elif kw == 'example':
            name = None
        elif kw == 'alias':
            if k < i1 and toks[k].text == '⟨':
                # alias ⟨a, b⟩ := foo
                names = []
                k2 = k + 1
                while toks[k2].text != '⟩':
                    if toks[k2].kind == 'ident':
                        names.append(toks[k2].text)
                    k2 += 1
                c.info['alias_names'] = names
            elif k < i1 and toks[k].kind == 'ident':
                name = toks[k].text
        else:
            if k < i1 and toks[k].kind == 'ident':
                name = toks[k].text
        c.info['name'] = name
        c.info['name_tok'] = k if name else None
        return c, i1
    if t.kind == 'ident' and kw in NOTATION_KW:
        c = Cmd('notation', toks, i, i1)
        c.info.update(mods=mods, attrs=attrs, kw=kw)
        return c, i1
    c = Cmd('other', toks, i, i1)
    c.info.update(mods=mods, attrs=attrs)
    return c, i1
