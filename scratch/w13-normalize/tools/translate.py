"""Translate the W13 port commands of a staged file into ordinary Lean (offline tool).

Usage: python3 translate.py [--write] MODULE...   (or --cone ROOTMOD..., or --all)
Writes nothing unless --write.  Produces work/translate/<module>.json with decisions and residuals.
"""
import os, sys, re, json, collections, argparse
sys.path.insert(0, os.path.dirname(__file__))
import cmdparse
import leanlex
from sim import (Graph, Facts, State, SimError, PREFIX, other_half, strip_root, join, split_name,
                 name_parents, dedup, is_atomic)
from index import decl_events, name_prefixes, attr_names
from graph import ROOT, staged_files, mod_of, path_of

WORK = '/home/jackmccarthy/cloud-b3/w13/normalize/work'
PORTUTIL = 'ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil'
PORTUTILEXT = 'ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt'
FQ_PREFIX = 'ZInQKernel.Contrib.CloudB3W13Shared.FiniteQuotient'

ID_FULL = re.compile('^' + leanlex.IDENT_RE.pattern + '$')


def ident(n):
    """render a Name as identifier syntax"""
    parts = split_name(n)
    out = []
    for p in parts:
        if re.match('^' + leanlex.ID_PART + '$', p) and p not in ('in', 'at', 'by', 'do', 'then', 'else', 'fun', 'have',
                                                                  'show', 'from', 'let', 'if', 'match', 'with',
                                                                  'end', 'open', 'where', 'deriving', 'instance',
                                                                  'class', 'structure', 'theorem', 'def', 'example'):
            out.append(p)
        else:
            out.append('«' + p + '»')
    return '.'.join(out)


def root_ident(n):
    return '_root_.' + ident(n)


class Translator:
    def __init__(self, G, mod, oracle=None):
        self.G = G
        self.mod = mod
        self.path = path_of(mod)
        self.src = open(os.path.join(ROOT, self.path), encoding='utf-8').read()
        self.toks, self.cmds = cmdparse.parse(self.src)
        self.F = Facts(G, mod)
        self.S = State(self.F)
        self.T = State(self.F)
        self.edits = []      # (a, b, text)
        self.res = []        # residuals
        self.counts = collections.Counter()
        self.decisions = []
        self.inert = []      # (kind, ns) opened/activated in S but nonexistent
        self.oracle = oracle
        self.imports = [c.info['mod'] for c in self.cmds if c.kind == 'import']

    # ------------------------------------------------------------------ helpers
    def residual(self, c, kind, detail):
        self.res.append({'line': c.line if c is not None else None, 'kind': kind, 'detail': detail})

    def norm_ods(self, ods):
        out = set()
        for od in ods:
            if od[0] == 's':
                hid = frozenset(h for h in od[2] if self.hidden_exists(od[1], h))
                out.add(('s', od[1], hid))
            else:
                out.add(od)
        return out

    def hidden_exists(self, ns, h):
        rid = join(ns, h)
        return self.F.contains(rid) or self.F.private(rid)

    def delta(self):
        S, T = self.S.top, self.T.top
        sods, tods = self.norm_ods(S.ods), self.norm_ods(T.ods)
        add_ods = [od for od in S.ods if self.norm_od(od) in (sods - tods)]
        extra_ods = tods - sods
        add_act = S.active - T.active
        extra_act = T.active - S.active
        return add_ods, extra_ods, add_act, extra_act

    def norm_od(self, od):
        if od[0] == 's':
            return ('s', od[1], frozenset(h for h in od[2] if self.hidden_exists(od[1], h)))
        return od

    def plan_fix(self, c):
        """plain commands bringing T's top scope to S's: returns list of command dicts"""
        add_ods, extra_ods, add_act, extra_act = self.delta()
        cmds = []
        simple = []
        seen = set()
        for od in reversed(add_ods):
            if od[0] != 's':
                self.residual(c, 'explicit-od', str(od))
                continue
            ns, hid = od[1], od[2]
            if not self.F.is_ns(ns):
                continue
            hidx = [h for h in sorted(hid) if self.hidden_exists(ns, h)]
            key = (ns, tuple(hidx))
            if key in seen:
                continue
            seen.add(key)
            if hidx:
                cmds.append({'form': 'hiding', 'names': ['_root_.' + ns], 'hiding': hidx})
            else:
                simple.append(ns)
        if simple:
            cmds.insert(0, {'form': 'simple', 'names': ['_root_.' + n for n in simple]})
        # activations not covered by the opens above
        covered = set(simple) | {cm['names'][0][7:] for cm in cmds if cm['form'] == 'hiding'}
        sc = []
        for n in sorted(add_act - covered):
            if not self.F.is_ns(n):
                continue
            sc.append(n)
        if sc:
            cmds.append({'form': 'scoped', 'names': ['_root_.' + n for n in sc]})
        if extra_ods:
            self.residual(c, 'extra-od-in-T', sorted(map(str, extra_ods)))
        if extra_act:
            self.residual(c, 'extra-activation-in-T', sorted(extra_act))
        return cmds

    def render_open(self, cm, in_=False):
        names = ' '.join(root_ident(n[7:]) if n.startswith('_root_.') else ident(n) for n in cm['names'])
        if cm['form'] == 'simple':
            s = 'open ' + names
        elif cm['form'] == 'scoped':
            s = 'open scoped ' + names
        elif cm['form'] == 'hiding':
            s = 'open ' + names + ' hiding ' + ' '.join(ident(h) for h in cm['hiding'])
        else:
            raise ValueError(cm)
        return s + (' in' if in_ else '')

    def apply_T_open(self, cm, c):
        try:
            self.T.cmd_open(cm)
        except SimError as e:
            self.residual(c, 'T-open-failed', str(e))

    def check_equal(self, c, what):
        add_ods, extra_ods, add_act, extra_act = self.delta()
        add_real = [od for od in add_ods if od[0] != 's' or self.F.is_ns(od[1])]
        act_real = [n for n in add_act if self.F.is_ns(n)]
        if add_real or extra_ods or act_real or extra_act:
            self.residual(c, 'state-mismatch-after-' + what,
                          {'missing_od': [str(x) for x in add_real], 'extra_od': [str(x) for x in extra_ods],
                           'missing_act': sorted(act_real), 'extra_act': sorted(extra_act)})

    # ------------------------------------------------------------------ S semantics of port commands
    def S_open_dual(self, s, scoped_only):
        S, F = self.S, self.F
        for w in s.split(' '):
            if not w:
                continue
            parts = w.split('~')
            n = parts[0]
            hidden = frozenset(h for h in parts[1:] if h)
            cands = S.resolve_ns(strip_root(n) if n.startswith('_root_.') else n)
            if n.startswith('_root_.'):
                cands = [strip_root(n)] + cands
            for cnd in cands:
                k = other_half(cnd)
                if not k:
                    continue
                if F.is_ns(k) or k == PREFIX or k.startswith(PREFIX + '.'):
                    if not scoped_only:
                        od = ('s', k, hidden)
                        if od not in S.top.ods:
                            S.top.ods.insert(0, od)
                    S.activate(k)

    def S_namespace_dual(self):
        S, F = self.S, self.F
        for sc in S.scopes:
            ns = sc.ns
            if not ns.startswith(PREFIX + '.'):
                continue
            rel = ns[len(PREFIX) + 1:]
            acc = ''
            for comp in split_name(rel):
                acc = join(acc, comp)
                od = ('s', acc, frozenset())
                if F.is_ns(acc) and od not in sc.ods:
                    sc.ods.insert(0, od)
        cur = S.ns
        if cur.startswith(PREFIX + '.'):
            rel = cur[len(PREFIX) + 1:]
            acc = ''
            for comp in split_name(rel):
                acc = join(acc, comp)
                if F.is_ns(acc):
                    S.activate(acc)

    def S_open_scoped(self, s):
        for w in s.split(' '):
            if not w:
                continue
            ns = w.split('~')[0]
            for n in (ns, join(PREFIX, ns)):
                self.S.activate(n)

    def S_w03_open(self, s):
        S = self.S
        for w in s.split(' '):
            if not w:
                continue
            parts = w.split('~')
            ns = parts[0]
            hidden = frozenset(h for h in parts[1:] if h)
            for n in (ns, join(PREFIX, ns)):
                S.top.ods.insert(0, ('s', n, hidden))
                S.activate(n)

    def S_w03_reactivate(self, s):
        for w in s.split(' '):
            if not w:
                continue
            self.S.activate(join(PREFIX, w))

    def S_w03_export(self, n, m):
        S, F = self.S, self.F
        cur = S.ns
        made = []
        for w in m.split(' '):
            if not w:
                continue
            full = join(join(PREFIX, n), w)
            glob = join(n, w)
            if F.contains(full):
                t = full
            elif F.contains(glob):
                t = glob
            elif F.private(full):
                t = '_private:' + full
            else:
                self.counts['w03_export-skip'] += 1
                continue
            a = join(cur, w)
            S.aliases[a].append(t)
            made.append((a, t, w))
        return made

    def S_w03_export_all(self, n, s):
        S, F = self.S, self.F
        base = join(join(PREFIX, n), s)
        cur = S.ns
        made = []
        for c, (prv, prot) in list(F.local_consts.items()):
            if c.startswith(base + '.') and not any(p.startswith('_') for p in split_name(c[len(base) + 1:])):
                rest = c[len(base) + 1:]
                a = join(join(cur, s), rest)
                t = ('_private:' + c) if prv else c
                S.aliases[a].append(t)
                made.append((a, t, join(s, rest)))
        return made

    def S_alias(self, a, n):
        S, F = self.S, self.F
        def scoped(x):
            return x if (x == PREFIX or x.startswith(PREFIX + '.')) else join(PREFIX, x)
        st = scoped(n)
        t = None
        if F.contains(st):
            t = st
        elif F.contains(n):
            t = n
        elif F.private(st):
            t = '_private:' + st
        elif F.private(n):
            t = '_private:' + n
        if t is None:
            self.counts['alias-target-missing'] += 1
            return None
        al = scoped(a)
        S.aliases[al].append(t)
        return (al, t)

    def S_erase(self, c, attr, s):
        S = self.S
        ok = []
        for w in s.split(' '):
            if not w:
                continue
            r = S.resolve_global(w)
            ov = self.oracle(self.mod, w, r) if self.oracle else None
            if ov is not None:
                r = ov
            if len(r) != 1:
                self.counts['erase-skip-' + ('unknown' if not r else 'ambiguous')] += 1
                self.decisions.append({'line': c.line, 'attr': attr, 'name': w, 'erase': False, 'res': r})
                continue
            d = r[0]
            if d in S.erased[attr]:
                self.counts['erase-skip-already'] += 1
                self.decisions.append({'line': c.line, 'attr': attr, 'name': w, 'erase': False, 'res': r, 'why': 'already'})
                continue
            S.erased[attr].add(d)
            ok.append(w)
            self.decisions.append({'line': c.line, 'attr': attr, 'name': w, 'erase': True, 'res': r})
        return ok

    # ------------------------------------------------------------------ main loop
    def run(self):
        n = len(self.cmds)
        for i, c in enumerate(self.cmds):
            self.process(c)
            if c.kind in ('shim',):
                continue
            # a scope about to be closed by the next `end` needs no re-synchronisation
            if c.kind == 'end' and i + 1 < n and self.cmds[i + 1].kind == 'end':
                continue
            self.sync(c)
        # remaining S-only state for namespaces that exist at EOF (base scope)
        add_ods, extra_ods, add_act, extra_act = self.delta()
        live = [str(od) for od in add_ods if od[0] != 's' or self.F.is_ns(od[1])]
        live_act = [n for n in add_act if self.F.is_ns(n)]
        if live or live_act:
            self.residual(None, 'eof-mismatch', {'ods': live, 'act': live_act})
        return self

    def sync(self, c):
        """after a command: bring T's top scope to S's (e.g. a namespace that the port command opened
        before it existed has now been created)"""
        cms = self.plan_fix(c)
        if cms:
            txt = '\n'.join(self.render_open(cm) for cm in cms)
            self.edits.append((c.b, c.b, '\n' + txt))
            for cm in cms:
                self.apply_T_open(cm, c)
            self.counts['sync-after-' + c.kind] += 1
            self.check_equal(c, 'sync')

    def process(self, c, inner_of=None):
        k = c.kind
        S, T, F = self.S, self.T, self.F
        if k == 'import':
            if c.info['mod'] == PORTUTILEXT:
                if PORTUTIL in self.imports:
                    self.edit_delete_line(c)
                else:
                    self.edits.append((c.a, c.b, 'import ' + PORTUTIL))
                self.counts['import-portutilext'] += 1
            return
        if k == 'namespace':
            S.cmd_namespace(c.info['name']); T.cmd_namespace(c.info['name'])
            return
        if k == 'section':
            S.cmd_section(c.info['name'], c.info.get('noncomputable')); T.cmd_section(c.info['name'], c.info.get('noncomputable'))
            return
        if k == 'end':
            S.cmd_end(c.info['name']); T.cmd_end(c.info['name'])
            return
        if k == 'open':
            if c.info.get('in'):
                S.cmd_section(None); T.cmd_section(None)
            for st, nm in ((S, 'S'), (T, 'T')):
                try:
                    st.cmd_open(c.info)
                except SimError as e:
                    self.residual(c, 'open-failed-' + nm, str(e))
            if c.info.get('in'):
                if c.inner is not None:
                    self.process(c.inner, inner_of=c)
                S.cmd_end(None); T.cmd_end(None)
            return
        if k == 'export':
            for st, nm in ((S, 'S'), (T, 'T')):
                try:
                    st.cmd_export(c.info['ns'], c.info['ids'])
                except SimError as e:
                    self.residual(c, 'export-failed-' + nm, str(e))
            return
        if k == 'decl':
            for e in decl_events(c, S.ns, self.src):
                if e[0] == 'const':
                    F.local_consts[e[1]] = (e[2], e[3])
                    for p in name_prefixes(e[1]):
                        F.local_ns.add(p)
                elif e[0] == 'ns':
                    F.local_ns.add(e[1])
            return
        if k == 'attribute':
            self.plain_attribute(c)
            if c.info.get('in') and c.inner is not None:
                S.cmd_section(None); T.cmd_section(None)
                self.process(c.inner)
                S.cmd_end(None); T.cmd_end(None)
            return
        if k in ('set_option', 'variable', 'omit', 'include') and c.info.get('in') and c.inner is not None:
            S.cmd_section(None); T.cmd_section(None)
            self.process(c.inner)
            S.cmd_end(None); T.cmd_end(None)
            return
        if k == 'hash':
            if c.info['name'] == '#r2nos_type_eq_warn':
                self.edit_delete_cmd(c)
                self.counts['typeeq-removed'] += 1
            return
        if k == 'shim':
            self.shim(c)
            return
        return

    def plain_attribute(self, c):
        S, T = self.S, self.T
        for kind, an, extra in attr_names(c.info['attrs']):
            if an.startswith('-'):
                attr = an[1:]
                for st in (S, T):
                    for w in c.info['names']:
                        r = st.resolve_global(w)
                        if len(r) == 1:
                            st.erased.setdefault(attr, set()).add(r[0])

    # ------------------------------------------------------------------ edits
    def line_span(self, a, b):
        """extend [a,b) to whole lines if the command is alone on its lines"""
        src = self.src
        ls = src.rfind('\n', 0, a) + 1
        le = src.find('\n', b)
        le = len(src) if le < 0 else le
        if src[ls:a].strip() == '' and src[b:le].strip() == '':
            return ls, min(le + 1, len(src)), True
        return a, b, False

    def edit_delete_line(self, c):
        a, b, whole = self.line_span(c.a, c.b)
        self.edits.append((a, b, ''))

    def edit_delete_cmd(self, c):
        a, b, whole = self.line_span(c.toks[0].a, c.toks[-1].b)
        self.edits.append((a, b, ''))

    def replace_cmd(self, c, text):
        """replace the command's own tokens (incl. trailing `in`) by text (possibly empty)"""
        a, b = c.toks[0].a, c.toks[-1].b
        if not text:
            a2, b2, whole = self.line_span(a, b)
            if whole:
                self.edits.append((a2, b2, ''))
                return
            # mid-line: remove and keep a single space
            self.edits.append((a, b, ''))
            return
        la, lb, whole = self.line_span(a, b)
        if not whole and '\n' in text:
            text = '\n' + text + '\n'
        self.edits.append((a, b, text))

    # ------------------------------------------------------------------ port commands
    def shim(self, c):
        name = c.info['name']
        args = c.info['args']
        S, T = self.S, self.T
        in_ = bool(c.info.get('in'))
        self.counts['shim-' + name] += 1
        if in_:
            S.cmd_section(None); T.cmd_section(None)
        out_cmds = []   # rendered plain commands
        if name in ('r2nos_open_dual', 'r2nos_open_scoped_dual', 'r2nos_namespace_dual', 'r2nos_open_scoped',
                    'w03_open', 'w03_reactivate'):
            if name == 'r2nos_open_dual':
                self.S_open_dual(args[0], False)
            elif name == 'r2nos_open_scoped_dual':
                self.S_open_dual(args[0], True)
            elif name == 'r2nos_namespace_dual':
                self.S_namespace_dual()
            elif name == 'r2nos_open_scoped':
                self.S_open_scoped(args[0])
            elif name == 'w03_open':
                self.S_w03_open(args[0])
            elif name == 'w03_reactivate':
                self.S_w03_reactivate(args[0])
            cms = self.plan_fix(c)
            for cm in cms:
                self.apply_T_open(cm, c)
                out_cmds.append(self.render_open(cm, in_))
            self.check_equal(c, name)
        elif name in ('w03_export', 'w03_export_all', 'r2nos_alias'):
            if name == 'w03_export':
                made = self.S_w03_export(args[0], args[1])
            elif name == 'w03_export_all':
                made = self.S_w03_export_all(args[0], args[1])
            else:
                r = self.S_alias(args[0], args[1])
                made = [] if r is None else [(r[0], r[1], None)]
            out_cmds.extend(self.render_exports(c, made, in_))
        elif name == 'r2nos_erase_attr':
            attr = args[0]
            ok = self.S_erase(c, attr, args[1])
            if ok:
                for w in ok:
                    r = T.resolve_global(w)
                    if len(r) == 1:
                        T.erased[attr].add(r[0])
                out_cmds.append('attribute [-%s] %s%s' % (attr, ' '.join(ident(w) for w in ok), ' in' if in_ else ''))
        else:
            self.residual(c, 'unhandled-shim', name)
            return
        self.replace_cmd(c, '\n'.join(out_cmds))
        if in_:
            if c.inner is not None:
                self.process(c.inner)
            S.cmd_end(None); T.cmd_end(None)
            # after the combinator, both are back in the outer scope

    def render_exports(self, c, made, in_):
        """aliases a -> t created by S: emit `export` in the current namespace when possible"""
        T = self.T
        cur = T.ns
        groups = collections.OrderedDict()
        for a, t, w in made:
            if not a.startswith(cur + '.'):
                # alias outside the current namespace: check whether it is redundant for resolution
                if self.alias_redundant(a, t):
                    self.counts['alias-redundant'] += 1
                    self.decisions.append({'line': c.line, 'alias': a, 'target': t, 'redundant': True})
                    continue
                self.residual(c, 'alias-outside-namespace', {'alias': a, 'target': t})
                continue
            idn = a[len(cur) + 1:]
            tt = t[len('_private:'):] if t.startswith('_private:') else t
            if not tt.endswith('.' + idn) and tt != idn:
                self.residual(c, 'alias-shape', {'alias': a, 'target': t})
                continue
            nsp = tt[:-len(idn) - 1] if tt != idn else ''
            if not nsp:
                self.residual(c, 'alias-root-namespace', {'alias': a, 'target': t})
                continue
            groups.setdefault(nsp, []).append((idn, a, t))
        out = []
        for nsp, items in groups.items():
            out.append('export %s (%s)%s' % (root_ident(nsp), ' '.join(ident(i) for i, _, _ in items), ' in' if in_ else ''))
            for idn, a, t in items:
                T.aliases[a].append(t)
        return out

    def alias_redundant(self, a, t):
        """alias `a` (absolute) -> t: redundant iff resolving the relative name from inside the alias's
        parent namespace already yields t through the namespace chain without the alias"""
        # the alias is visible at namespace level parent(a); a lookup of id = suffix of a relative to a
        # namespace N ⊑ parent(a) first checks deeper levels (unchanged), then parent(a) (alias), then
        # outer levels.  Without the alias the chain continues to outer levels.
        par = '.'.join(split_name(a)[:-1])
        last = split_name(a)[-1]
        # the identifiers used in source are relative to some namespace inside `par`; the relevant
        # comparison: from par, id `x` such that par.x == a. Lookup outer levels of par for x.
        x = last
        # x may be dotted relative to a deeper level; we test the most specific form: relative to
        # the namespace of the alias' declaration context (the S_X level) — compute against PREFIX chain
        rel_par = par
        best = None
        # walk outward from parent(par)
        parts = split_name(par)
        tt = t[len('_private:'):] if t.startswith('_private:') else t
        # find suffix: a = P2MW.S_X.<suffix>; the source refers to <suffix>
        if a.startswith(PREFIX + '.P2MW.'):
            rest = a[len(PREFIX) + len('.P2MW.'):]
            comps = split_name(rest)
            sx = comps[0]
            suffix = '.'.join(comps[1:])
            # outer levels from P2MW.S_X: P2MW, PREFIX, ...
            for lvl in [PREFIX + '.P2MW'] + name_parents(PREFIX):
                rid = join(lvl, suffix)
                if self.F.contains(rid) or self.F.private(rid):
                    best = rid
                    break
            if best is None:
                # resolveExact root
                if self.F.contains(suffix):
                    best = suffix
            return best == tt
        return False

    # ------------------------------------------------------------------ output
    def output(self):
        edits = sorted(self.edits, key=lambda e: (e[0], e[1]))
        out = []
        pos = 0
        for a, b, t in edits:
            if a < pos:
                raise RuntimeError('overlapping edits in %s at %d' % (self.mod, a))
            out.append(self.src[pos:a])
            out.append(t)
            pos = b
        out.append(self.src[pos:])
        return ''.join(out)


def topo_order(G, mods):
    order = []
    seen = set()
    def visit(m):
        if m in seen or m not in G.idx:
            return
        seen.add(m)
        for i in G.idx[m].imports:
            visit(i)
        order.append(m)
    sys.setrecursionlimit(100000)
    for m in mods:
        visit(m)
    return order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mods', nargs='*')
    ap.add_argument('--cone', action='store_true')
    ap.add_argument('--all', action='store_true')
    ap.add_argument('--write', action='store_true')
    ap.add_argument('--out', default=os.path.join(WORK, 'translate'))
    args = ap.parse_args()
    G = Graph()
    if args.all:
        mods = sorted(G.idx)
    elif args.cone:
        mods = topo_order(G, args.mods)
    else:
        mods = args.mods
    mods = topo_order(G, mods) if not args.cone else mods
    os.makedirs(args.out, exist_ok=True)
    tot = collections.Counter()
    rescount = collections.Counter()
    for m in mods:
        if m.startswith(FQ_PREFIX):
            tot['skipped-finitequotient'] += 1
            continue
        tr = Translator(G, m).run()
        # publish aliases for dependents
        for a, ts in tr.S.aliases.items():
            for t in ts:
                G.add_alias(m, a, t)
        new = tr.output()
        for r in tr.res:
            rescount[r['kind']] += 1
        tot.update(tr.counts)
        json.dump({'module': m, 'counts': tr.counts, 'residuals': tr.res, 'decisions': tr.decisions},
                  open(os.path.join(args.out, m + '.json'), 'w'), indent=1, default=str)
        if args.write and new != tr.src:
            open(os.path.join(ROOT, tr.path), 'w', encoding='utf-8').write(new)
    print(json.dumps({'modules': len(mods), 'counts': tot, 'residuals': rescount}, indent=1, default=str))


if __name__ == '__main__':
    main()
