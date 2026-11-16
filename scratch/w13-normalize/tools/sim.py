"""Scope simulator and translator for the W13 port commands (offline tool).

For every staged file it runs two simulations side by side over Lean 4.35's own scoping rules
(Lean/ResolveName.lean, Lean/Elab/Open.lean, Lean/Elab/BuiltinCommand.lean, Lean/ScopedEnvExtension.lean):
  S = the recovered source with the semantics of the port commands (PortUtil.lean / PortUtilExt.lean,
      read as specifications, never executed);
  T = the translated file (ordinary Lean only).
Each port command is replaced by plain `open`/`open scoped`/`export`/`attribute [-…]` commands chosen so
that T's scope (open declarations, active scoped namespaces, aliases, erased attributes) equals S's
after the command.  Any state difference that plain Lean cannot reproduce is reported as a residual.
"""
import os, sys, collections, json
sys.path.insert(0, os.path.dirname(__file__))
import cmdparse
from index import split_name, join, name_prefixes, full_decl_name, FLT, build_index, attr_names
from graph import ROOT, staged_files, mod_of, path_of
import envdb

PREFIX = FLT


def is_atomic(n):
    return len(split_name(n)) == 1


def strip_root(n):
    return n[len('_root_.'):] if n.startswith('_root_.') else (('') if n == '_root_' else n)


def name_parents(ns):
    """ns, parent(ns), ..., excluding anonymous"""
    parts = split_name(ns) if ns else []
    out = []
    for k in range(len(parts), 0, -1):
        out.append('.'.join(parts[:k]))
    return out


def other_half(c):
    if c == PREFIX:
        return ''
    if c.startswith(PREFIX + '.'):
        return c[len(PREFIX) + 1:]
    return join(PREFIX, c)


class Facts:
    """environment facts for a file's import closure"""

    def __init__(self, G, mod):
        self.G = G
        self.mod = mod
        self.closure = G.closure_of(mod)
        self.local_ns = set()
        self.local_consts = {}   # name -> (private, protected)
        self.local_alias = collections.defaultdict(list)
        self.local_inst = set()
        self.local_scoped_inst = collections.defaultdict(set)

    # --- namespaces
    def is_ns(self, n):
        if not n:
            return False
        if n in self.local_ns:
            return True
        owners = self.G.ns_owner.get(n)
        if owners:
            for m in owners:
                if m in self.closure:
                    return True
        return False

    # --- constants
    def contains(self, n):
        v = self.local_consts.get(n)
        if v is not None and not v[0]:
            return True
        owners = self.G.const_owner.get(n)
        if owners:
            for m in owners:
                if m in self.closure:
                    return True
        return False

    def private(self, n):
        v = self.local_consts.get(n)
        return v is not None and v[0]

    def is_protected(self, n):
        v = self.local_consts.get(n)
        if v is not None:
            return v[1]
        return n in self.G.prot

    def get_aliases(self, a, skip_protected):
        out = []
        for t in self.local_alias.get(a, []):
            out.append(t)
        for t, m in self.G.alias.get(a, []):
            if m in self.closure:
                out.append(t)
        if skip_protected:
            out = [t for t in out if not self.is_protected(t)]
        return out


class Scope:
    __slots__ = ('kind', 'header', 'ns', 'ods', 'active', 'nc')

    def __init__(self, kind, header, ns, ods, active, nc=False):
        self.kind, self.header, self.ns, self.ods, self.active, self.nc = kind, header, ns, ods, active, nc

    def copy(self):
        return Scope(self.kind, self.header, self.ns, list(self.ods), set(self.active), self.nc)


class State:
    """Lean command-elaboration scope state (one of S or T)"""

    def __init__(self, F):
        self.F = F
        self.scopes = [Scope('base', '', '', [], set())]
        self.aliases = collections.defaultdict(list)
        self.erased = {'instance': set(), 'simp': set()}

    def clone_scopes(self):
        return [s.copy() for s in self.scopes]

    @property
    def top(self):
        return self.scopes[-1]

    @property
    def ns(self):
        return self.top.ns

    @property
    def ods(self):
        return self.top.ods

    # ---- name resolution (Lean.ResolveName)
    def resolve_ns_scope(self, n, ns):
        F = self.F
        for p in name_parents(ns):
            c = join(p, n)
            if F.is_ns(c):
                return c
        n2 = strip_root(n)
        return n2 if F.is_ns(n2) else None

    def resolve_ns(self, n, ods=None, ns=None):
        if ods is None:
            ods = self.ods
        if ns is None:
            ns = self.ns
        out = []
        s = self.resolve_ns_scope(n, ns)
        if s:
            out.append(s)
        for od in ods:
            if od[0] == 's':
                c = join(od[1], n)
                if self.F.is_ns(c) and n not in od[2]:
                    out.append(c)
        return out

    def alias_lookup(self, a, skip_protected):
        out = list(self.aliases.get(a, []))
        out += self.F.get_aliases(a, False)
        if skip_protected:
            out = [t for t in out if not self.F.is_protected(t)]
        return out

    def qualified(self, ns, id_):
        F = self.F
        rid = join(ns, id_)
        res = self.alias_lookup(rid, is_atomic(id_))
        if not is_atomic(id_) or not F.is_protected(rid):
            if F.contains(rid):
                return [rid] + res
            if F.private(rid):
                return ['_private:' + rid] + res
        return res

    def resolve_global(self, id_):
        """exact interpretations (no field projections) of identifier id_"""
        F = self.F
        for p in name_parents(self.ns):
            r = self.qualified(p, id_)
            if r:
                return dedup(r)
        if not is_atomic(id_):
            rid = strip_root(id_)
            if F.contains(rid):
                return [rid]
            if F.private(rid):
                return ['_private:' + rid]
        r = []
        if F.contains(id_):
            r = [id_]
        if F.private(id_):
            r = ['_private:' + id_] + r
        for od in self.ods:
            if od[0] == 's':
                if id_ in od[2]:
                    continue
                r = self.qualified(od[1], id_) + r
            else:
                opened, resolved = od[1], od[2]
                if opened == id_:
                    r = [resolved] + r
                elif id_.startswith(opened + '.'):
                    cand = resolved + id_[len(opened):]
                    if F.contains(cand):
                        r = [cand] + r
        r = self.alias_lookup(id_, is_atomic(id_)) + r
        return dedup(r)

    # ---- scoped extension activation
    def activate(self, n):
        self.top.active.add(n)

    # ---- commands
    def push(self, kind, header, ns, nc=False):
        t = self.top.copy()
        t.kind, t.header, t.ns = kind, header, ns
        t.nc = t.nc or nc
        self.scopes.append(t)

    def cmd_namespace(self, name):
        for comp in split_name(name):
            ns = join(self.ns, comp)
            self.F.local_ns.add(ns)
            self.push('namespace', comp, ns)
            self.activate(ns)

    def cmd_section(self, name, nc=False):
        if name:
            for comp in split_name(name):
                self.push('section', comp, self.ns, nc)
        else:
            self.push('section', '', self.ns, nc)

    def cmd_end(self, name):
        k = len(split_name(name)) if name else 1
        for _ in range(k):
            if len(self.scopes) > 1:
                self.scopes.pop()

    def add_od(self, od):
        self.top.ods.insert(0, od)

    def cmd_open(self, info):
        """plain `open` (Lean.Elab.OpenDecl.elabOpenDecl); returns resolved namespaces per token"""
        form = info['form']
        ods = list(self.ods)
        resolved_all = []
        if form == 'simple':
            for n in info['names']:
                rs = self.resolve_ns(n, ods=ods)
                if not rs:
                    raise SimError('unknown namespace %s' % n)
                for r in rs:
                    ods.insert(0, ('s', r, frozenset()))
                    self.activate(r)
                resolved_all.append((n, rs))
        elif form == 'scoped':
            for n in info['names']:
                rs = self.resolve_ns(n, ods=ods)
                if not rs:
                    raise SimError('unknown namespace %s' % n)
                for r in rs:
                    self.activate(r)
                resolved_all.append((n, rs))
        elif form == 'hiding':
            n = info['names'][0]
            rs = self.resolve_ns(n, ods=ods)
            if len(rs) != 1:
                raise SimError('ambiguous/unknown namespace in hiding %s %s' % (n, rs))
            r = rs[0]
            self.activate(r)
            hid = frozenset(info['hiding'])
            ods.insert(0, ('s', r, hid))
            resolved_all.append((n, rs))
        elif form == 'explicit':
            n = info['names'][0]
            rs = self.resolve_ns(n, ods=ods)
            if not rs:
                raise SimError('unknown namespace %s' % n)
            for idn in info['ids']:
                cands = []
                for r in rs:
                    rid = join(r, idn)
                    if self.F.contains(rid) or self.F.private(rid):
                        cands.append(rid)
                if len(cands) != 1:
                    raise SimError('explicit open %s (%s): %s' % (n, idn, cands))
                ods.insert(0, ('e', idn, cands[0]))
            resolved_all.append((n, rs))
        elif form == 'renaming':
            raise SimError('renaming open unsupported')
        self.top.ods = ods
        return resolved_all

    def cmd_export(self, ns_tok, ids):
        rs = self.resolve_ns(ns_tok)
        if not rs:
            raise SimError('export: unknown namespace %s' % ns_tok)
        if rs == [self.ns]:
            raise SimError('self export')
        for idn in ids:
            cands = []
            for r in rs:
                rid = join(r, idn)
                if self.F.contains(rid):
                    cands.append(rid)
                elif self.F.private(rid):
                    cands.append('_private:' + rid)
                else:
                    pass
            if len(cands) != 1:
                raise SimError('export %s (%s): %s' % (ns_tok, idn, cands))
            self.aliases[join(self.ns, idn)].append(cands[0])

    def ods_set(self):
        return set(self.ods)


class SimError(Exception):
    pass


def dedup(xs):
    out = []
    for x in xs:
        if x not in out:
            out.append(x)
    return out


class Graph:
    """global facts: external (EnvDump) + staged (static index); closures"""

    def __init__(self):
        self.db = envdb.load()
        self.idx = build_index()
        self.ns_owner = collections.defaultdict(list)
        self.const_owner = collections.defaultdict(list)
        self.prot = set()
        self.alias = collections.defaultdict(list)
        self.inst_owner = collections.defaultdict(list)
        self.private_owner = collections.defaultdict(list)
        for m, d in self.db.mods.items():
            for n in d['ns']:
                self.ns_owner[n].append(m)
            for c in d['consts']:
                self.const_owner[c].append(m)
            self.prot.update(d['prot'])
            for a, t in d['alias']:
                self.alias[a].append((t, m))
            for n, s in d['inst']:
                self.inst_owner[n].append((m, s))
        self.staged = set(self.idx)
        for m, fi in self.idx.items():
            for n in fi.ns:
                self.ns_owner[n].append(m)
            for c, inf in fi.consts.items():
                if inf['private']:
                    self.private_owner[c].append(m)
                    continue
                self.const_owner[c].append(m)
                if inf['protected']:
                    self.prot.add(c)
            for n, k in fi.inst.items():
                if isinstance(n, str):
                    self.inst_owner[n].append((m, k))
        self._ext_closure_cache = {}
        self._closure_cache = {}

    def imports_of(self, m):
        if m in self.idx:
            return self.idx[m].imports
        d = self.db.mods.get(m)
        return d['imports'] if d else []

    def ext_closure(self, m):
        c = self._ext_closure_cache.get(m)
        if c is None:
            c = frozenset(envdb.closure(self.db, [m]))
            self._ext_closure_cache[m] = c
        return c

    def staged_closure(self, m):
        c = self._closure_cache.get(m)
        if c is not None:
            return c
        seen = set()
        st = [m]
        ext_roots = set()
        while st:
            x = st.pop()
            if x in seen:
                continue
            if x in self.idx:
                seen.add(x)
                for i in self.idx[x].imports:
                    if i in self.idx:
                        st.append(i)
                    else:
                        ext_roots.add(i)
        self._closure_cache[m] = (frozenset(seen), frozenset(ext_roots))
        return self._closure_cache[m]

    def closure_of(self, m):
        st, ext_roots = self.staged_closure(m)
        out = set(st)
        out.discard(m)
        for r in ext_roots:
            out |= self.ext_closure(r)
        return out

    def add_alias(self, mod, a, t):
        self.alias[a].append((t, mod))
