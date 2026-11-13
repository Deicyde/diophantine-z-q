"""Split a Lean file into top-level chunks: a declaration (with its docstring/attributes) or a
structural line. Used by leaf-fold3 to merge files that share verbatim prefixes."""
import re
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|scoped|local)\s+)*(theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def|opaque|axiom)\b\s*([^\s:({\[]*)')
STRUCT = re.compile(r'^(namespace|end|section|open|variable|universe|noncomputable section|attribute|set_option|#|/-!|import|omit|include|local notation|notation|scoped notation|macro|syntax)\b')
def chunks(text):
    L = text.split('\n'); out = []; i = 0; n = len(L)
    cur = None
    def flush():
        nonlocal cur
        if cur: out.append(cur)
        cur = None
    while i < n:
        l = L[i]
        if l.startswith('/--') or l.startswith('@['):
            flush(); cur = {'kind': 'decl', 'name': None, 'lines': [l]}
            # docstring/attr continues until a decl line
            i += 1
            while i < n and cur['name'] is None:
                cur['lines'].append(L[i]); m = DECL.match(L[i])
                if m and not L[i].startswith(' '): cur['name'] = m.group(2); cur['kw'] = m.group(1)
                i += 1
            continue
        m = DECL.match(l)
        if m:
            flush(); cur = {'kind': 'decl', 'name': m.group(2), 'kw': m.group(1), 'lines': [l]}; i += 1; continue
        if STRUCT.match(l) or l.startswith('/-!'):
            flush()
            if l.startswith('/-!') or l.startswith('/-'):
                blk = [l]
                if '-/' not in l:
                    i += 1
                    while i < n:
                        blk.append(L[i])
                        if '-/' in L[i]: break
                        i += 1
                out.append({'kind': 'struct', 'lines': blk}); i += 1; continue
            out.append({'kind': 'struct', 'lines': [l]}); i += 1; continue
        if cur is None:
            out.append({'kind': 'other', 'lines': [l]}); i += 1; continue
        cur['lines'].append(l); i += 1
    flush()
    return out
def text(c): return '\n'.join(c['lines'])

def fullnames(cs, prefix_ns=()):
    """Yield (fullname, chunk) for declaration chunks, tracking namespace/section nesting."""
    ns = list(prefix_ns)
    for c in cs:
        if c['kind'] == 'struct':
            l = c['lines'][0]
            if l.startswith('namespace '): ns.append(('n', l.split()[1]))
            elif l.startswith('noncomputable section'): ns.append(('s', ''))
            elif l.startswith('section'): ns.append(('s', l.split()[1] if len(l.split()) > 1 else ''))
            elif l.startswith('end'):
                if ns: ns.pop()
        elif c['kind'] == 'decl' and c['name']:
            nm = c['name']
            if nm.startswith('_root_.'): full = nm[7:]
            else: full = '.'.join([x[1] for x in ns if x[0] == 'n'] + [nm])
            yield full, c
