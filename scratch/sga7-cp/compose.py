"""Compose the research-bundle conversions OpenResearchLeaves21 -> ... -> OpenResearchLeaves14 (TailZ25-TailZ34)
field by field: for each field of OpenResearchLeaves14, its term over the top bundle `r` (gen 21) and the
textbook bundle `t` (OpenTextbookLeaves11). Usage: python3 scratch/sga7-cp/compose.py"""
import re, glob
H = 'ZInQKernel/OneProof/H/'
src = {fn: open(fn).read() for fn in glob.glob(H + '*.lean')}

def struct_fields(name):
    for fn, s in src.items():
        m = re.search(r'^structure %s : Prop where\n(.*?)(?=\n\n|\n/-!|\ntheorem|\ndef)' % name, s, re.S | re.M)
        if m:
            return re.findall(r"^  ([A-Za-z_][\w']*) :", m.group(1), re.M)
    raise SystemExit('no struct ' + name)

def conv(k):
    nm = 'openResearchLeaves%d_of_OpenResearchLeaves%d' % (k, k + 1)
    for fn, s in src.items():
        m = re.search(r'^theorem %s \((\w) : [^\n]*? where\n(.*?)(?=\n\n|\n/-|\ntheorem|\nend)' % nm, s, re.S | re.M)
        if m:
            var = m.group(1)
            body = m.group(2)
            d = {}
            for fm in re.finditer(r"^  ([A-Za-z_][\w']*) := (.*?)(?=\n  [A-Za-z_][\w']* :=|\Z)", body, re.S | re.M):
                d[fm.group(1)] = (var, ' '.join(fm.group(2).split()))
            return fn, d
    raise SystemExit('no conv ' + nm)

terms = {f: 'r14.' + f for f in struct_fields('OpenResearchLeaves14')}
cur = {f: '{%d}.%s' % (14, f) for f in struct_fields('OpenResearchLeaves14')}
for k in range(14, 21):
    fn, d = conv(k)
    newcur = {}
    for f, term in cur.items():
        def sub(m):
            g = m.group(1)
            var, t = d[g]
            t = re.sub(r'\b%s\.([A-Za-z_][\w\']*)' % var, lambda mm: '{%d}.%s' % (k + 1, mm.group(1)), t)
            return '(' + t + ')' if ' ' in t else t
        newcur[f] = re.sub(r'\{%d\}\.([A-Za-z_][\w\']*)' % k, sub, term)
    cur = newcur
top = struct_fields('OpenResearchLeaves21')
for f, term in cur.items():
    term = term.replace('{21}.', 'r.')
    print(f'{f} := {term}')
print('-- top fields not reached:', [f for f in top if not any(('r.' + f) in t.replace('{21}.', 'r.') for t in cur.values())])
