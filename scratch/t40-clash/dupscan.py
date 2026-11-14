# Heuristic static scan for declaration names declared in two different tracked Lean files under
# ZInQKernel/ (namespace tracking via `namespace`/`end`; ignores `private`, `section` variables,
# auto-generated names). Prints names declared in >1 file where at least one file matches argv[1].
import subprocess, re, sys, collections
files = subprocess.run(['git','ls-files','ZInQKernel/*.lean'],capture_output=True,text=True).stdout.split()
decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|nonrec|public|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([^\s:({\[]+)')
where = collections.defaultdict(set)
for f in files:
    ns = []
    for line in open(f, encoding='utf-8'):
        if line.startswith('private ') or ' private ' in line[:20]: continue
        m = re.match(r'^namespace\s+(\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = decl.match(line)
        if m and m.group(1) != 'instance':
            n = m.group(2)
            full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(ns + [n])
            where[full].add(f)
pat = sys.argv[1]
for n, fs in sorted(where.items()):
    if len(fs) > 1 and any(pat in f for f in fs):
        print(n); [print('   ', f) for f in sorted(fs)]
