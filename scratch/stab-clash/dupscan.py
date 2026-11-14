# Heuristic static scan (adapted from scratch/t40-clash/dupscan.py): declaration names declared in
# two different git-tracked Lean files under ZInQKernel/Contrib/. Ignores `private`, instances,
# auto-generated names; prints names declared in >1 file.
import subprocess, re, collections
files = subprocess.run(['git','ls-files','ZInQKernel/Contrib/*.lean'],capture_output=True,text=True).stdout.split()
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|nonrec|public|unsafe|partial|irreducible_def)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|opaque|axiom|irreducible_def)\s+([^\s:({\[]+)')
where = collections.defaultdict(set)
for f in files:
    ns = []; incomment = False
    for line in open(f, encoding='utf-8'):
        s = line
        if '/-' in s and '-/' not in s: incomment = True; continue
        if incomment:
            if '-/' in s: incomment = False
            continue
        if re.match(r'^\s*private\s', s) or re.match(r'^\s*(@\[[^\]]*\]\s*)?private\s', s): continue
        m = re.match(r'^namespace\s+(\S+)', s)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', s)
        if m and ns and '.'.join(ns).endswith(m.group(1)):
            k = m.group(1).count('.')+1
            # namespace A.B ... end A.B pops one entry pushed as 'A.B'
            if ns[-1] == m.group(1): ns.pop()
            continue
        m = decl.match(s)
        if m:
            n = m.group(2)
            full = n[len('_root_.'):] if n.startswith('_root_.') else '.'.join(ns + [n])
            where[full].add(f)
for n, fs in sorted(where.items()):
    if len(fs) > 1:
        print(n); [print('   ', f) for f in sorted(fs)]
