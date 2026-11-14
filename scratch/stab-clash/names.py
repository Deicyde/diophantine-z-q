# print declared (non-private) names of a Lean file, namespace-qualified (heuristic, as dupscan.py)
import re, sys
decl = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected|nonrec|public|unsafe|partial)\s+)*(theorem|lemma|def|abbrev|structure|class|inductive|opaque|instance|irreducible_def)\s+([^\s:({\[]+)')
ns=[]; out=[]
for s in open(sys.argv[1]):
    if re.match(r'^\s*(@\[[^\]]*\]\s*)?private\s', s): continue
    m = re.match(r'^namespace\s+(\S+)', s)
    if m: ns.append(m.group(1)); continue
    m = re.match(r'^end\s+(\S+)\s*$', s)
    if m and ns and ns[-1]==m.group(1): ns.pop(); continue
    m = decl.match(s)
    if m:
        n=m.group(2); print(n[7:] if n.startswith('_root_.') else '.'.join(ns+[n]))
