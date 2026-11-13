"""Approximate list of top-level declarations of a Lean file with their namespace-qualified names (namespace/section
stack; block comments skipped). decls(path) -> {name: [line, ...]}."""
import re, sys
def decls(path, skip_hdec=False):
    stack = []; out = {}; depth = 0
    for ln, l in enumerate(open(path).read().split('\n'), 1):
        if depth > 0 or l.lstrip().startswith('/-'):
            # track block comments /- ... -/ (nesting by counts on the line)
            depth += l.count('/-') - l.count('-/')
            if depth < 0: depth = 0
            if not re.match(r'^(theorem|lemma|def|abbrev|instance|structure)', l): continue
        m = re.match(r'^namespace ([A-Za-z_][\w.\']*)\s*$', l)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'^(?:noncomputable )?section(?: ([\w.]+))?\s*$', l)
        if m: stack.append(('sec', m.group(1))); continue
        m = re.match(r'^end(?: ([\w.]+))?\s*(--.*)?$', l)
        if m:
            if stack: stack.pop()
            continue
        m = re.match(r'^(?:@\[[^\]]*\] )?(?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque) ([^\s:\[\{\(]+)', l)
        if m:
            nm = m.group(1)
            if nm.startswith('_root_.'): full = nm[7:]
            else:
                ns = '.'.join(x for k, x in stack if k == 'ns')
                full = (ns + '.' + nm) if ns else nm
            if skip_hdec and full.startswith('HDec.'): full = full[5:]
            out.setdefault(full, []).append(ln)
    return out
if __name__ == '__main__':
    a = decls(sys.argv[1]); b = decls(sys.argv[2], skip_hdec=True)
    common = [n for n in a if n in b]
    print(len(a), 'names in', sys.argv[1], ';', len(common), 'also in', sys.argv[2])
