"""walk() from mk_propts.py (leaf-fold3), verbatim, as a module (leaf-fold4)."""
import re, sys
sys.path.insert(0, "py")
from chunks import chunks, text, fullnames
seen_text = set()
def walk(cs, seen, keep_all=False, tag=''):
    ns = []; out = []; ndrop = 0; diffs = []
    for c in cs:
        if c['kind'] == 'struct':
            l = c['lines'][0]
            if l.startswith('namespace '): ns.append(('n', l.split()[1]))
            elif l.startswith('section'): ns.append(('s', l.split()[1] if len(l.split()) > 1 else ''))
            elif l.startswith('noncomputable section'): ns.append(('s', ''))
            elif l.startswith('end'):
                if ns: ns.pop()
            if l.startswith('#') or l.startswith('import '): continue
            out.append(text(c)); continue
        if c['kind'] == 'decl' and c['name']:
            nm = c['name']
            full = '.'.join([x[1] for x in ns if x[0] == 'n'] + [nm])
            if (full in seen or text(c) in seen_text) and not keep_all:
                if full in seen and seen[full] != text(c): diffs.append(full)
                ndrop += 1
                # drop the `… in` modifiers (open/attribute/set_option/omit … in) that applied to it
                while out and re.match(r'^(open|attribute|set_option|omit|include|variable)\b.*\sin\s*$', out[-1]) and '\n' not in out[-1]:
                    out.pop()
                continue
            seen.setdefault(full, text(c)); seen_text.add(text(c))
        out.append(text(c))
    print(tag, 'dropped', ndrop, 'diff', diffs, file=sys.stderr)
    return '\n'.join(out), diffs
