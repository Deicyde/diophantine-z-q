# Extract a top-level declaration block (with its docstring) by name; compare across files.
import re
def block(L, name, kinds=('def', 'abbrev', 'theorem', 'lemma', 'noncomputable def', 'instance')):
    pat = re.compile(r'^(?:' + '|'.join(kinds) + r')\s+' + re.escape(name) + r'(?=[\s:({\[]|$)')
    i = next(i for i, l in enumerate(L) if pat.match(l))
    s = i
    if s > 0 and L[s - 1].rstrip().endswith('-/'):
        s -= 1
        while not L[s].lstrip().startswith('/--'): s -= 1
    j = i + 1
    while j < len(L) and (L[j].startswith(' ') or (not L[j].strip() and j + 1 < len(L)
                          and L[j + 1].startswith(' '))):
        j += 1
    return s, j
def norm(xs): return re.sub(r'\s+', ' ', ''.join(xs)).strip()
