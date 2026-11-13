"""Remove from a Lean file the top-level declaration blocks whose (namespace-qualified) names already exist in a reference
file. A block = optional preceding docstring/attribute lines + the decl line + following lines until the next top-level item.
Usage: python3 -I dedup_part.py in.lean ref.lean out.lean"""
import re, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from decls import decls
src, ref, outp = sys.argv[1:4]
L = open(src).read().split('\n')
refd = decls(ref, skip_hdec=True)
top = re.compile(r'^(/--|/-!|@\[|theorem |lemma |def |abbrev |instance|structure |class |inductive |opaque |namespace |end\b|section\b|noncomputable |private |protected |open |variable |set_option |attribute |universe |#|local |scoped |example|omit |include )')
# decl line numbers to drop
mine = decls(src)
drop = {ln for n, lns in mine.items() if n in refd for ln in lns}
keep = [True] * len(L)
for ln in sorted(drop):
    i = ln - 1
    # extend backwards over docstrings, attributes and `set_option … in` / `open … in` prefixes directly above
    j = i - 1
    while j >= 0:
        if L[j].startswith('@[') or ((L[j].startswith('set_option') or L[j].startswith('open ')) and L[j].rstrip().endswith(' in')):
            j -= 1; continue
        if L[j].rstrip().endswith('-/'):
            k = j
            while k >= 0 and not (L[k].startswith('/--') or L[k].startswith('/-!') or L[k].startswith('/-')): k -= 1
            if k >= 0 and L[k].startswith('/--'):
                j = k - 1; continue
        break
    start = j + 1
    # forwards until next top-level item (a non-indented, non-empty line matching `top`), after the decl line
    e = i + 1
    while e < len(L) and not (L[e] and not L[e][0].isspace() and top.match(L[e])):
        e += 1
    for t in range(start, e): keep[t] = False
open(outp, 'w').write('\n'.join(l for l, k in zip(L, keep) if k))
print('dropped', len(drop), 'decls;', sum(1 for k in keep if not k), 'lines')
