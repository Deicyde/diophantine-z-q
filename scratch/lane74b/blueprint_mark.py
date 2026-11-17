"""Mark the blueprint articles whose lean: names were deleted with Route K (lane74, fork issue #77).

Input: the output of `autoform check blueprint --lean-root .` (lines "error: <article>: declaration not found in .:
<name>"). For each article: the missing names are dropped from `lean:`; if none remains, the keys `lean:`,
`statement:` and `proof:` are dropped (the article is then an unformalized page). A note after the title records
the removal and the tag `route-k-final`. Nothing else changes. Prints every article touched.
Usage: python3 scratch/lane74b/blueprint_mark.py CHECK-OUTPUT.txt
"""
import re, sys, collections
d = collections.defaultdict(list)
for l in open(sys.argv[1]):
    m = re.match(r'error: (\S+): declaration not found in \.: ([^;\s]+)(;|\s*$)', l)
    if m:
        d[m.group(1)].append(m.group(2))
NOTE_ALL = ('> **Removed from the Lean development.** The Lean declarations of this page were removed with Route K and '
            'the Tian–Yuan–Zhang/Gross–Zagier route (fork issue #77); they are at the tag `route-k-final`. '
            'The page is kept, unformalized, until the blueprint rewrite (#81).')
NOTE_SOME = ('> **Partly removed from the Lean development.** Some Lean declarations of this page were removed with '
             'Route K (fork issue #77; they are at the tag `route-k-final`): {names}. The page is kept until the '
             'blueprint rewrite (#81).')
for a, gone in sorted(d.items()):
    f = f'blueprint/roadmap/{a}.md'
    s = open(f).read()
    assert s.startswith('---\n')
    end = s.index('\n---\n', 4)
    head, body = s[4:end].split('\n'), s[end + 5:]
    lean = next(l for l in head if l.startswith('lean: '))
    names = [x.strip() for x in lean[6:].split(',')]
    rest = [x for x in names if x not in gone]
    assert len(rest) + len(set(gone)) == len(names), (a, gone, names)
    if rest:
        head = [('lean: ' + ', '.join(rest)) if l == lean else l for l in head]
        note = NOTE_SOME.format(names=', '.join(f'`{x}`' for x in names if x not in rest))
    else:
        head = [l for l in head if not l.startswith(('lean: ', 'statement: ', 'proof: '))]
        note = NOTE_ALL
    # the note goes after the first heading line
    bl = body.split('\n')
    i = next(k for k, l in enumerate(bl) if l.startswith('# '))
    bl[i + 1:i + 1] = ['', note]
    open(f, 'w').write('---\n' + '\n'.join(head) + '\n---\n' + '\n'.join(bl))
    print(f, 'partial' if rest else 'all', len(set(gone)))
