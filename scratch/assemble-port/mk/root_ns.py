"""assemble-port: Mathlib-namespace blocks (`namespace AlgebraicGeometry`, `namespace IsLocalRing`) inside `namespace
HDec` would create `HDec.AlgebraicGeometry`, which (i) breaks dot notation on Mathlib types (`f.stalkMapAt` looks up
`AlgebraicGeometry.Scheme.Hom.stalkMapAt`) and (ii) shadows the Mathlib namespace in every later `open
AlgebraicGeometry`. So each such block becomes `section APRoot_X` + `open _root_.X`, and each top-level named
declaration `NAME` in it becomes `_root_.X.NAME` (the same full name as in the root-namespace assembly).
Usage: python3 -I mk/root_ns.py part.lean ..."""
import re, sys
NS = ('AlgebraicGeometry', 'IsLocalRing')
for path in sys.argv[1:]:
    L = open(path).read().split('\n'); cur = None; n = 0
    for i, l in enumerate(L):
        m = re.match(r'^namespace (\S+)\s*$', l)
        if m and m.group(1) in NS and cur is None:
            cur = m.group(1); L[i] = 'section APRoot_' + cur
            if not (i + 1 < len(L) and L[i + 1].strip() == 'open _root_.' + cur):
                L[i] += '\nopen _root_.' + cur
            continue
        if cur and re.match(r'^end %s\s*$' % cur, l):
            L[i] = 'end APRoot_' + cur; cur = None; continue
        if cur:
            m = re.match(r'^((?:private |protected )?(?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure) )([^\s:\[\{\(]+)(.*)$', l)
            if m:
                L[i] = m.group(1) + '_root_.' + cur + '.' + m.group(2) + m.group(3); n += 1
    assert cur is None
    open(path, 'w').write('\n'.join(L)); print(path, n, 'declarations rooted')
