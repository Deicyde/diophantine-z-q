"""Compare two HashDump.lean outputs (name module levels typeHash valueHash per constant of every ZInQKernel module).
usage: cmp_hashes_full.py BEFORE AFTER [REPO-DIR-AFTER]
Prints: changed constants (both present, record differs), constants only before grouped by module (marking modules
whose file is absent after), constants only after grouped by module."""
import sys, os, collections
def load(f):
    d = {}
    for l in open(f):
        p = l.split()
        if p: d[p[0]] = p[1:]
    return d
a, b = load(sys.argv[1]), load(sys.argv[2])
root = sys.argv[3] if len(sys.argv) > 3 else '.'
exists = lambda m: os.path.exists(os.path.join(root, m.replace('.', '/') + '.lean'))
only_a = sorted(set(a) - set(b)); only_b = sorted(set(b) - set(a))
changed = sorted(n for n in set(a) & set(b) if a[n] != b[n])
print(f'before {len(a)}  after {len(b)}  only before {len(only_a)}  only after {len(only_b)}  changed {len(changed)}')
print('\n## changed (name: module | before type,value hash -> after)')
for n in changed:
    what = []
    if a[n][0] != b[n][0]: what.append(f'module {a[n][0]} -> {b[n][0]}')
    if a[n][1] != b[n][1]: what.append('levels')
    if a[n][2] != b[n][2]: what.append('type')
    if a[n][3] != b[n][3]: what.append('value')
    print(f'{n}: {b[n][0]} | {", ".join(what)}')
mods_a = {v[0] for v in a.values()}; mods_b = {v[0] for v in b.values()}
def groups(names, d, tag, other_mods):
    g = collections.defaultdict(list)
    for n in names: g[d[n][0]].append(n)
    print(f'\n## only {tag}: {len(names)} constants in {len(g)} modules')
    for kind, test in [('file absent after', lambda m: not exists(m)),
                       ('file present, module not in the other environment', lambda m: exists(m) and m not in other_mods),
                       ('module in both environments', lambda m: exists(m) and m in other_mods)]:
        ms = [m for m in sorted(g) if test(m)]
        print(f'\n### {kind}: {sum(len(g[m]) for m in ms)} constants in {len(ms)} modules')
        for m in ms:
            print(f'{m}: {len(g[m])}' + (': ' + ', '.join(g[m]) if kind.startswith('module in both') else ''))
groups(only_a, a, 'before', mods_b)
groups(only_b, b, 'after', mods_a)
