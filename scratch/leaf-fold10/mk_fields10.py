#!/usr/bin/env python3
"""leaf-fold10: the field table of the new bundles (run from the repository root).

Reads leaf-fold9's `scratch/leaf-fold9/fields9.tsv`, drops the fields leaf-fold10 removes, adds the fields it adds,
writes `scratch/leaf-fold10/fields10.tsv` and the markdown tables `fields10_tables.md`, and prints the counts after
each fold."""
import csv

SRC = 'scratch/leaf-fold9/fields9.tsv'
D = 'scratch/leaf-fold10/'

REMOVED = {
    '(1) dimjac-glue (`dimJacobianEqGenus` proved, no hypotheses)': [('T', 'dimJacobianEqGenus')],
}
ADDED = {k: [] for k in REMOVED}
ORDER = list(REMOVED)
BUNDLES = [('R', 'OpenResearchLeaves9'), ('T', 'OpenTextbookLeaves10'), ('A', 'OpenAddedLeaves8'),
           ('G', 'OpenGlue7')]
KEYS = ['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces']


def kind(form):
    if form.startswith('published form'):
        return 'LEAF'
    return {'consequence of one theorem': 'GLUE (c)', 'composite': 'GLUE (comp)', 'project glue': 'GLUE (pg)'}[form]


def counts(rows):
    c = {'pub': 0, 'c': 0, 'comp': 0, 'pg': 0}
    for r in rows:
        f = r['form']
        c['pub' if f.startswith('published form') else {'consequence of one theorem': 'c', 'composite': 'comp',
                                                          'project glue': 'pg'}[f]] += 1
    n = len(rows)
    return n, c, (c['pub'], n - c['pub']), (c['pub'] + c['c'], c['comp'] + c['pg'])


with open(SRC) as f:
    rd = csv.reader(f, delimiter='\t')
    hdr = next(rd)
    rows = [dict(zip(KEYS, r)) for r in rd]

# The task: keep reduct-split's four DVR leaves marked "published form pending the base review".
PENDING = {'serreTateThm2', 'semistableReductionDVR', 'semistableUnipotent', 'neronSchemeModelExistsDVR'}
for r in rows:
    if r['bundle'] == 'R' and r['field'] in PENDING:
        f = r['form']
        assert f.startswith('published form'), r
        r['form'] = (f[:-1] + '; pending the base review)') if f.endswith(')') else f + ' (pending the base review)'
assert sum(r['field'] in PENDING for r in rows) == 4

table = [('leaf-fold9 (`sixContactMin_of_open9`)', counts(rows))]
for step in ORDER:
    rem = set(REMOVED[step])
    assert all(any((r['bundle'], r['field']) == x for r in rows) for x in rem), step
    rows = [r for r in rows if (r['bundle'], r['field']) not in rem]
    for a in ADDED[step]:
        rows.append(dict(zip(KEYS, a)))
    table.append((step, counts(rows)))

with open(D + 'fields10.tsv', 'w') as f:
    f.write('\t'.join(hdr) + '\n')
    for b, _ in BUNDLES:
        for r in rows:
            if r['bundle'] == b:
                f.write('\t'.join(r[k] for k in KEYS) + '\n')

out = []
for b, name in BUNDLES:
    rs = [r for r in rows if r['bundle'] == b]
    out.append(f'### {name} ({len(rs)} field{"s" if len(rs) != 1 else ""})\n')
    out.append('| field | Lean type | strict kind | form | source | last task | replaces |')
    out.append('|---|---|---|---|---|---|---|')
    for r in rs:
        out.append(f"| `{r['field']}` | `{r['type']}` | {kind(r['form'])} | {r['form']} | {r['source']} | "
                   f"{r['task']} | {r['replaces']} |")
    out.append('')
open(D + 'fields10_tables.md', 'w').write('\n'.join(out))

print('| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |')
print('|---|---|---|---|---|---|---|---|')
for name, (n, c, s, l) in table:
    print(f"| {name} | {n} | {c['pub']} | {c['c']} | {c['comp']} | {c['pg']} | {s[0]} / {s[1]} | {l[0]} / {l[1]} |")
