#!/usr/bin/env python3
"""leaf-fold9: the field table of the new bundles (run from the repository root).

Reads leaf-fold8's `scratch/leaf-fold8/fields8.tsv`, drops the 8 fields leaf-fold9 removes, adds reduct-split's 4 leaves and shimura-split's 1,
writes `scratch/leaf-fold9/fields9.tsv` and the markdown tables `fields9_tables.md`, and prints the counts after
each fold."""
import csv

SRC = 'scratch/leaf-fold8/fields8.tsv'
D = 'scratch/leaf-fold9/'

REMOVED = {
    'r1r2-bridge (r1rec, r5 from r1r2)': [('R', 'r1rec'), ('R', 'r5')],
    'cloud PR #11 (t33, normalModelOfFunctionFieldQ)': [('T', 't33'), ('T', 'normalModelOfFunctionFieldQ')],
    'modular-split (r15 from dsThm966)': [('R', 'r15')],
    'reduct-split (r7b, r8 from published-form leaves)': [('R', 'r7b'), ('R', 'r8')],
    'shimura-split (r5count from GonzalezRotgerCountX6)': [('R', 'r5count')],
}
ADDED = {k: [] for k in REMOVED}
RS = '_root_.ReductSplit.'
ADDED['reduct-split (r7b, r8 from published-form leaves)'] = [
    ('R', 'serreTateThm2', RS + 'SerreTateThm2', 'published form',
     'Serre-Tate, Ann. of Math. 88 (1968) Thm 2: potential good reduction iff the image of inertia on T_l A is finite '
     '(RISK: if printed for complete K, a consequence; reduct-split §5)', 'reduct-split; folded by leaf-fold9',
     'r7b (consequence), with mumfordTorsionAlgClosed'),
    ('R', 'semistableReductionDVR', RS + 'SemistableReductionDVR', 'published form (specialization)',
     'SGA 7 I Exp. IX Thm 3.6 over a DVR: A_K\' semistable at every place above O for a finite K\' (print: finite '
     'separable)', 'reduct-split; folded by leaf-fold9', 'r8 (consequence), with the next two and mumfordTorsionAlgClosed'),
    ('R', 'semistableUnipotent', RS + 'SemistableUnipotent', 'published form (weakest reading)',
     'SGA 7 I Exp. IX Prop. 3.5, semistable => (sigma-1)^2 = 0 on T_l for sigma in inertia, one sigma at a time',
     'reduct-split; folded by leaf-fold9', 'r8'),
    ('R', 'neronSchemeModelExistsDVR', RS + 'NeronSchemeModelExistsDVR', 'published form',
     'BLR, Neron models, 1.4 Thm 3 over a DVR, scheme form (no group law)', 'reduct-split; folded by leaf-fold9',
     'r8'),
]
ADDED['shimura-split (r5count from GonzalezRotgerCountX6)'] = [
    ('R', 'gonzalezRotgerCountX6', '_root_.ShimuraSplit.GonzalezRotgerCountX6', 'published form (specialization)',
     'Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6 (read by the audit) at (D,N) = (6,1), on the points '
     'of one canonical coarse witness X6 (with the R1fp/X6 clause lists and Lemma QP, as for r1r2)',
     'shimura-split; folded by leaf-fold9', 'r5count (consequence)'),
]
ORDER = list(REMOVED)
BUNDLES = [('R', 'OpenResearchLeaves9'), ('T', 'OpenTextbookLeaves9'), ('A', 'OpenAddedLeaves8'),
           ('G', 'OpenGlue7')]


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
    rows = [dict(zip(['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces'], r)) for r in rd]

table = [('leaf-fold8 (`sixContactMin_of_open8`)', counts(rows))]
for step in ORDER:
    rem = set(REMOVED[step])
    assert all(any((r['bundle'], r['field']) == x for r in rows) for x in rem), step
    rows = [r for r in rows if (r['bundle'], r['field']) not in rem]
    for a in ADDED[step]:
        rows.append(dict(zip(['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces'], a)))
    table.append((step, counts(rows)))

with open(D + 'fields9.tsv', 'w') as f:
    f.write('\t'.join(hdr) + '\n')
    for b, _ in BUNDLES:
        for r in rows:
            if r['bundle'] == b:
                f.write('\t'.join(r[k] for k in ['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces'])
                        + '\n')

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
open(D + 'fields9_tables.md', 'w').write('\n'.join(out))

print('| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |')
print('|---|---|---|---|---|---|---|---|')
for name, (n, c, s, l) in table:
    print(f"| {name} | {n} | {c['pub']} | {c['c']} | {c['comp']} | {c['pg']} | {s[0]} / {s[1]} | {l[0]} / {l[1]} |")
