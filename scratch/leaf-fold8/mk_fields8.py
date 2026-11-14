#!/usr/bin/env python3
"""leaf-fold8: the field table of the new bundles (run from the repository root).

Reads leaf-fold7's `scratch/leaf-fold7/fields7.tsv`, drops the 14 fields leaf-fold8 removes, appends the 11 new
fields (forms as the source reports give them; see docs/research/leaf-fold8.md §2 for the readings), writes
`scratch/leaf-fold8/fields8.tsv` and the markdown tables `fields8_tables.md`, and prints the counts after each
fold."""
import csv

SRC = 'scratch/leaf-fold7/fields7.tsv'
D = 'scratch/leaf-fold8/'

REMOVED = {
    'height': [('R', 'r18'), ('R', 'r19'), ('R', 'r20'), ('R', 'r21'), ('R', 'r22'), ('R', 'h5fin')],
    'qm-glue': [('A', 'valenceFormulaGammaStar'), ('A', 'qmHauptmodulBase3')],
    'contrib': [('T', 't3Surj'), ('T', 't11bExists'), ('T', 't24'), ('A', 'zariskiConnectedness'),
                ('A', 'egaIV_8_8_2_ii'), ('A', 'egaIV_17_7_8_ii')],
}
HS = '_root_.ZInQ.HeightSplit.'
HREP = 'r18-r22, h5fin (the eight together, with N1 from neronSchemeExtensionExists and T35 from h38)'
ADDED = {
    'height': [
        ('R', 'semistableReductionThm', HS + 'SemistableReductionThm', 'consequence of one theorem',
         'SGA 7 I Exp. IX Thm 3.6 (Grothendieck semistable reduction) in global form: good reduction outside '
         'finitely many primes and SGA 7 IX 3.3 (height-split §1)', 'height-split; folded by leaf-fold8', HREP),
        ('R', 'semistableNeronBaseChange', HS + 'SemistableNeronBaseChange', 'consequence of one theorem',
         'SGA 7 I Exp. IX Prop. 3.3 / Cor. 3.3.1, in the open-subgroup form of the kernel\'s N2 (identity component: '
         'SGA 3 VI_B 3.10)', 'height-split; folded by leaf-fold8', HREP),
        ('R', 'semistablePersists', HS + 'SemistablePersists', 'consequence of one theorem',
         'SGA 7 I Exp. IX 3.3 (semistability persists under finite extension), global form',
         'height-split; folded by leaf-fold8', 'r20 (with faltingsLemma5BC)'),
        ('R', 'bostLowerBound', HS + 'BostLowerBound', 'published form',
         'Bost, Sem. Bourbaki 795 (Asterisque 237, 1996): h_D(A) >= -(g/2) log 2pi, Deligne normalization '
         '(display UNVERIFIED, height-split §2)', 'height-split; folded by leaf-fold8', 'r21'),
        ('R', 'javanpeykarBound', HS + 'JavanpeykarBound', 'published form (specialization)',
         'Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 (read by the audit), for curves over K with a '
         'K-rational Belyi function, over the published stable height', 'height-split; folded by leaf-fold8', 'r18'),
        ('R', 'faltingsLemma5BC', HS + 'FaltingsLemma5BC', 'consequence of one theorem',
         'Faltings 1983 Lemma 5 in the semistable inequality form (Pazuki 2012 Rem. 2.3; Raynaud, Asterisque 127 '
         'VII Cor. 2.1.3 is the operative source, height-split §8), applied over every number field L above K',
         'height-split; folded by leaf-fold8', 'r20'),
        ('R', 'pazukiCor13Upper', HS + 'PazukiCor13Upper', 'published form (half)',
         'Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), upper half (read by the audit; RISK: Pazuki\'s level-2 '
         'coordinates, height-split §8)', 'height-split; folded by leaf-fold8', 'r22'),
        ('R', 'gaudronRemondThm14', HS + 'GaudronRemondThm14', 'published form',
         'Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the audit), over the published stable height',
         'height-split; folded by leaf-fold8', 'r19 (same statement over the kernel infimum)'),
    ],
    'qm-glue': [
        ('A', 'valenceFormulaCocompactEq', 'LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq', 'published form',
         'valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4), '
         'over Mathlib\'s invariant measure on the upper half plane and a genuine fundamental domain',
         'qm-split, qm-glue; folded by leaf-fold8',
         'valenceFormulaGammaStar (consequence), qmHauptmodulBase3 (composite), with the next two'),
        ('A', 'shimizuCovolumeO1', 'LeafQCheck.HM.QMSplit.ShimizuCovolumeO1', 'published form',
         'iota(O^1) is cocompact Fuchsian with covolume 2pi/3 (Shimura 1971 Prop. 9.2; Shimizu 1965; Voight '
         'Thm 39.1.13)', 'qm-split, qm-glue; folded by leaf-fold8',
         'valenceFormulaGammaStar, qmHauptmodulBase3 (GammaStarFromO1 proved by qm-glue)'),
        ('A', 'igusaCMValue24', 'LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24', 'published form',
         'Lin-Yang 2020 eqs. (2), (14) at the Baba-Granath CM value j = -16/27 (discriminant -24; Baba-Granath '
         '2008 Thm 2.1, Elkies 1998), Lauter-Naehrig-Yang 2015 §2.2 conventions; the manuscript\'s citation '
         '(l.908-923); equivalent to the old glue ThetaQuotientValue24', 'qm-glue; folded by leaf-fold8',
         'qmHauptmodulBase3 (with igusaPsi4, igusaChi10 and the previous two)'),
    ],
    'contrib': [],
}
ORDER = ['height', 'qm-glue', 'contrib']
BUNDLES = [('R', 'OpenResearchLeaves8'), ('T', 'OpenTextbookLeaves8'), ('A', 'OpenAddedLeaves8'),
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

table = [('leaf-fold7 (`sixContactMin_of_open7`)', counts(rows))]
for step in ORDER:
    rem = set(REMOVED[step])
    assert all(any((r['bundle'], r['field']) == x for r in rows) for x in rem), step
    rows = [r for r in rows if (r['bundle'], r['field']) not in rem]
    for a in ADDED[step]:
        rows.append(dict(zip(['bundle', 'field', 'type', 'form', 'source', 'task', 'replaces'], a)))
    table.append((step, counts(rows)))

with open(D + 'fields8.tsv', 'w') as f:
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
open(D + 'fields8_tables.md', 'w').write('\n'.join(out))

print('| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |')
print('|---|---|---|---|---|---|---|---|')
for name, (n, c, s, l) in table:
    print(f"| {name} | {n} | {c['pub']} | {c['c']} | {c['comp']} | {c['pg']} | {s[0]} / {s[1]} | {l[0]} / {l[1]} |")
