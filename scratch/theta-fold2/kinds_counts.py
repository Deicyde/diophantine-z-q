import csv, collections, sys
rows = list(csv.DictReader(open('docs/one-proof/kinds.tsv'), delimiter='\t'))
H = [r for r in rows if r['bundle'] in ('research', 'added', 'textbook', 'glue')]
print('rows', len(rows), 'H rows', len(H), collections.Counter(r['bundle'] for r in rows))
for col in ('strict', 'strictest'):
    print(col, 'H', dict(collections.Counter(r[col] for r in H)), 'all', dict(collections.Counter(r[col] for r in rows)))
