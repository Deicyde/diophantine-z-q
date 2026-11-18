#!/usr/bin/env python3
"""fold-b116 items 4 and 5: kinds.tsv / claims.tsv row edits (text only; no rating changes), reproducible.

    python3 scratch/fold-b116/rows_items45.py logp     # item 4: inbox 82's optional flag narrowing (panPrintedF, bergerSurveyF)
    python3 scratch/fold-b116/rows_items45.py docs     # item 5: inbox 78 items 1-2 and inbox 80 (claims.tsv)

Each edit checks that its old text occurs exactly once and stops otherwise.
"""
import sys

KP, CP = 'docs/one-proof/kinds.tsv', 'docs/one-proof/claims.tsv'


def die(m):
    sys.exit('rows_items45: ' + m)


def load(p):
    lines = open(p).read().split('\n')
    return lines, {c: i for i, c in enumerate(lines[0].split('\t'))}


def row_index(lines, field):
    hits = [i for i, l in enumerate(lines) if l.split('\t')[1:2] == [field] or l.split('\t')[:1] == [field]]
    if len(hits) != 1:
        die(f'expected one row {field}, found {len(hits)}')
    return hits[0]


def edit(lines, ix, field, col, old, new):
    i = row_index(lines, field)
    r = lines[i].split('\t')
    if old is None:
        r[ix[col]] = new
    else:
        if r[ix[col]].count(old) != 1:
            die(f'{field}.{col}: expected one occurrence of {old[:70]!r}')
        r[ix[col]] = r[ix[col]].replace(old, new)
    lines[i] = '\t'.join(r)


def logp():
    lines, ix = load(KP)
    old = '(BergerBst.LogPTildeTranscendental is an open Prop)'
    new = ('(BergerBst.LogPTildeTranscendental is an open Prop, reduced in Lean to log[p~] not in Frac(B_max) '
           '(LogPTransc.logPTildeTranscendental_iff_notInFrac, Contrib/OneProof/LogPTranscendenceBdR.lean))')
    for f in ('panPrintedF', 'bergerSurveyF'):
        edit(lines, ix, f, 'flag', old, new)
    open(KP, 'w').write('\n'.join(lines))
    print('item 4: panPrintedF, bergerSurveyF flags narrowed')


def docs():
    lines, ix = load(KP)
    # inbox 78 item 1: javanpeykarThm111An
    f = 'javanpeykarThm111An'
    edit(lines, ix, f, 'flag', '(Szpiro, Asterisque 127, Lemme 3.2.1, Ch. I)',
         '(Szpiro (ed.), Asterisque 127, Chap. I, Lemme 3.2.1)')
    edit(lines, ix, f, 'flag', 'reading risk: R3\' closed', 'R3\' closed')
    i = row_index(lines, f)
    r = lines[i].split('\t')
    r[ix['flag']] += ('; locators page-checked 11-17: arXiv v1 p. 1 (Thm 1.1.1), p. 9 (§2.3); ANT p. 90; ANT p. 98 not '
                      'reachable, arXiv v1 is the cited print')
    r[ix['flag_class']] = 'note'
    lines[i] = '\t'.join(r)
    # inbox 78 item 2: locators (rows already LEAF/LEAF)
    edit(lines, ix, 'r9a', 'source', 'Faltings 1983 Satz 3', 'Faltings 1983 §5 Endomorphismen, Satz 3, p. 360')
    edit(lines, ix, 'r9b', 'source', 'Faltings 1983 Satz 4, Kor. 1', 'Faltings 1983 §5, Satz 4 p. 360 and Korollar 1 p. 361')
    edit(lines, ix, 'dsThm966Printed', 'source', 'Deligne-Serre 1974 Thm 4.1 (4.1.1), pp. 513-514',
         'Deligne-Serre, Thm 4.1 with (4.1.1), pp. 513-514')
    i = row_index(lines, 'dsThm966Printed')
    r = lines[i].split('\t')
    r[ix['flag']] += " (print not in the manuscript's bibliography)"
    lines[i] = '\t'.join(r)
    open(KP, 'w').write('\n'.join(lines))
    # inbox 80: claims.tsv: the hPC project row (hand edit authorized); pazuki row dropped (no activity after
    # 11-17 12:00 PST on origin/wip/pazuki-inputs or pazuki-route); no PoincareComplement row (not an OPEN.md field)
    cl, cix = load(CP)
    cl = [l for l in cl if not l.startswith('pazukiCor13Upper\t')]
    if any(l.startswith('hPC\t') for l in cl):
        die('claims.tsv already has an hPC row')
    row = {c: '' for c in cix}
    row.update(field='hPC', task='#83 / PR #90 (Theorem 5.3 headline)', status='PR #90 under review',
               holder_kind='project', public_holder='project',
               claim_url='https://github.com/Deicyde/diophantine-z-q/pull/90', hold='held')
    body = [l for l in cl[1:] if l.strip()]
    body.append('\t'.join(row[c] for c in sorted(cix, key=cix.get)))
    open(CP, 'w').write('\n'.join([cl[0]] + body) + '\n')
    print('item 5: javanpeykarThm111An, r9a, r9b, dsThm966Printed edited; claims.tsv: hPC added, pazuki dropped')


if __name__ == '__main__':
    {'logp': logp, 'docs': docs}[sys.argv[1]]()
