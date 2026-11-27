"""Unit tests of render_open.py: the LEAF/GLUE scoring rule (ruling 2026-11-17: unread and unverified rows count as
glue), reading the tables as raw text, claims.tsv rows of hypotheses that are no longer open, volatile.tsv rows,
and the claims-sync lag.

Run: python3 -I scripts/one_proof/test_scoring.py   (or pytest scripts/one_proof/test_scoring.py)
"""
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import render_open  # noqa: E402


def row(flag, strict='LEAF', strictest='LEAF', kind='published', flag_class='unread'):
    return dict(bundle='research', field='x', kind=kind, flag=flag, strict=strict, strictest=strictest,
                source='', rated_by='', packet='', label='', tier='', flag_class=flag_class,
                area_issue='elliotglazer/diophantine-z-q#1')


def test_unread_published_row_scores_glue():
    assert render_open.must_be_glue('unread: new printed leaf, no reading recorded')
    probs = render_open.kinds_row_problems(row('unread: new printed leaf'), [], set())
    assert any('counts GLUE' in p for p in probs), probs
    assert not [p for p in render_open.kinds_row_problems(row('unread: new printed leaf', 'GLUE', 'GLUE'), [], set())
                if 'counts GLUE' in p]


def test_each_marker():
    for m in ('unread', 'locator UNVERIFIED', 'recalled from memory', 'one model review', 'pending reading: x',
              'pending review (new leaf)'):
        assert render_open.must_be_glue(m), m


def test_read_row_keeps_leaf():
    flag = 'reading 11-17: direct instance of the printed proposition, p. 366'
    assert not render_open.must_be_glue(flag)
    assert not [p for p in render_open.kinds_row_problems(row(flag, flag_class='note'), [], set()) if 'counts GLUE' in p]


ISSUES = {'claims_issue': 'o/r#14', 'statement_checks_issue': '', 'packet_issues': {}, 'log_issue': 'o/r#3'}


def claim(field, hold='held', url='https://github.com/o/r/pull/9'):
    return dict(field=field, task='', status='', since='2026-11-17', issue='', holder_kind='project',
                public_holder='project', claim_url=url, hold=hold)


def board(claims_rows=(), volatile=()):
    """What render_open.validate and render read: open rows a (project interest), b and c (packet R2, unread) and
    the manuscript hypothesis hPC; volatile is a list of (field, note)."""
    kinds_rows = [dict(row('reading: p. 1', flag_class='note'), field='a', label='project-interest', source='Src'),
                  dict(row('unread: locator', 'GLUE', 'GLUE'), field='b', packet='R2', source='SGA 3'),
                  dict(row('unread: locator', 'GLUE', 'GLUE'), field='c', packet='R2', source='EGA IV'),
                  dict(row('reading: p. 2', flag_class='note'), field='hPC', bundle='frozenTarget', source='Thm')]
    return dict(hyps=[dict(field=r['field'], bundle=r['bundle'], type='True', docstring='') for r in kinds_rows],
                kinds={r['field']: r for r in kinds_rows}, kinds_rows=kinds_rows, claims_rows=list(claims_rows),
                reviews=[], credits=[], volatile={f: dict(field=f, note=n, since='2026-11-18') for f, n in volatile},
                issues=dict(ISSUES))


def test_tables_are_read_as_raw_text():
    # a cell that starts with a double quote keeps it and does not swallow the rows after it
    with tempfile.TemporaryDirectory() as tmp:
        vol, cl = os.path.join(tmp, 'volatile.tsv'), os.path.join(tmp, 'claims.tsv')
        with open(vol, 'w') as fh:
            fh.write('field\tnote\tsince\n'
                     'fooA\t"renamed by fold-x\t2026-11-18\n'
                     'fooB\tremoved by fold-x\t2026-11-18\n')
        with open(cl, 'w') as fh:
            fh.write('field\tstatus\thold\n'
                     'x1\t"Lemma 2 fails\treleased\n'
                     'x2\tworking on it\theld\n')
        vrows, crows = render_open.read_tsv(vol), render_open.read_tsv(cl)
    assert [(r['field'], r['note']) for r in vrows] == [('fooA', '"renamed by fold-x'), ('fooB', 'removed by fold-x')]
    assert [(r['field'], r['hold']) for r in crows] == [('x1', 'released'), ('x2', 'held')]


def test_claims_row_of_a_closed_field_is_skipped():
    m = board([claim('dischargedX', url='https://github.com/o/r/tree/wip/x')])
    assert render_open.validate(m) == []
    open_md, _, _ = render_open.render(m)
    assert 'dischargedX' not in open_md
    assert '\nNothing is held.\n' in open_md
    # the other claims.tsv checks still apply to such a row
    assert any('hold must be one of' in p for p in render_open.validate(board([claim('dischargedX', hold='bogus')])))


def test_volatile_rows_are_not_offered():
    m = board([claim('hPC')], volatile=[('a', 'renamed by fold-x'), ('c', ''), ('hPC', '')])
    assert render_open.validate(m) == []
    open_md, pages, _ = render_open.render(m)
    # a project-interest row and an open row are no longer offered; a held row keeps its holder
    assert '* Status: may change soon, not offered: renamed by fold-x.' in open_md
    assert '| 0 | may change soon, not offered: renamed by fold-x |' in open_md
    assert '* Status: may change soon, not offered.' in open_md
    assert '* Status: held by the project ([claim](https://github.com/o/r/pull/9)) (may change soon).' in open_md
    assert '* Status: open.' in open_md
    # the volatile project-interest row's label is shown without its offer
    assert 'label project-interest (project interest, free to claim)' not in open_md
    assert 'label project-interest' in open_md
    # the Packets lists mark volatile rows, and pages-wanted.md leaves them out
    assert '* [`c`](#c) (GLUE; unread) (may change soon): EGA IV' in open_md
    assert '* [`b`](#b) (GLUE; unread): SGA 3' in open_md
    assert '[`b`](OPEN.md#b)' in pages and '[`c`](OPEN.md#c)' not in pages



def review(field, commit, edition, quote, evidence='AI-READ'):
    return dict(field=field, commit=commit, reader='AI review', known_reader='', edition=edition, page='1',
                display='', copy='scan', quote=quote, verdict='YES', not_read='', ai_use='whole reading by AI',
                relayed_by='', url='', ruling='', ruled_by='', evidence=evidence)


def test_real_text_rule():
    """An AI-READ row names the copy read (sha256) and quotes it (2026-11-26); legacy rows are only noted."""
    m = board()
    m['reviews'] = [review('a', 'abc1234', 'J. 1 (2000), scan sha256 0123abcd', '"the printed words"'),
                    review('b', 'abc1234', 'J. 1 (2000), scan', '"the printed words"'),
                    review('c', 'abc1234', 'J. 1 (2000), scan sha256 0123abcd', ''),
                    review('a', 'abc1234', 'J. 1 (2000), scan', '', evidence='HUMAN-READ')]
    probs = [p for p in render_open.validate(m) if 'real-text rule' in p]
    assert len(probs) == 2 and 'b: ' in probs[0] and 'sha256' in probs[0] and 'c: ' in probs[1], probs
    legacy = sorted(render_open.LEGACY_AI_READS)[0]
    assert render_open.real_text_missing(review(legacy[0], legacy[1] + ' (re-read)', 'scan', ''))
    m['reviews'] = [review('a', legacy[1] + ' (re-read)', 'scan', '')]
    m['reviews'][0]['field'] = legacy[0]
    assert not [p for p in render_open.validate(m) if 'real-text rule' in p]


def test_claims_lag_is_a_note():
    """After a claims sync OPEN.md lags claims.tsv until the next fold: tolerated; any other difference is not."""
    old = board()
    open_md, pages, _ = render_open.generated(old)
    synced = board([claim('b')])                       # the sync adds a claim; nothing else changes
    assert render_open.generated(synced)[0] != open_md
    assert render_open.claims_lag_only(synced, open_md, pages)
    assert render_open.claims_lag_only(old, open_md, pages)
    relabeled = board([claim('b')])                    # a kinds.tsv change as well: not a claims-only lag
    relabeled['kinds']['c']['label'] = 'good-first'
    assert not render_open.claims_lag_only(relabeled, open_md, pages)
    restrict = board()                                 # a kinds.tsv change alone
    restrict['kinds']['a']['strictest'] = 'GLUE'
    assert not render_open.claims_lag_only(restrict, open_md, pages)
    assert not render_open.claims_lag_only(synced, open_md.replace('open', 'opne', 1), pages)  # hand edit
    assert not render_open.claims_lag_only(synced, open_md, pages + 'x\n')
    assert not render_open.claims_lag_only(synced, open_md.split('<!-- render stamp')[0], pages)  # no stamp

if __name__ == '__main__':
    for name, fn in list(globals().items()):
        if name.startswith('test_'):
            fn()
            print('ok', name)
