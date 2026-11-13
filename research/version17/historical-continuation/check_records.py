"""Continue four historical navigation, selector and policy identities across Version 17."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD = 'research/quartic214-main-integration/check_historical_records.py'
NAVIGATION = {'README.md', '.github/workflows/quartic214-manuscript.yml'}
SELECTOR_POLICY = {'docs/current-manuscript.json', 'docs/release-policy.md'}
DOMAIN = NAVIGATION | SELECTOR_POLICY
AUTHORS = ['/root', '/root/pr30_final_repair_review']


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def pin(path):
    data = (ROOT / path).read_bytes()
    return {'path': path, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)}


def check_pin(item):
    require(set(item) == {'path', 'sha256', 'bytes'}, 'invalid-binding')
    path = Path(item['path'])
    require(not path.is_absolute() and '..' not in path.parts and '\\' not in item['path'], 'unsafe-binding')
    require(pin(item['path']) == item, 'stale-binding:' + item['path'])


def check_domain(mapping):
    require(set(mapping) == DOMAIN, 'undeclared-historical-substitution')


def router(original, mapping):
    check_domain(mapping)
    def resolve(base, path):
        # Do not redirect aliases, other roots, absolute paths or proof files.
        if base == ROOT and path in NAVIGATION:
            return mapping[path]
        return original(base, path)
    return resolve


def check_review(review, record):
    require(review is not None, 'missing-independent-review')
    require(review.get('schema') == 'v17-navigation-continuation-review/v1', 'wrong-review-schema')
    require(review.get('authors') == AUTHORS and isinstance(review.get('reviewer'), str)
            and review['reviewer'] not in AUTHORS and review['reviewer'].strip(), 'self-or-misattributed-review')
    require(review.get('decision') == 'accepted-at-stated-scope', 'nonaccepting-review')
    require(review.get('controller_acceptance') is False and review.get('mathematical_acceptance_renewed') is False,
            'unsupported-acceptance')
    require(review.get('historical_substitutions') == sorted(DOMAIN), 'wrong-review-domain')
    require(isinstance(review.get('limitations'), list) and review['limitations'], 'missing-review-limitations')
    require(review.get('record') == pin('research/version17/historical-continuation/CONTINUATION.json'), 'stale-review-record')


def load_record():
    record = json.loads((HERE / 'CONTINUATION.json').read_text())
    require(record['schema'] == 'v17-navigation-continuation/v1' and record['authors'] == AUTHORS, 'wrong-record')
    require(record['historical_substitutions'] == sorted(DOMAIN)
            and record['mathematical_acceptance_renewed'] is False, 'wrong-record-scope')
    expected = set(json.loads((HERE / 'FROZEN.json').read_text())) | DOMAIN | {
        'research/version17/historical-continuation/' + name for name in
        ('check_records.py', 'FROZEN.json', 'README.md', 'historical/README.md', 'historical/quartic214-manuscript.yml',
         'historical/current-manuscript.json', 'historical/release-policy.md')} | {
             'scripts/check_version_increment.py', 'scripts/test_version_increment.py',
             'scripts/check_current_manuscript.py', '.github/workflows/research-checks.yml'}
    require(len(record['bindings']) == len(expected) and {p['path'] for p in record['bindings']} == expected,
            'incorrect-record-bindings')
    for item in record['bindings']:
        check_pin(item)
    frozen = json.loads((HERE / 'FROZEN.json').read_text())
    for path, digest in frozen.items():
        require(pin(path)['sha256'] == digest, 'changed-old-authority:' + path)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--reviewed-artifacts', action='store_true')
    modes.add_argument('--author-check', action='store_true')
    args = parser.parse_args()
    record = load_record()
    if args.reviewed_artifacts:
        receipt = HERE / 'REVIEW.json'
        check_review(json.loads(receipt.read_text()) if receipt.is_file() else None, record)
    spec = importlib.util.spec_from_file_location('unchanged_main_integration', ROOT / OLD)
    old = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(old)
    mapping = {key: HERE / 'historical' / Path(key).name for key in DOMAIN}
    # Independently reproduce what the old checker expects before installing the
    # exact navigation adapter. Its own archives and authority checks remain active.
    old.check_current(old.exact_archives(), {key: mapping[key].read_bytes() for key in NAVIGATION})
    original = old.safe
    old.safe = router(original, mapping)
    original_loader = old.original_checker
    def historical_checker():
        module = original_loader()
        original_read = module.read
        def read(path, overrides):
            if path in SELECTOR_POLICY and path not in overrides:
                return mapping[path].read_bytes()
            return original_read(path, overrides)
        module.read = read
        return module
    old.original_checker = historical_checker
    # The historical selector is evidence only. Validate the real current pair
    # separately; the Research checks job enforces its trusted publication base.
    sys.path.insert(0, str(ROOT / 'scripts'))
    import check_current_manuscript
    check_current_manuscript.validate(ROOT)
    controls = []
    if args.self_test:
        def rejects(name, action):
            try:
                action()
            except ValueError:
                controls.append(name)
            else:
                raise ValueError('negative-control-not-rejected:' + name)
        rejects('arbitrary-proof-substitution', lambda: router(original, dict(mapping, **{'manuscripts/quartic_v16.tex': HERE / 'fake'})))
        rejects('missing-navigation-substitution', lambda: router(original, {}))
        proof = 'manuscripts/quartic_v16.tex'
        require(old.safe(ROOT, proof) == original(ROOT, proof), 'proof-read-redirected')
        require(old.safe(HERE, 'README.md') == original(HERE, 'README.md'), 'other-root-redirected')
        controls.extend(['ordinary-proof-path-live', 'other-root-live'])
        rejects('missing-review', lambda: check_review(None, record))
        rejects('nonaccepting-review', lambda: check_review({'schema': 'v17-navigation-continuation-review/v1', 'authors': AUTHORS, 'reviewer': '/independent-test', 'decision': 'rejected'}, record))
        for author in AUTHORS:
            rejects('self-review-' + author, lambda a=author: check_review({'schema': 'v17-navigation-continuation-review/v1', 'authors': AUTHORS, 'reviewer': a}, record))
        rejects('changed-current-navigation', lambda: check_pin({'path': 'README.md', 'sha256': '0' * 64, 'bytes': 0}))
    saved = sys.argv
    try:
        # Always require the real prior independent receipt, even in the new
        # author's pre-review mode. Never synthesize an old or new approval.
        sys.argv = [str(ROOT / OLD), '--reviewed-artifacts'] + (['--self-test'] if args.self_test else [])
        old.main()
    finally:
        sys.argv = saved
        old.safe = original
        old.original_checker = original_loader
    print(json.dumps({'status': 'PASS', 'scope': 'Four historical navigation/selector/policy identities only; all mathematical reads remain current.',
                      'review_mode': 'independently reviewed' if args.reviewed_artifacts else 'author check; no new independent acceptance',
                      'negative_controls': controls, 'mathematical_acceptance_renewed': False,
                      'controller_acceptance': False}, indent=2))


if __name__ == '__main__':
    main()
