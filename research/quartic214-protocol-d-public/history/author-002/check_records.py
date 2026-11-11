#!/usr/bin/env python3
"""Finite Protocol D record consistency; no mathematical or controller attestation."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import re
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
RECORD = HERE / 'RECORDS.json'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()

class Invalid(ValueError):
    pass

def require(test, message):
    if not test:
        raise Invalid(message)

def resolve(path):
    require(isinstance(path, str) and path, 'missing path')
    p = Path(path)
    require(not p.is_absolute() and '..' not in p.parts, 'non-portable path: ' + path)
    full = ROOT / p
    require(full.resolve().is_relative_to(ROOT.resolve()), 'path escapes repository')
    return full

def read(path, overrides):
    return overrides[path] if path in overrides else resolve(path).read_bytes()

def pin_check(pin, overrides):
    data = read(pin['path'], overrides)
    require(digest(data) == pin['sha256'], 'stale bound source: ' + pin['path'])
    if 'bytes' in pin:
        require(len(data) == pin['bytes'], 'byte count: ' + pin['path'])
    if 'lines' in pin:
        lo, hi = pin['lines']
        lines = data.splitlines(keepends=True)
        require(1 <= lo <= hi <= len(lines), 'invalid passage range')
        expected = pin.get('passage_sha256', pin.get('excerpt_sha256'))
        require(digest(b''.join(lines[lo-1:hi])) == expected, 'stale passage: ' + pin['path'])
    return data

def walk_pins(value, overrides):
    if isinstance(value, dict):
        if 'path' in value and 'sha256' in value:
            pin_check(value, overrides)
        for child in value.values():
            walk_pins(child, overrides)
    elif isinstance(value, list):
        for child in value:
            walk_pins(child, overrides)

def indexed(items, label):
    result = {x['id']: x for x in items}
    require(len(result) == len(items), 'duplicate ' + label)
    return result

def review_records():
    records = []
    folder = HERE / 'review'
    if folder.exists():
        for path in sorted(folder.glob('*.json')):
            item = json.loads(path.read_text())
            # Only explicit decision objects participate. Other reviewer evidence may use another schema.
            if isinstance(item, dict) and 'decision' in item and 'reviewer' in item and 'bound_files' in item:
                records.append(item)
    return records

def validate(record, reviews=None, overrides=None):
    overrides = overrides or {}
    reviews = review_records() if reviews is None else reviews
    require(record['schema'] == 'quartic214-public-integration-records/v1', 'unknown schema')
    authors = set(record['authors'])
    require(authors, 'missing authors')
    pins = {p['path']: p for p in record['files']}
    require(len(pins) == len(record['files']), 'duplicate file pin')
    walk_pins(record, overrides)
    initial = json.loads(read(record['source_history']['initial_reconstruction'], overrides))
    initial_ids = {x['id'] for x in initial['entries']}
    require(len(initial_ids) == len(initial['entries']), 'duplicate initial source-use ID')
    recon = {x['initial_id']: x for x in record['initial_reconciliation']}
    require(len(recon) == len(record['initial_reconciliation']) and set(recon) == initial_ids, 'initial reconciliation coverage')
    uses = indexed(record['uses'], 'use')
    suppliers = indexed(record['suppliers'], 'supplier')
    connections = indexed(record['connections'], 'connection')
    apps = {x['path']: x for x in record['applications']}
    require(len(apps) == len(record['applications']), 'duplicate application')
    app_ids = set()
    for path, app in apps.items():
        require(path in pins, 'unbound application')
        data = pin_check(app, overrides)
        contract = json.loads(data)
        app_ids.add(contract['application_id'])
        require(app['application_id'] == contract['application_id'], 'application id mismatch')
        obligations = contract['obligations']
        require(len(obligations) == 9, 'nine obligations required: ' + path)
        groups = [
            {'sourcehypotheses'}, {'constructedobjects'},
            {'domainindexcoverage','indexdomaincoverage','domainandindexcoverage'},
            {'transitioncomparisonmaps','transitionmaps','transitionandcomparisonmaps'},
            {'identityconsumedobject','consumedobjectidentity','identityofconsumedobject','identityoftheconsumedobject'},
            {'coefficientnormalization','coefficientconventions','coefficientsandnormalizations','coefficientandnormalizationconventions'},
            {'localconditions'}, {'exceptionalcases'}, {'downstreamconsumption'}]
        names = {re.sub('[^a-z]', '', name.lower()) for name in obligations}
        require(all(len(names & group) == 1 for group in groups), 'nine named semantic obligations required: '+path)
        for obligation in obligations.values():
            for field in ['required_input', 'constructed_input', 'justification', 'source_references', 'evidence']:
                require(bool(obligation.get(field)), 'incomplete application obligation: ' + field)
        require(contract.get('independent_acceptance') is None, 'author contract must not generate independent acceptance')
        for who in contract.get('authors', []):
            authors.add(who)
        if contract.get('public_port_author'):
            authors.add(contract['public_port_author'])
        for field in ['manuscript','proof','construction_passages','application_passages','consumer_passages','required_sources','obligations']:
            require(bool(contract.get(field)), 'missing application boundary: ' + field)
            walk_pins(contract[field], overrides)
    for sid, supplier in suppliers.items():
        require(digest(canonical(supplier['output'])) == supplier['contract_sha256'], 'supplier contract hash')
        for field in ['token','assertion','domain','identity','normalization']:
            require(bool(supplier['output'].get(field)), 'incomplete supplier output')
    for uid, use in uses.items():
        require(use['application'] in apps, 'missing application for use: ' + uid)
        require(use['supplier_id'] in suppliers, 'missing actual direct supplier: ' + uid)
        require(use['connection_id'] in connections, 'missing direct edge: ' + uid)
        supplier = suppliers[use['supplier_id']]
        edge = connections[use['connection_id']]
        require(edge['use_id'] == uid and edge['supplier_id'] == supplier['id'], 'edge identity mismatch')
        require(edge['consumer'] == use['consumer'], 'edge wrong consumer')
        derivation = edge['derivation']
        require(edge['bridge'] == derivation['passage'], 'edge wrong connecting derivation')
        require(derivation['mode'] in ['identity','derived'], 'unknown connection mode')
        require(bool(derivation['argument_summary']), 'missing connecting argument')
        require(derivation['input_supplier_contract_sha256'] == supplier['contract_sha256'], 'stale derivation supplier binding')
        require(digest(canonical(derivation)) == edge['derived_contract_sha256'] == use['derived_contract_sha256'], 'stale derived-output binding')
        require(use['supplier_contract_sha256'] == supplier['contract_sha256'], 'stale supplier-to-consumer contract: ' + uid)
        pairs = [('needed_token','token'),('needed_assertion','assertion'),('needed_identity','identity'),('needed_domain','domain')]
        for left, right in pairs:
            require(use[left] == derivation['output'][right], 'derived-output/consumer contract mismatch: ' + uid)
        require(edge['available_token'] == supplier['output']['token'], 'available supplier token mismatch')
        require(edge['needed_token'] == use['needed_token'], 'needed derived token mismatch')
        require(edge['available_assertion'] == supplier['output']['assertion'], 'literal available assertion mismatch')
        require(edge['needed_assertion'] == use['needed_assertion'], 'derived needed assertion mismatch')
        if derivation['mode'] == 'identity':
            require(all(derivation['output'][key] == supplier['output'][key] for key in ['assertion','domain','identity','normalization']), 'identity connection silently strengthened supplier')
        require(edge['identity_check'] == use['needed_identity'] and edge['domain_check'] == use['needed_domain'], 'connection identity/domain mismatch')
        require(bool(edge['map_check']), 'missing transition map comparison')
    require({e['use_id'] for e in connections.values()} == set(uses), 'extra or omitted direct edge')
    require({u['supplier_id'] for u in uses.values()} == set(suppliers), 'unconsumed extra supplier')
    for iid, item in recon.items():
        require(item['disposition'] in ['mapped','excluded_from_214'], 'unresolved required reconciliation: ' + iid)
        require(bool(item['reason']), 'unjustified reconciliation')
        if item['disposition'] == 'mapped':
            require(bool(item['current_use_ids']), 'deleted required initial use')
            for uid in item['current_use_ids']:
                require(uid in uses and uses[uid]['origin_initial_id'] == iid, 'missing reconciled use: ' + iid)
        else:
            require(iid in {'1.2','2.7','3.8'} and not item['current_use_ids'], 'unsupported initial exclusion')
    coverage = indexed(record['coverage'], 'coverage')
    covered = {}
    for c in coverage.values():
        require(c['path'] in pins and c['sha256'] == pins[c['path']]['sha256'], 'coverage source pin missing')
        lo, hi = c['lines']
        require(lo == covered.get(c['path'], 0)+1, 'coverage overlap or gap: ' + c['path'])
        covered[c['path']] = hi
        require(c['classification'] in ['current_inference_or_supplier','application_scoped_source_or_argument','historical_or_scope_nonderivation','historical_superseded_derivation'], 'unclassified coverage passage')
        require(bool(c['classification_reason']), 'unexplained coverage classification')
        linked = c['use_ids'] + c['supplied_to_use_ids'] + c['derivation_use_ids'] + c['premise_use_ids']
        require(bool(linked or c['application_ids']) or c['classification'].startswith('historical'), 'unlinked substantive coverage passage')
        for uid in linked:
            require(uid in uses, 'coverage references deleted use: ' + uid)
        for uid in c['use_ids']:
            use = uses[uid]
            require(use['consumer']['path'] == c['path'], 'coverage wrong consumer')
        require(set(c['application_ids']) <= app_ids, 'coverage references unknown application')
    expected = {'research/quartic214/PROOF.md'}
    expected |= {str(p.relative_to(ROOT)) for p in (ROOT/'research/quartic214/proofs').glob('*.md')}
    expected |= {str(p.relative_to(ROOT)) for p in (ROOT/'research/quartic214/sources').glob('*') if p.suffix in ['.md','.tex']}
    require(set(covered) == expected, 'complete declared public proof-file coverage missing')
    for path, last in covered.items():
        require(last == len(read(path, overrides).splitlines()), 'incomplete line coverage: ' + path)
    require(set(uses) == {u for c in coverage.values() for u in c['use_ids']}, 'use omitted from consumer coverage')
    require({f['id'] for f in record['findings']}, 'findings ledger missing')
    for finding in record['findings']:
        require(finding['decision'] is None, 'author must not close finding by own verdict')
        for field in ['historical_disposition','current_author_response','consuming_passage']:
            require(bool(finding.get(field)), 'incomplete finding history/current distinction')
    accepted_scopes = set()
    for review in reviews:
        reviewer = review['reviewer']
        require(isinstance(reviewer, str) and reviewer not in authors, 'self approval or unknown reviewer identity')
        require(review['role'] == 'non-author internal model reviewer', 'review role not explicit')
        require(review['decision'] in ['accepted','pending','rejected'], 'unknown review decision')
        require(isinstance(review['bound_files'], dict) and review['bound_files'], 'unbound review')
        for path, expected_hash in review['bound_files'].items():
            require(digest(read(path, overrides)) == expected_hash, 'stale reviewer binding: ' + path)
        if review['decision'] == 'accepted':
            required = set(pins) | {str(RECORD.relative_to(ROOT)), str((HERE/'check_records.py').relative_to(ROOT)), str((HERE/'CHECKER.md').relative_to(ROOT))}
            require(required <= set(review['bound_files']), 'accepted public decision lacks frozen source/record/contract coverage')
            accepted_scopes.update(review['scopes'])
    return {'structural_status':'PASS', 'uses':len(uses), 'coverage_passages':len(coverage),
            'applications':len(apps), 'accepted_scopes':sorted(accepted_scopes),
            'pending_scopes':sorted(set(record['required_review_scopes'])-accepted_scopes),
            'controller_eligibility':'not attested; protected controller/App decision required',
            'mathematical_truth':'not decided by this checker'}

def self_test(record):
    """Mutations are in memory; synthetic review objects are never acceptance artifacts."""
    count = 0
    def reject(name, edit=None, reviews=None, overrides=None):
        nonlocal count
        item = copy.deepcopy(record)
        if edit:
            edit(item)
        try:
            validate(item, reviews=[] if reviews is None else reviews, overrides=overrides)
        except (Invalid, KeyError, FileNotFoundError):
            count += 1
        else:
            raise Invalid('negative control accepted: ' + name)
    for kind in ['named-theorem','section-only','unnamed-estimate']:
        uid = next(u['id'] for u in record['uses'] if u['kind'] == kind)
        reject('missing '+kind+' edge', lambda d, uid=uid:d['connections'].__setitem__(slice(None),[e for e in d['connections'] if e['use_id'] != uid]))
    reject('deleted use with coverage', lambda d:d['uses'].pop())
    reject('unresolved required reconciliation', lambda d:d['initial_reconciliation'][0].update(disposition='unresolved'))
    reject('missing ninth obligation', overrides={record['applications'][0]['path']:json.dumps({'obligations':{}}).encode()})
    proof = next(p for p in record['files'] if p['path'].endswith('proofs/height-averaging.md'))
    reject('changed proof without fresh binding', overrides={proof['path']:read(proof['path'],{})+b'\nChanged proof.\n'})
    bindings = {p['path']:p['sha256'] for p in record['files']}
    bindings[str(RECORD.relative_to(ROOT))] = digest(RECORD.read_bytes())
    for name in ['check_records.py','CHECKER.md']:
        bindings[str((HERE/name).relative_to(ROOT))] = digest((HERE/name).read_bytes())
    fixture = {'reviewer':'negative-control-reviewer','role':'non-author internal model reviewer','decision':'accepted','scopes':record['required_review_scopes'],'bound_files':bindings}
    validate(record, reviews=[fixture])
    reject('self approval', reviews=[dict(fixture, reviewer=record['authors'][0])])
    # Even a coherently rewritten supply and all its declared consuming fields cannot reuse an earlier frozen decision.
    weakened = copy.deepcopy(record)
    supplier = weakened['suppliers'][0]
    supplier['output']['assertion'] = 'Only a proper subdomain or weaker estimate is supplied.'
    supplier['contract_sha256'] = digest(canonical(supplier['output']))
    for use in weakened['uses']:
        if use['supplier_id'] == supplier['id']:
            use['needed_assertion'] = supplier['output']['assertion']
            use['supplier_contract_sha256'] = supplier['contract_sha256']
            edge = next(e for e in weakened['connections'] if e['id'] == use['connection_id'])
            edge['needed_assertion'] = edge['available_assertion'] = supplier['output']['assertion']
            edge['derivation']['input_supplier_contract_sha256'] = supplier['contract_sha256']
            edge['derivation']['output']['assertion'] = supplier['output']['assertion']
            edge['derived_contract_sha256'] = digest(canonical(edge['derivation']))
            use['derived_contract_sha256'] = edge['derived_contract_sha256']
    validate(weakened, reviews=[])
    changed = json.dumps(weakened,indent=2,ensure_ascii=False).encode()+b'\n'
    reject('coherently weakened supplier with stale review', edit=lambda d:(d.clear(),d.update(weakened)), reviews=[fixture], overrides={str(RECORD.relative_to(ROOT)):changed})
    # A changed proof cannot reuse the existing source/reviewer binding.
    new_proof = read(proof['path'],{})+b'\nChanged proof.\n'
    reject('old review on changed proof', reviews=[fixture], overrides={proof['path']:new_proof})
    reject('deleted connecting premise', lambda d: next(e for e in d['connections'] if e['use_id']=='finite-H4')['derivation']['additional_premises'].pop())
    reject('deleted connecting derivation', lambda d: next(e for e in d['connections'] if e['use_id']=='reflected-height').pop('derivation'))
    return count

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test',action='store_true')
    parser.add_argument('--require-scoped-review',action='store_true',help='also require actual bound decisions for all four declared public scopes; never attests controller eligibility')
    args = parser.parse_args()
    try:
        record = json.loads(RECORD.read_text())
        result = validate(record)
        if args.self_test:
            result['negative_controls_rejected'] = self_test(record)
        if args.require_scoped_review:
            require(not result['pending_scopes'], 'required public mathematical review scopes remain pending: '+', '.join(result['pending_scopes']))
        print(json.dumps(result,sort_keys=True))
        return 0
    except (Invalid,KeyError,ValueError,OSError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        return 1

if __name__ == '__main__':
    sys.exit(main())
