#!/usr/bin/env python3
"""Check editorial source/TeX/PDF bindings; never certify mathematics."""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from pathlib import Path

CORRECTION_IDS = {'F1', 'F2'} | {'F3-'+str(i) for i in range(1,9)} | {'F4-'+str(i) for i in range(1,10)}
REVIEW_SCOPES = {'formula-incorporation', 'related-use-coverage', 'source-inclusion-and-changed-joins', 'research-artifact-packaging'}
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OBLIGATIONS = {
    'source_hypotheses', 'constructed_objects', 'domain_index_coverage',
    'transition_comparison_maps', 'identity_consumed_object',
    'coefficient_normalization', 'local_conditions', 'exceptional_cases',
    'downstream_consumption',
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe(path):
    p = Path(path)
    if p.is_absolute() or '..' in p.parts:
        raise ValueError('unsafe repository path: ' + str(path))
    return ROOT / p


def read(path, overrides):
    return overrides[path] if path in overrides else safe(path).read_bytes()


def binding(record, overrides):
    data = read(record['path'], overrides)
    if digest(data) != record['sha256']:
        raise ValueError('stale file binding: ' + record['path'])
    if 'bytes' in record and len(data) != record['bytes']:
        raise ValueError('wrong file length: ' + record['path'])
    if 'lines' in record:
        first, last = record['lines']
        lines = data.splitlines(keepends=True)
        if not 1 <= first <= last <= len(lines):
            raise ValueError('invalid passage: ' + record['path'])
        excerpt = b''.join(lines[first-1:last])
        if digest(excerpt) != record['passage_sha256']:
            raise ValueError('stale passage: ' + record['path'])
    return data


def key(p):
    return (p['path'], tuple(p['lines']), p['passage_sha256'])


def manifest_binding(path, overrides, required):
    manifest = json.loads(read(path, overrides))
    entries = manifest['files']
    if isinstance(entries, dict):
        entries = [{'path':p, **entry} for p,entry in entries.items()]
    pins = {}
    for entry in entries:
        if entry['path'] == path:
            raise ValueError('release manifest cannot bind itself')
        if 'bytes' not in entry:
            raise ValueError('release manifest requires byte lengths')
        binding(entry, overrides)
        if entry['path'] in pins:
            raise ValueError('duplicate release manifest input')
        pins[entry['path']] = entry['sha256']
    if not set(required) <= set(pins):
        raise ValueError('release manifest omits required artifact')
    return digest(read(path, overrides))


def validate(record, overrides=None, release=False, decision_path=None, manifest_path=None):
    overrides = overrides or {}
    if record['role'] != 'author_editorial_application_no_independent_acceptance':
        raise ValueError('author role must remain explicit')
    for field in ['manuscript', 'source_map', 'assembler', 'initial_source_uses', 'findings']:
        binding(record[field], overrides)
    if set(record['obligations']) != OBLIGATIONS:
        raise ValueError('missing nine-obligation argument')
    for name, obligation in record['obligations'].items():
        for field in ['required_input', 'constructed_input', 'justification', 'source_references', 'evidence']:
            if not obligation.get(field):
                raise ValueError('missing obligation argument: ' + name + ':' + field)
    initial = json.loads(binding(record['initial_source_uses'], overrides))
    needed = {p['path'] for p in initial['required_source_blocks']}
    foundation = initial['retained_v15']['path']
    if record.get('foundation_transition'):
        transition = record['foundation_transition']
        binding(transition['historical_source'], overrides)
        if transition['historical_source']['sha256'] != initial['retained_v15']['sha256']:
            raise ValueError('historical foundation was rewritten')
        binding(transition['current_source'], overrides)
        binding(transition['bridge'], overrides)
        application = json.loads(binding(transition['contract'], overrides))
        if (application['manuscript'] != record['manuscript']
                or application['source_map'] != record['source_map']
                or application['bridge'] != transition['bridge']
                or set(application['obligations']) != OBLIGATIONS):
            raise ValueError('stale or incomplete foundation application')
        for obligation in application['obligations'].values():
            for field in ['required_input', 'constructed_input', 'justification', 'source_references', 'evidence']:
                if not obligation.get(field):
                    raise ValueError('missing foundation obligation argument')
        for source in application['required_sources']:
            binding(source, overrides)
        if set(application['transitions']) != {'GI-exact-lifts', 'TZ-fixed-extra-factor', 'CMH-product-height'}:
            raise ValueError('missing changed-foundation connection')
        for changed in application['transitions'].values():
            for field in ['source_passages', 'construction_passages', 'consumer_passages']:
                if not changed[field]:
                    raise ValueError('missing foundation source or consumer')
                for passage in changed[field]:
                    binding(passage['source'], overrides)
                    binding(passage['tex'], overrides)
        foundation = transition['current_source']['path']
    if not record.get('correction_application'):
        raise ValueError('missing current correction application')
    correction = json.loads(binding(record['correction_application'], overrides))
    if correction['manuscript'] != record['manuscript'] or correction['source_map'] != record['source_map']:
        raise ValueError('stale correction receiving binding')
    if set(correction['obligations']) != OBLIGATIONS:
        raise ValueError('missing correction nine-obligation argument')
    for obligation in correction['obligations'].values():
        for field in ['required_input','constructed_input','justification','source_references','evidence']:
            if not obligation.get(field):
                raise ValueError('missing correction obligation evidence')
    for field in ['sidecar','argument','adverse_review','adverse_findings','related_use_evidence']:
        binding(correction[field], overrides)
    if set(correction.get('related_use_scopes', {})) != {'F1','F2','F3','F4','F5'} or not all(correction['related_use_scopes'].values()):
        raise ValueError('missing correction related-use scope')
    for role in ['required_sources','construction_passages','application_passages','consumer_passages']:
        if not correction.get(role):
            raise ValueError('missing correction consumer or source evidence')
        for passage in correction[role]:
            binding(passage, overrides)
    sidecar = json.loads(binding(correction['sidecar'], overrides))
    if {c['id'] for c in sidecar['corrections']} != CORRECTION_IDS or len(sidecar['corrections']) != 19:
        raise ValueError('missing source correction')
    expected_lines = {'F1':'D(mu_sigma)^(-1/4)', 'F2':'`Σ_j e_j f_j=d`'}
    combined = next(c for c in sidecar['corrections'] if c['id'] == 'F3-2')
    if set(combined.get('finding_ids', [])) != {'F3','F5'} or '`[n]^{*}ω=nω`' not in combined['corrected_line'] or 'Ω_{[n]}' not in combined['corrected_line']:
        raise ValueError('missing F5 combined correction or derivative evidence')
    for c in sidecar['corrections']:
        if c['id'] in expected_lines and expected_lines[c['id']] not in c['corrected_line']:
            raise ValueError('altered correction mathematical replacement')
        original = read(c['source'], overrides)
        if digest(original) != c['source_sha256'] or original.decode().splitlines()[c['source_line']-1] != c['original_line']:
            raise ValueError('altered correction original evidence')
        if not c['corrected_line'] or c['corrected_line'] == c['original_line']:
            raise ValueError('altered correction replacement')
    needed.add(foundation)
    mapping = json.loads(binding(record['source_map'], overrides))
    selected = {c['id']:c for c in sidecar['corrections']}
    annotated = {}
    for span in mapping['spans']:
        for note in span.get('source_corrections', []):
            annotated[note['id']] = (span['source'], note)
    if set(annotated) != CORRECTION_IDS:
        raise ValueError('missing selected correction map evidence')
    for finding, c in selected.items():
        source, note = annotated[finding]
        if source != c['source'] or note['sidecar'] != correction['sidecar']['path'] or note['corrected_source_line'] != c['corrected_line']:
            raise ValueError('altered selected correction map evidence')
        if finding == 'F3-2' and set(note.get('finding_ids', [])) != {'F3','F5'}:
            raise ValueError('missing F5 map finding traceability')
    if mapping['output'] != record['manuscript']['path'] or mapping['output_sha256'] != record['manuscript']['sha256']:
        raise ValueError('map selects another TeX target')
    tex_lines = read(record['manuscript']['path'], overrides).decode().splitlines()
    line_coverage = {}
    for path, source in mapping['sources'].items():
        binding({'path':path, **source}, overrides)
    for span in mapping['spans']:
        path = span['source']
        first, last = span['tex_lines']
        if not 1 <= first <= last <= len(tex_lines):
            raise ValueError('invalid mapped TeX range')
        if 'source_lines' in span:
            a, b = span['source_lines']
            if not 1 <= a <= b <= mapping['sources'][path]['line_count']:
                raise ValueError('invalid mapped source range')
            line_coverage.setdefault(path, set()).update(range(a,b+1))
            if span['method'] == 'exact-retained-body-LF':
                source_lines = read(path, overrides).decode().splitlines()
                if source_lines[a-1:b] != tex_lines[first-1:last]:
                    raise ValueError('retained foundation mathematical body changed')
    for source in initial['required_source_blocks']:
        if line_coverage.get(source['path']) != set(range(1,source['line_count']+1)):
            raise ValueError('omitted source-map proof lines: ' + source['path'])
    if record.get('foundation_transition'):
        bridge = record['foundation_transition']['bridge']['path']
        required_bridge = set(range(1,len(read(bridge, overrides).splitlines())+1))
        if line_coverage.get(bridge) != required_bridge:
            raise ValueError('omitted current-foundation connecting argument')
    wrappers = {r'\begin{document}', r'\maketitle', r'\tableofcontents', r'\end{document}'}
    required_foundation = {n for n,line in enumerate(read(foundation, overrides).decode().splitlines(),1) if line not in wrappers}
    if not required_foundation <= line_coverage.get(foundation,set()):
        raise ValueError('omitted current foundation lines')
    covered = set()
    for entry in record['source_coverage']:
        binding(entry['source'], overrides)
        binding(entry['tex'], overrides)
        covered.add(entry['source']['path'])
    if not needed <= covered:
        raise ValueError('omitted required proof coverage: ' + ', '.join(sorted(needed-covered)))
    original_index = json.loads(binding(record['original_contract_index'], overrides))
    indexed = {p['application_id']: p for p in original_index['contracts']}
    if set(indexed) != {p['application_id'] for p in record['applications']}:
        raise ValueError('missing original application connection')
    for app in record['applications']:
        original = indexed[app['application_id']]
        if app['original_contract'] != original:
            raise ValueError('changed original contract link')
        contract = json.loads(binding(original, overrides))
        for source in contract['required_sources']:
            binding(source, overrides)
        for role in ['construction_passages', 'application_passages', 'consumer_passages']:
            expected = {key(p) for p in contract[role]}
            actual = {key(p['source']) for p in app[role]}
            if expected != actual:
                raise ValueError('missing original passage connection: ' + app['application_id'] + ':' + role)
            for passage in app[role]:
                binding(passage['source'], overrides)
                binding(passage['tex'], overrides)
    findings = json.loads(binding(record['findings'], overrides))
    if {f['id'] for f in findings['findings']} != set(record['finding_ids']):
        raise ValueError('omitted tracked finding')
    if release:
        if not record.get('pdf_binding'):
            raise ValueError('missing PDF/build binding')
        pdf = record['pdf_binding']
        binding(pdf['build'], overrides)
        binding(pdf['pdf'], overrides)
        build = json.loads(binding(pdf['build'], overrides))
        if build['pdf']['sha256'] != pdf['pdf']['sha256'] or build['pdf']['path'] != pdf['pdf']['path']:
            raise ValueError('PDF differs from build output')
        if build['source_files'].get(record['manuscript']['path']) != record['manuscript']['sha256']:
            raise ValueError('PDF built from another TeX target')
        manifest_required = [record[f]['path'] for f in ['manuscript','source_map','assembler','initial_source_uses','findings']]
        manifest_required += [pdf['build']['path'],pdf['pdf']['path'],
            'research/quartic214-manuscript-review/ADAPTATION.json',
            'research/quartic214-manuscript-review/check_records.py']
        if record.get('foundation_transition'):
            manifest_required += [record['foundation_transition'][f]['path'] for f in ['contract','bridge']]
        manifest_required += [record['correction_application']['path']] + [correction[f]['path'] for f in ['sidecar','argument','adverse_review','adverse_findings','related_use_evidence']]
        if not manifest_path:
            raise ValueError('missing release manifest')
        manifest_sha = manifest_binding(manifest_path, overrides, manifest_required)
        if not decision_path:
            raise ValueError('missing separately authored review decision')
        decision = json.loads(read(decision_path, overrides))
        if decision['reviewer'] in record['authors'] or decision['role'] != 'non-author internal model reviewer':
            raise ValueError('self-approval or incorrect reviewer role')
        if decision['decision'] not in ['accept', 'accepted', 'scoped-acceptance']:
            raise ValueError('review is not accepting')
        if decision.get('controller_eligibility') != 'notattested':
            raise ValueError('checker cannot attest controller eligibility')
        required = {record['manuscript']['path']:record['manuscript']['sha256'],
                    record['source_map']['path']:record['source_map']['sha256'],
                    pdf['build']['path']:pdf['build']['sha256'],pdf['pdf']['path']:pdf['pdf']['sha256']}
        contract_path = 'research/quartic214-manuscript-review/ADAPTATION.json'
        required[contract_path] = digest(read(contract_path, overrides))
        required[record['findings']['path']] = record['findings']['sha256']
        required[manifest_path] = manifest_sha
        if record.get('foundation_transition'):
            for field in ['contract', 'bridge', 'current_source']:
                source = record['foundation_transition'][field]
                required[source['path']] = source['sha256']
        if decision.get('full_closure') is not False or decision.get('whole_proof_status') != 'incomplete':
            raise ValueError('scoped receipt must preserve incomplete whole-proof status')
        if decision.get('complete_assembled_proof_status') != 'not-accepted' or decision.get('complete_inventory_status') != 'not-accepted':
            raise ValueError('narrow receipt must not accept complete proof or inventory')
        required[record['correction_application']['path']] = record['correction_application']['sha256']
        for field in ['sidecar','argument','adverse_review','adverse_findings','related_use_evidence']:
            required[correction[field]['path']] = correction[field]['sha256']
        if set(decision['scopes']) != REVIEW_SCOPES:
            raise ValueError('missing required review scope')
        for scope in REVIEW_SCOPES:
            if not decision.get('scope_details', {}).get(scope):
                raise ValueError('missing explicit review-scope limitation: ' + scope)
        dispositions = decision.get('finding_dispositions', {})
        if set(dispositions) != set(record['finding_ids']):
            raise ValueError('missing current finding disposition')
        for finding, disposition in dispositions.items():
            if disposition.get('decision') not in {'resolved', 'scope-explained'}:
                raise ValueError('unresolved release finding: ' + finding)
            evidence = disposition.get('evidence', '').split('#',1)[0]
            if not evidence or evidence not in decision['bound_files']:
                raise ValueError('unbound finding-disposition evidence: ' + finding)
        for path, sha in required.items():
            if decision['bound_files'].get(path) != sha:
                raise ValueError('stale review decision: ' + path)
        for path, sha in decision['bound_files'].items():
            if digest(read(path, overrides)) != sha:
                raise ValueError('stale review file: ' + path)
    return True


def self_test(record):
    tests = []
    def rejected(name, changed, overrides, expected, release=False):
        try:
            validate(changed, overrides, release)
        except (ValueError, KeyError) as exc:
            if expected not in str(exc):
                raise ValueError(name + ' failed for unintended reason: ' + str(exc))
            tests.append(name)
        else:
            raise ValueError(name + ' was not rejected')
    bad = copy.deepcopy(record)
    del bad['obligations']['domain_index_coverage']
    rejected('missing-domain-argument', bad, {}, 'missing nine-obligation')
    bad = copy.deepcopy(record)
    bad['obligations']['identity_consumed_object']['justification'] = ''
    rejected('missing-consumed-object-derivation', bad, {}, 'missing obligation')
    path = record['source_map']['path']
    rejected('stale-source-to-TeX-map', record, {path:read(path,{})+b'\n'}, 'stale file binding')
    bad = copy.deepcopy(record)
    mapping = json.loads(read(path, {}))
    corrected_paths = {span['source'] for span in mapping['spans'] if span.get('source_corrections')}
    target = next(entry['source']['path'] for entry in record['source_coverage'] if entry['source']['path'] not in corrected_paths)
    mapping['spans'] = [s for s in mapping['spans'] if s['source'] != target]
    changed_map = json.dumps(mapping).encode()
    bad['source_map']['sha256'] = digest(changed_map)
    bad['source_map']['bytes'] = len(changed_map)
    changed_files = {path:changed_map}
    if bad.get('foundation_transition'):
        app_path = bad['foundation_transition']['contract']['path']
        application = json.loads(read(app_path, {}))
        application['source_map'] = bad['source_map']
        data = json.dumps(application).encode()
        bad['foundation_transition']['contract'].update(sha256=digest(data), bytes=len(data))
        changed_files[app_path] = data
    correction_path = bad['correction_application']['path']
    correction = json.loads(read(correction_path, {}))
    correction['source_map'] = bad['source_map']
    data = json.dumps(correction).encode()
    bad['correction_application'].update(sha256=digest(data), bytes=len(data))
    changed_files[correction_path] = data
    rejected('omitted-map-proof-with-updated-author-hashes', bad, changed_files, 'omitted source-map proof lines')
    if record.get('foundation_transition'):
        bad = copy.deepcopy(record)
        app_path = bad['foundation_transition']['contract']['path']
        application = json.loads(read(app_path, {}))
        del application['transitions']['TZ-fixed-extra-factor']
        data = json.dumps(application).encode()
        bad['foundation_transition']['contract'].update(sha256=digest(data), bytes=len(data))
        rejected('missing-current-premise-transition', bad, {app_path:data}, 'missing changed-foundation connection')
        current_path = record['foundation_transition']['current_source']['path']
        rejected('changed-current-foundation-source', record, {current_path:read(current_path,{})+b'\n'}, 'stale file binding')
    bad = copy.deepcopy(record)
    target = record['source_coverage'][0]['source']['path']
    bad['source_coverage'] = [p for p in bad['source_coverage'] if p['source']['path'] != target]
    rejected('omitted-proof-block', bad, {}, 'omitted required proof coverage')
    bad = copy.deepcopy(record)
    bad['applications'][0]['consumer_passages'].pop()
    rejected('omitted-original-consumer', bad, {}, 'missing original passage connection')
    bad = copy.deepcopy(record)
    bad['finding_ids'].pop()
    rejected('omitted-finding', bad, {}, 'omitted tracked finding')
    # Synthetic build bindings exercise the actual PDF-target comparison without a build.
    bad = copy.deepcopy(record)
    fake_pdf = b'%PDF-1.4\nsynthetic negative-control fixture\n'
    fake_build = json.dumps({'pdf':{'path':'test.pdf','sha256':'0'*64},
        'source_files':{record['manuscript']['path']:record['manuscript']['sha256']}}).encode()
    bad['pdf_binding'] = {'pdf':{'path':'test.pdf','sha256':digest(fake_pdf)},
        'build':{'path':'test-build.json','sha256':digest(fake_build)}}
    rejected('PDF-build-mismatch', bad, {'test.pdf':fake_pdf,'test-build.json':fake_build},
        'PDF differs from build output', True)
    build = {'pdf':{'path':'test.pdf','sha256':digest(fake_pdf)},'source_files':{record['manuscript']['path']:'0'*64}}
    fake_build = json.dumps(build).encode()
    bad['pdf_binding']['build']['sha256'] = digest(fake_build)
    rejected('mismatched-PDF-build-target', bad, {'test.pdf':fake_pdf,'test-build.json':fake_build},
        'PDF built from another TeX target', True)
    fixture = b'synthetic manifest input'
    manifest = json.dumps({'files':[{'path':'test-input.tex','sha256':digest(fixture),'bytes':len(fixture)}]}).encode()
    try:
        manifest_binding('test-manifest.json', {'test-manifest.json':manifest,'test-input.tex':fixture+b' changed'}, ['test-input.tex'])
    except ValueError as exc:
        if 'stale file binding' not in str(exc):
            raise ValueError('manifest test failed for unintended reason')
        tests.append('stale-release-manifest-input')
    else:
        raise ValueError('stale release manifest input was not rejected')
    app_path = record['correction_application']['path']
    for name, mutate, expected in [
        ('missing-correction-obligation', lambda a: a['obligations'].pop('identity_consumed_object'), 'missing correction nine'),
        ('missing-correction-consumer', lambda a: a.update(consumer_passages=[]), 'missing correction consumer'),
        ('missing-correction-related-use', lambda a: a.update(related_use_scopes={}), 'missing correction related-use'),
    ]:
        bad = copy.deepcopy(record)
        application = json.loads(read(app_path, {}))
        mutate(application)
        data = json.dumps(application).encode()
        bad['correction_application'].update(sha256=digest(data), bytes=len(data))
        rejected(name, bad, {app_path:data}, expected)
    application = json.loads(read(app_path, {}))
    sidecar_path = application['sidecar']['path']
    rejected('altered-source-correction', record, {sidecar_path:read(sidecar_path,{})+b'\n'}, 'stale file binding')
    for name, mutate, expected in [
        ('missing-source-correction', lambda d: d['corrections'].pop(), 'missing source correction'),
        ('altered-correction-formula', lambda d: d['corrections'][0].update(corrected_line='wrong formula'), 'altered correction mathematical replacement'),
    ]:
        bad = copy.deepcopy(record)
        application = json.loads(read(app_path, {}))
        sidecar = json.loads(read(sidecar_path, {}))
        mutate(sidecar)
        data = json.dumps(sidecar).encode()
        application['sidecar'].update(sha256=digest(data), bytes=len(data))
        app_data = json.dumps(application).encode()
        bad['correction_application'].update(sha256=digest(app_data), bytes=len(app_data))
        rejected(name, bad, {app_path:app_data, sidecar_path:data}, expected)
    related = application['related_use_evidence']['path']
    rejected('altered-correction-related-use-evidence', record, {related:read(related,{})+b'\n'}, 'stale file binding')
    for family, missing in [('F3','F3-6'),('F4','F4-3')]:
        bad = copy.deepcopy(record)
        application = json.loads(read(app_path, {}))
        sidecar = json.loads(read(sidecar_path, {}))
        sidecar['corrections'] = [c for c in sidecar['corrections'] if c['id'] != missing]
        data = json.dumps(sidecar).encode()
        application['sidecar'].update(sha256=digest(data), bytes=len(data))
        app_data = json.dumps(application).encode()
        bad['correction_application'].update(sha256=digest(app_data), bytes=len(app_data))
        rejected('missing-'+family+'-correction', bad, {app_path:app_data,sidecar_path:data}, 'missing source correction')
    bad = copy.deepcopy(record)
    application = json.loads(read(app_path, {}))
    sidecar = json.loads(read(sidecar_path, {}))
    next(c for c in sidecar['corrections'] if c['id'] == 'F3-2')['finding_ids'] = ['F3']
    data = json.dumps(sidecar).encode()
    application['sidecar'].update(sha256=digest(data),bytes=len(data))
    app_data = json.dumps(application).encode()
    bad['correction_application'].update(sha256=digest(app_data),bytes=len(app_data))
    rejected('missing-F5-combined-finding',bad,{app_path:app_data,sidecar_path:data},'missing F5 combined')
    return tests


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--reviewed-artifacts', action='store_true', help='check scoped research artifacts and receipt; not official full release acceptance')
    parser.add_argument('--decision', default='research/quartic214-manuscript-review/REVIEW_DECISION.json')
    parser.add_argument('--manifest', default='research/quartic214-manuscript/RELEASE_MANIFEST.json')
    args = parser.parse_args()
    record = json.loads((HERE/'ADAPTATION.json').read_text())
    validate(record, release=args.reviewed_artifacts, decision_path=args.decision, manifest_path=args.manifest)
    tests = self_test(record) if args.self_test else []
    print(json.dumps({'status':'PASS','scope':'editorial byte bindings, recorded coverage links and declared decisions only',
        'reviewed_artifacts_mode':args.reviewed_artifacts,'negative_controls':tests,
        'mathematical_acceptance':'not established by this checker','controller_eligibility':'notattested'}))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError) as exc:
        raise SystemExit('FAIL: ' + str(exc))
