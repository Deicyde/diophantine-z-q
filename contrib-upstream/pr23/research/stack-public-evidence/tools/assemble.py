"""Assemble the stack-public-evidence packet from read-only build directories.

Provenance tool, kept for transparency; reviewers do not need to run it.
It reads build outputs, checks every candidate file against the hashes published
in the frozen #20 tree (75e76303) and the public review archive (452c8620),
refuses files whose path-level published hash differs, compresses large files
deterministically (gzip level 9, mtime 0, no file name) and writes INDEX.json.
It imports nothing from the stack.  Usage:

    python3 -B tools/assemble.py BUILD_ROOT REPO PACKET_DIR
"""
import gzip, hashlib, json, re, subprocess, sys
from pathlib import Path

FROZEN = '75e7630341e0722aca7bca414e10b6ff003ba498'
ARCHIVE = '452c8620a47752d58b42ca44d8432a907f89fae5'
PACKETS = ['conditional-quartic-reduction', 'factored-pole-reduction', 'scalar-chain-reduction',
           'scalar-preparation-zero', 'detector-cube-reuse', 'height-consumer-refinement',
           'mixed-detector-normalization', 'scalar-row-reduction', 'odd-power-detectors',
           'higher-order-variant']
ARCHIVE_DIR = 'research/independent-local-reviews/2026-11-09'
GZIP_THRESHOLD = 16384

# (label, PR, head, packet, expected key, build dir relative to BUILD_ROOT, {role: relpath})
COMMON = {
    'table': None, 'rowsIr': 'balanced/integer-ir.json',
    'diagonalCertificate': 'balanced/diagonal-certificate.json',
    'balancedSummary': 'balanced/summary.json',
    'preDiagonalIr': 'final/integer-candidate-ir.json',
    'transportCertificate': 'transport-certificate.json', 'transportCheck': 'transport-check.json',
    'preTransportIr': 'before-factor/integer-candidate-ir.json',
    'compiledIr': 'compiled/compiled-ir.json', 'coordinateMap': 'compiled/coordinate-map.json',
    'reductionCertificate': 'compiled/reduction-certificate.json',
    'compilerReport': 'compiled/compiler-report.json',
    'specializationCertificate': 'compiled/specialization-certificate.json',
    'preTransportVerification': 'before-factor/verification.json',
    'moduloCertificate': 'before-factor/modulo-certificate.json',
    'rawIr': 'raw-translated-ir.json', 'gateCheck': 'gate-check.json',
    'diagonalCheck': 'diagonal-check.json', 'measured': 'MEASURED.json',
}


def spec(label, pr, head, packet, key, build, n, layer_check=None, prefix='', drop=(), extra=None):
    roles = dict(COMMON)
    roles['table'] = f'quartic-{n}-balanced-decimal.txt'
    if layer_check:
        roles['layerCheck'] = layer_check
    for r in drop:
        roles.pop(r)
    if prefix:
        for r in ['table', 'rowsIr', 'diagonalCertificate', 'balancedSummary', 'preDiagonalIr',
                  'transportCertificate', 'transportCheck', 'diagonalCheck']:
            if r in roles:
                roles[r] = prefix + roles[r]
    roles.update(extra or {})
    return dict(label=label, pr=pr, head=head, packet=packet, key=key, build=build,
                variables=n, roles=roles)


TABLES = [
    spec('pr08-389', 8, 'ad7fc75610fb325313a1afd73b2bfbc4ba5a0d71', 'conditional-quartic-reduction', None,
         'pr389/build/conditional-quartic-n6gd42mq/construction', 389,
         drop=['transportCertificate', 'transportCheck', 'preTransportIr', 'preTransportVerification',
               'moduloCertificate', 'diagonalCheck', 'measured'],
         extra={'gateCheck': 'independent-gate-check.json', 'preDiagonalVerification': 'final/verification.json',
                'moduloCertificate': 'final/modulo-certificate.json'}),
    spec('pr09-385', 9, '51111cc97d0f42d50338ae378268700c457497f9', 'factored-pole-reduction', None,
         'pr385/build/quartic-385/candidate385', 385,
         drop=['compiledIr', 'coordinateMap', 'reductionCertificate', 'compilerReport',
               'specializationCertificate', 'preTransportVerification', 'moduloCertificate', 'rawIr',
               'gateCheck', 'measured'],
         extra={'preTransportIr': 'baseline389-ir.json'}),
    spec('pr11-385', 11, 'e8654b2ca24a424cead6b62f3f790136a170d953', 'scalar-chain-reduction', None,
         'prchain/build/scalar-chain-final', 385, prefix='factored/', drop=['measured'],
         extra={'preTransportIr': 'candidate/final/integer-candidate-ir.json',
                'compiledIr': 'candidate/compiled/compiled-ir.json',
                'coordinateMap': 'candidate/compiled/coordinate-map.json',
                'reductionCertificate': 'candidate/compiled/reduction-certificate.json',
                'compilerReport': 'candidate/compiled/compiler-report.json',
                'specializationCertificate': 'candidate/compiled/specialization-certificate.json',
                'preTransportVerification': 'candidate/final/verification.json',
                'moduloCertificate': 'candidate/final/modulo-certificate.json',
                'rawIr': 'candidate/raw-translated-ir.json', 'gateCheck': 'candidate/gate-check.json',
                'layerCheck': 'candidate/source-check.json'}),
    spec('pr12-383', 12, '772fe96a0e65bee76db500d8ef3a7a6b5e884d1f', 'scalar-preparation-zero', None,
         'pr383/build/preparation-zero', 383, prefix='factored/', drop=['measured'],
         extra={'preTransportIr': 'candidate/final/integer-candidate-ir.json',
                'compiledIr': 'candidate/compiled/compiled-ir.json',
                'coordinateMap': 'candidate/compiled/coordinate-map.json',
                'reductionCertificate': 'candidate/compiled/reduction-certificate.json',
                'compilerReport': 'candidate/compiled/compiler-report.json',
                'specializationCertificate': 'candidate/compiled/specialization-certificate.json',
                'preTransportVerification': 'candidate/final/verification.json',
                'moduloCertificate': 'candidate/final/modulo-certificate.json',
                'rawIr': 'candidate/raw-translated-ir.json', 'gateCheck': 'candidate/gate-check.json',
                'layerCheck': 'candidate/source-check.json',
                'freeOmission': 'candidate/free-omission.json'}),
    spec('pr13-380', 13, '31563264ba3dfbc3f00b4b08c099e9380caacd42', 'detector-cube-reuse', '45',
         'cube/build/final380', 380, layer_check='cube-check.json'),
    spec('pr13-383-order47', 13, '31563264ba3dfbc3f00b4b08c099e9380caacd42', 'detector-cube-reuse', '47',
         'cube/build/final383-small', 383, layer_check='cube-check.json',
         extra={'baselineRawIr': 'baseline/raw-translated-ir.json'}),
    spec('pr16-380', 16, '59c59e5589d86036ee41994c82a2b900fce85c2d', 'height-consumer-refinement', '45',
         'height/build/height380', 380, layer_check='height-check.json'),
    spec('pr16-383-order47', 16, '59c59e5589d86036ee41994c82a2b900fce85c2d', 'height-consumer-refinement', '47',
         'height/build/height383', 383, layer_check='height-check.json'),
    spec('pr17-380', 17, 'eb00b7c9c5be2e8666c0403c750c6c780cf78563', 'mixed-detector-normalization', '46',
         'mixed/build/mixed380', 380, layer_check='mixed-check.json'),
    spec('pr18-379', 18, 'ce15e8ece219a2bb000075a5a79f6ffd9bea6dfd', 'scalar-row-reduction', None,
         'row379/build/row379', 379, layer_check='row-check.json'),
    spec('pr19-376', 19, '32abb654ec295e28b51f92a51d7f12d4c5a626ec', 'odd-power-detectors', None,
         'power376/build/power376', 376, layer_check='power-check.json'),
    spec('pr20-377', 20, '75e7630341e0722aca7bca414e10b6ff003ba498', 'higher-order-variant', None,
         'higher377/build/higher377-full', 377, layer_check='higher-check.json'),
]

OMITTED = {
    'balanced/polynomial.json': 'Same quartic as the decimal table plus the compaction list (IR id -> x index in increasing id order); assemble.py checked both equal before omitting it. Its hash is published and is stated in diagonal-certificate.json (polynomialSha256).',
    'compiled/polynomial.json': 'Sum of squares of compiled-ir.json rows over Z[S] before the fixed-S specialization, transport and diagonal map; derivable and about 4.3 MB per table. Not reproduced or checked here.',
    'raw-ir.json': 'Raw source before the affine anchor translation; raw-translated-ir.json (the compiler input, hash-bound in EXPECTED.json) is included instead.',
    'active-ir.json / before-factor/source-ir.json': 'compiled-ir.json with the two certified-unused preparation coordinates dropped (see coordinate-map.json omittedFreeCoordinates); derivable.',
    'before-factor/candidate-ir.json, final/candidate-ir.json': 'Rational-normalized twin of integer-candidate-ir.json (same rows up to row scaling); the integer version is the one consumed downstream.',
    'builder.cjs, baseline/builder.cjs': 'Generator code, not data. Reproduction uses the committed packet patches. Note: the mixed380 build builder.cjs (cd0aae54...) differs from the hash a2ce8241... in mixed-detector-normalization/EXPECTED.json; its raw-translated-ir.json matches EXPECTED. Not included.',
    'baseline/*': 'Parent layer raw IR; identical to the parent table\'s included raw-translated-ir.json, except the order-47 baseline of #13, which is included.',
    'census.json, replay.log, reproduction.log, reproduction-receipt.json': 'Diagnostics with timing or local paths.',
    '#8 ordinary391/392/393, quartic-389-decimal.txt, quartic-389-symbolic.txt, quartic-39x-decimal.txt, reference_round7/*': 'Not one of the 12 selected tables (Carlos did not review the 391/392/393 variants).',
}


def sha(b):
    return hashlib.sha256(b).hexdigest()


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], capture_output=True, check=True).stdout


def published_index(repo):
    out = {}
    H = re.compile(rb'[0-9a-f]{64}')
    specs = [(FROZEN, 'research/' + p) for p in PACKETS] + [(ARCHIVE, ARCHIVE_DIR)]
    for rev, path in specs:
        for name in git(repo, 'ls-tree', '-r', '--name-only', rev, path).decode().split('\n'):
            if not name or name.endswith('.pdf'):
                continue
            data = git(repo, 'show', f'{rev}:{name}')
            for m in H.finditer(data):
                out.setdefault(m.group().decode(), set()).add((rev, name))
    return out


def path_expectations(repo, t):
    """Path-level published hashes (and bytes) for this table's build files."""
    rel = lambda p: p
    exp = {}
    def load(p):
        return json.loads(git(repo, 'show', f'{FROZEN}:research/{t["packet"]}/{p}'))
    src = lambda p: f'{FROZEN[:8]}:research/{t["packet"]}/{p}'
    if t['pr'] == 8:
        d = load('EXPECTED_OUTPUTS.json')
        for f in d['files']:
            exp[f['path'].removeprefix('construction/')] = (f['sha256'], f['bytes'], src('EXPECTED_OUTPUTS.json'))
        return exp
    if t['pr'] == 9:
        d = load('EXPECTED.json')
        for a in d['artifacts']:
            exp[a['path']] = (a['sha256'], d['summary']['tableBytes'] if a['path'].endswith('.txt') else None,
                              src('EXPECTED.json'))
        exp['baseline389-ir.json'] = (d['sourceIrSha256'], None, src('EXPECTED.json') + ' sourceIrSha256')
        return exp
    if t['pr'] in (11, 12):
        d = load('EXPECTED.json'); r = load('REPRODUCTION.json'); lc = load('LOCAL_CHECKS.json')
        s = d['summary']; n = t['variables']
        exp[f'factored/quartic-{n}-balanced-decimal.txt'] = (s['tableSha256'], s['tableBytes'], src('EXPECTED.json'))
        exp['factored/balanced/diagonal-certificate.json'] = (s['certificateSha256'], None, src('EXPECTED.json') + ' certificateSha256')
        exp['candidate/final/integer-candidate-ir.json'] = (d['compiledIrSha256'], None, src('EXPECTED.json') + ' compiledIrSha256')
        for rep in r['reports']:
            exp[rep['path']] = (rep['sha256'], None, src('REPRODUCTION.json') + ' reports')
        if t['pr'] == 11:
            exp['candidate/raw-translated-ir.json'] = (lc['rawIrSha256'], None, src('LOCAL_CHECKS.json') + ' rawIrSha256')
        else:
            exp['candidate/raw-translated-ir.json'] = (lc['afterSha256'], None, src('LOCAL_CHECKS.json') + ' afterSha256')
            fo = r['freeOmission']
            exp['candidate/compiled/compiled-ir.json'] = (fo['sourceSha256'], None, src('REPRODUCTION.json') + ' freeOmission.sourceSha256')
            exp['candidate/compiled/coordinate-map.json'] = (fo['coordinateMapSha256'], None, src('REPRODUCTION.json') + ' freeOmission.coordinateMapSha256')
        return exp
    d = load('EXPECTED.json')
    if t['key']:
        d = d[t['key']]
    s = d['summary']; n = t['variables']
    exp[f'quartic-{n}-balanced-decimal.txt'] = (s['tableSha256'], s['tableBytes'], src('EXPECTED.json'))
    exp['balanced/diagonal-certificate.json'] = (s['certificateSha256'], None, src('EXPECTED.json') + ' certificateSha256')
    for p, h in d['files'].items():
        exp[p] = (h, None, src('EXPECTED.json') + ' files')
    return exp


def summary_expectation(repo, t):
    def load(p):
        return json.loads(git(repo, 'show', f'{FROZEN}:research/{t["packet"]}/{p}'))
    if t['pr'] == 8:
        return load('EXPECTED_OUTPUTS.json')['selected']
    d = load('EXPECTED.json')
    if t['key']:
        d = d[t['key']]
    return d['summary']


def main():
    build_root, repo, packet = map(Path, sys.argv[1:4])
    pub = published_index(repo)
    index = {'format': 'stack-public-evidence-index-v1', 'frozenCommit': FROZEN, 'archiveCommit': ARCHIVE,
             'gzip': 'Python gzip.compress(data, compresslevel=9, mtime=0); no file name stored',
             'tables': [], 'files': {}, 'omittedFromEveryTable': OMITTED, 'excluded': []}
    by_sha = {}
    pending = []  # (label, role, rel, data)
    for t in TABLES:
        base = build_root / t['build']
        pexp = path_expectations(repo, t)
        entry = {k: t[k] for k in ['label', 'pr', 'head', 'packet', 'variables']}
        entry['expectedKey'] = t['key']
        entry['buildDirectory'] = t['build']
        entry['publishedSummary'] = summary_expectation(repo, t)
        entry['roles'] = {}
        for role, rel in t['roles'].items():
            p = base / rel
            data = p.read_bytes()
            h = sha(data)
            e = pexp.get(rel)
            if e is not None and (e[0] != h or (e[1] is not None and e[1] != len(data))):
                index['excluded'].append({'table': t['label'], 'path': rel, 'sha256': h, 'bytes': len(data),
                                          'published': e[0], 'publishedBytes': e[1], 'source': e[2]})
                print('MISMATCH, excluded:', t['label'], rel, file=sys.stderr)
                continue
            rec = by_sha.get(h)
            if rec is None:
                suffix = '.gz' if len(data) >= GZIP_THRESHOLD else ''
                ppath = f'tables/{t["label"]}/{rel}{suffix}'
                stored = gzip.compress(data, compresslevel=9, mtime=0) if suffix else data
                assert gzip.decompress(stored) == data if suffix else True
                rec = {'packetPath': ppath, 'sha256': h, 'bytes': len(data),
                       'storedSha256': sha(stored), 'storedBytes': len(stored),
                       'compressed': bool(suffix), 'origins': [], 'pathBinding': [], 'publishedIn': [],
                       'statedIn': []}
                by_sha[h] = rec
                index['files'][ppath] = rec
                out = packet / ppath
                out.parent.mkdir(parents=True, exist_ok=True)
                out.write_bytes(stored)
                pending.append((h, data))
            rec['origins'].append(f'{t["build"]}/{rel}')
            if e is not None:
                rec['pathBinding'].append({'source': e[2], 'sha256': e[0], 'bytes': e[1]})
            entry['roles'][role] = rec['packetPath']
        # Redundancy check before omitting balanced/polynomial.json.
        prefix = 'factored/' if t['pr'] in (11, 12) else ''
        poly = json.loads((base / (prefix + 'balanced/polynomial.json')).read_bytes())
        ir = json.loads((base / t['roles']['rowsIr']).read_bytes())
        ids = sorted(c['id'] for c in ir['coordinates'])
        assert [c['sourceId'] for c in poly['coordinates']] == ids
        assert [c['id'] for c in poly['coordinates']] == list(range(len(ids)))
        table = {}
        for line in (base / t['roles']['table']).read_text().splitlines():
            if line.startswith('#'):
                continue
            c, m = line.split('\t')
            mono = [] if m == '1' else sum(([int(f.split('^')[0][1:])] * int(f.split('^')[1] if '^' in f else 1)
                                            for f in m.split('*')), [])
            table[tuple(mono)] = int(c)
        polyterms = {tuple(x['monomial']): int(x['coefficient']) for x in poly['terms']}
        assert polyterms == table, t['label']
        polysha = sha((base / (prefix + 'balanced/polynomial.json')).read_bytes())
        entry['omittedPolynomialJson'] = {'sha256': polysha, 'checkedEqualToTable': True,
                                          'compactionIsIncreasingIrId': True}
        index['tables'].append(entry)
    # Bindings: direct publication, and statement inside another bound packet file (fixed point).
    for h, rec in by_sha.items():
        rec['publishedIn'] = sorted(f'{rev[:8]}:{name}' for rev, name in pub.get(h, ()))
    texts = {h: d.decode('utf8', 'replace') for h, d in pending}
    bound = {h for h, r in by_sha.items() if r['publishedIn'] or r['pathBinding']}
    changed = True
    while changed:
        changed = False
        for h, rec in by_sha.items():
            for g in list(bound):
                if g != h and h in texts[g]:
                    carrier = by_sha[g]['packetPath']
                    if carrier not in rec['statedIn']:
                        rec['statedIn'].append(carrier)
                        changed = True
                    if h not in bound:
                        bound.add(h)
                        changed = True
    for h, rec in by_sha.items():
        rec['statedIn'].sort()
        rec['bound'] = h in bound
    (packet / 'INDEX.json').write_text(json.dumps(index, indent=1, sort_keys=False) + '\n')
    print('files', len(by_sha), 'unbound', sum(not r['bound'] for r in by_sha.values()),
          'excluded', len(index['excluded']))


if __name__ == '__main__':
    main()
