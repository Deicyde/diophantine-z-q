"""Check archive navigation and alias witnesses using immutable Git objects."""
import argparse
import copy
import functools
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
from urllib.parse import unquote

ARCHIVE = '005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f'
URL = re.compile(r'https://github\.com/elliotglazer/diophantine-z-q/(blob|tree)/'
                 + ARCHIVE + r'/([^\s)]+)')
ROW = re.compile(r'- Archived target: `([^`]+)`\. SHA256: `([0-9a-f]{64})`\.'
                 r' Recorded workspace aliases: (.+)\.')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_path(path):
    require(isinstance(path, str) and path and '\\' not in path and '\0' not in path and ':' not in path,
            'Invalid repository path')
    parts = PurePosixPath(path)
    require(not parts.is_absolute() and '..' not in parts.parts and str(parts) == path,
            'Noncanonical repository path: ' + path)
    return path


def git(repository, *args):
    return subprocess.check_output(['git', '-C', str(repository), *args])


@functools.lru_cache(maxsize=None)
def archive_object(repository, path):
    safe_path(path)
    oid = git(repository, 'rev-parse', '--verify', ARCHIVE + ':' + path).decode().strip()
    kind = git(repository, 'cat-file', '-t', oid).decode().strip()
    require(kind in {'blob', 'tree'}, 'Unexpected archive object type')
    raw = git(repository, 'cat-file', 'blob', oid) if kind == 'blob' else None
    return oid, kind, raw


def witness_object(raw, pointer):
    value = json.loads(raw)
    require(isinstance(pointer, str) and (pointer == '' or pointer.startswith('/')),
            'Invalid witness JSON pointer')
    for token in pointer.split('/')[1:] if pointer else []:
        token = token.replace('~1', '/').replace('~0', '~')
        try:
            value = value[int(token)] if isinstance(value, list) else value[token]
        except (KeyError, IndexError, TypeError, ValueError) as error:
            raise ValueError('Missing witness pointer: ' + pointer) from error
    require(isinstance(value, dict), 'Witness must identify a JSON object')
    return value


def verify(repository, documents, manifest):
    require(manifest['schema'] == 'archive-bindings/v1', 'Wrong manifest schema')
    require(manifest['archive_commit'] == ARCHIVE, 'Wrong archive commit')
    require(git(repository, 'rev-parse', '--verify', ARCHIVE + '^{commit}').decode().strip()
            == ARCHIVE, 'Archive commit unavailable')
    found, document_hashes = [], {}
    require(len(set(manifest['documents'])) == len(manifest['documents']), 'Repeated document')
    for document in manifest['documents']:
        document_bytes = (documents / safe_path(document)).read_bytes()
        document_hashes[document] = hashlib.sha256(document_bytes).hexdigest()
        text = document_bytes.decode('utf-8')
        for match in URL.finditer(text):
            kind, encoded = match.groups()
            target = safe_path(unquote(encoded.split('#', 1)[0]).rstrip('/'))
            found.append((document, kind, target))
    declared = [(row['document'], row['kind'], row['target']) for row in manifest['links']]
    require(sorted(found) == sorted(declared), 'Navigation links do not match manifest')
    checked_links = []
    for row in manifest['links']:
        oid, kind, raw = archive_object(repository, row['target'])
        require((oid, kind) == (row['git_oid'], row['kind']), 'Wrong linked object: ' + row['target'])
        if kind == 'blob':
            require(hashlib.sha256(raw).hexdigest() == row['sha256'], 'Wrong linked bytes: ' + row['target'])
        checked_links.append(row)
    guide_bytes = (documents / safe_path(manifest['guide'])).read_bytes()
    document_hashes[manifest['guide']] = hashlib.sha256(guide_bytes).hexdigest()
    guide = guide_bytes.decode('utf-8')
    guide_aliases = []
    for line in guide.splitlines():
        if not line.startswith('- Archived target: '):
            continue
        match = ROW.fullmatch(line)
        require(match is not None, 'Unrecognized guide alias row')
        target, digest, text = match.groups()
        aliases = re.findall(r'`([^`]+)`', text)
        require(bool(aliases), 'Guide row has no aliases')
        guide_aliases.extend((target, digest, alias) for alias in aliases)
    declared_aliases = [(row['target'], row['sha256'], row['alias']) for row in manifest['aliases']]
    require(sorted(guide_aliases) == sorted(declared_aliases), 'Guide aliases do not match manifest')
    checked_aliases = []
    for row in manifest['aliases']:
        _, kind, target = archive_object(repository, row['target'])
        require(kind == 'blob' and hashlib.sha256(target).hexdigest() == row['sha256'],
                'Wrong alias target bytes: ' + row['target'])
        witness = row['witness']
        _, kind, raw = archive_object(repository, witness['path'])
        require(kind == 'blob' and hashlib.sha256(raw).hexdigest() == witness['sha256'],
                'Wrong witness bytes: ' + witness['path'])
        obj = witness_object(raw, witness['pointer'])
        require(obj.get(witness['alias_key']) == row['alias'], 'Wrong recorded alias')
        digest = obj.get(witness['sha256_key'])
        require(isinstance(digest, str) and digest.lower() == row['sha256'], 'Wrong recorded digest')
        checked_aliases.append(row)
    return {'archive_commit': ARCHIVE, 'document_sha256': document_hashes,
            'verified_links': checked_links,
            'verified_aliases': checked_aliases,
            'scope': 'Exact committed object bytes and direct alias/digest witnesses only. '
                     'No mathematical acceptance or availability of external work directories is asserted.'}


def rejection_tests(repository, documents, manifest):
    probes = []
    bad = copy.deepcopy(manifest)
    next(row for row in bad['links'] if row['kind'] == 'blob')['sha256'] = '0' * 64
    probes.append(('altered linked digest', bad))
    bad = copy.deepcopy(manifest)
    bad['links'].pop()
    probes.append(('omitted navigation link', bad))
    bad = copy.deepcopy(manifest)
    bad['aliases'][0]['witness']['pointer'] += '/__absent_archive_probe__'
    probes.append(('missing source witness', bad))
    bad = copy.deepcopy(manifest)
    bad['aliases'][0]['witness']['sha256_key'] = '__absent_digest_probe__'
    probes.append(('absent associated source digest', bad))
    for name, bad in probes:
        try:
            verify(repository, documents, bad)
        except ValueError:
            continue
        raise ValueError('Failed to reject ' + name)
    return [name for name, _ in probes]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    root = Path(__file__).resolve().parents[1]
    parser.add_argument('--repository', type=Path, default=root)
    parser.add_argument('--documents', type=Path, default=root)
    parser.add_argument('--manifest', type=Path, default=root / 'docs/research-review/archive-bindings.json')
    parser.add_argument('--output', type=Path, default=root / 'build/archive-bindings.json')
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    manifest_bytes = args.manifest.read_bytes()
    manifest = json.loads(manifest_bytes)
    report = verify(args.repository.resolve(), args.documents.resolve(), manifest)
    report['manifest_sha256'] = hashlib.sha256(manifest_bytes).hexdigest()
    if args.self_test:
        report['rejection_tests'] = rejection_tests(args.repository.resolve(), args.documents.resolve(), manifest)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({'archive_commit': ARCHIVE, 'verified_links': len(report['verified_links']),
                      'verified_aliases': len(report['verified_aliases']),
                      'distinct_targets': len({row['target'] for row in report['verified_aliases']}),
                      'rejection_tests': report.get('rejection_tests', [])}))


if __name__ == '__main__':
    main()
