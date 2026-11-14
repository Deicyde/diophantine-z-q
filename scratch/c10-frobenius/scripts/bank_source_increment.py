#!/usr/bin/env python3
"""Bank a source increment without changing its verified base archive."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import zipfile


def safe_name(name):
    path = PurePosixPath(name)
    if not name or path.is_absolute() or '..' in path.parts or path.as_posix() != name:
        raise ValueError(f'Unsafe archive path: {name}')
    return name


def bank(base, output, additions, metadata, expected_base_sha256):
    if base.resolve() == output.resolve():
        raise ValueError('The base archive must not be overwritten')
    if hashlib.sha256(base.read_bytes()).hexdigest() != expected_base_sha256:
        raise ValueError('Base archive checksum differs')
    with zipfile.ZipFile(base) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError('Duplicate archive entries')
        payloads = {safe_name(name): archive.read(name) for name in names}
    manifest = json.loads(payloads['MANIFEST.json'])
    recorded = manifest['files']
    if set(recorded) != set(payloads) - {'MANIFEST.json'}:
        raise ValueError('Base manifest does not cover the exact file set')
    for name, entry in recorded.items():
        data = payloads[name]
        if len(data) != entry['bytes'] or hashlib.sha256(data).hexdigest() != entry['sha256']:
            raise ValueError(f'Base file checksum differs: {name}')
    for name, data in additions.items():
        if name == 'MANIFEST.json':
            raise ValueError('Manifest is generated, not supplied')
        payloads[safe_name(name)] = data
    if 'files' in metadata:
        raise ValueError('The file manifest must not be overridden by metadata')
    manifest.update(metadata)
    manifest['files'] = {
        name: {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
        for name, data in payloads.items() if name != 'MANIFEST.json'
    }
    payloads['MANIFEST.json'] = (json.dumps(manifest, indent=2) + '\n').encode()
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for name, data in payloads.items():
            archive.writestr(name, data)
    with zipfile.ZipFile(output) as archive:
        if archive.testzip() is not None:
            raise ValueError('Archive CRC check failed')
        for name, entry in manifest['files'].items():
            if hashlib.sha256(archive.read(name)).hexdigest() != entry['sha256']:
                raise ValueError(f'Output file checksum differs: {name}')
    return hashlib.sha256(output.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--base-sha256', required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--metadata', type=Path, required=True)
    parser.add_argument('--add', action='append', default=[], help='archive-path=local-file')
    args = parser.parse_args()
    additions = {}
    for value in args.add:
        name, path = value.split('=', 1)
        if name in additions:
            raise ValueError(f'Duplicate addition: {name}')
        additions[name] = Path(path).read_bytes()
    checksum = bank(args.base, args.out, additions,
                    json.loads(args.metadata.read_text()), args.base_sha256)
    print(f'Verified increment archive: {args.out.stat().st_size} bytes, SHA-256 {checksum}')


if __name__ == '__main__':
    main()
