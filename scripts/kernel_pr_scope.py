#!/usr/bin/env python3
"""Conservative PR-only kernel skip decision; embedded before checkout in CI.

No candidate source is executed. Unknown inputs, malformed API responses and
incomplete/racing diffs all request the full build. See docs/kernel-ci-scope.md.
"""
import base64
import json
import os
from pathlib import Path, PurePosixPath
import re
import urllib.parse
import urllib.request


def api(repo, path):
    req = urllib.request.Request('https://api.github.com/repos/' + repo + path,
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json', 'X-GitHub-Api-Version': '2022-11-28'})
    with urllib.request.urlopen(req, timeout=30) as response:
        return json.load(response)


def valid_path(path):
    return (isinstance(path, str) and bool(path) and not path.startswith('/')
            and '\\' not in path and ':' not in path
            and all(p not in {'', '.', '..'} for p in path.split('/')))


def contract_paths(repo, sha):
    value = api(repo, '/contents/KERNEL_CONTRACT.json?ref=' + sha)
    if value.get('type') != 'file' or value.get('encoding') != 'base64':
        raise ValueError('Kernel contract is not an inline regular file')
    contract = json.loads(base64.b64decode(value['content']))
    files = contract['files']
    if contract.get('schema') != 'kernel-contract/v1' or not isinstance(files, dict) or not files:
        raise ValueError('Missing or unknown kernel contract')
    if not all(valid_path(p) and isinstance(h, str) and re.fullmatch(r'[0-9a-f]{64}', h)
               for p, h in files.items()):
        raise ValueError('Malformed kernel contract entries')
    return set(files)


def affects_kernel(path, locked):
    if not valid_path(path):
        return True
    name = PurePosixPath(path).name
    # validate() scans ALL tracked Lean sources and lakefiles for bypass options.
    if (path in locked or path.endswith('.lean')
            or name in {'lakefile.toml', 'lakefile.lean', 'lake-manifest.json', 'lean-toolchain', 'KERNEL_CONTRACT.json'}
            or path.startswith(('ZInQKernel/', 'ThirdParty/', 'lean/', 'scripts/', '.lake/', 'build/kernel-ci/'))
            or path in {'.gitattributes', '.gitmodules', '.github/workflows/kernel-lean.yml'}):
        return True
    # These independent review-gate sources/tests do not feed the kernel job.
    if path in {'.github/workflows/protocol-b.yml', '.github/protocol-b-reviewer.md'}:
        return False
    if path.startswith('tests/protocol_b/') and path.endswith('.py'):
        return False
    if path.startswith(('.github/', 'tests/', 'build/')):
        return True
    # Only ordinary documentation formats qualify for the remaining skip path.
    # Data, archives, executables and any unrecognized extension run the build.
    return PurePosixPath(path).suffix.lower() not in {'.md', '.tex', '.bib', '.pdf'}


def decide(event_name, event, repo):
    if event_name != 'pull_request':
        return True, 'Pushes and manual runs always perform the full kernel build.', []
    pr = event['pull_request']
    number, base, head = pr['number'], pr['base']['sha'], pr['head']['sha']
    if type(number) is not int or number < 1 or not all(re.fullmatch(r'[0-9a-f]{40}', s) for s in [base, head]):
        raise ValueError('Invalid PR identity')
    if not re.fullmatch(r'[\w.-]+/[\w.-]+', repo):
        raise ValueError('Invalid repository')
    current = api(repo, f'/pulls/{number}')
    def same_revision(value):
        return value['base']['sha'] == base and value['head']['sha'] == head
    if not same_revision(current):
        raise ValueError('PR base or head changed')
    count = current['changed_files']
    if type(count) is not int or not 1 <= count <= 3000:
        raise ValueError('Unavailable or oversized changed-file list')
    rows = []
    for page in range(1, (count + 99) // 100 + 1):
        batch = api(repo, f'/pulls/{number}/files?per_page=100&page={page}')
        if not isinstance(batch, list):
            raise ValueError('Invalid changed-file page')
        rows.extend(batch)
    if len(rows) != count or len({r['filename'] for r in rows}) != count:
        raise ValueError('Incomplete or duplicate changed-file list')
    paths = set()
    for row in rows:
        if row.get('status') not in {'added', 'removed', 'modified', 'renamed', 'copied', 'changed'}:
            raise ValueError('Ambiguous change status')
        paths.add(row['filename'])
        if row['status'] == 'renamed':
            paths.add(row['previous_filename'])
    if not all(valid_path(p) for p in paths):
        raise ValueError('Invalid changed path')
    locked = contract_paths(repo, base) | contract_paths(repo, head)
    if not same_revision(api(repo, f'/pulls/{number}')):
        raise ValueError('PR changed during classification')
    affected = sorted(p for p in paths if affects_kernel(p, locked))
    if affected:
        return True, 'Kernel inputs or unclassified files changed: ' + ', '.join(affected[:10]), sorted(paths)
    return False, 'Only documentation or independent Protocol B files changed; no kernel build or audit input changed.', sorted(paths)


def main():
    try:
        event_name = os.environ.get('GITHUB_EVENT_NAME', '')
        event = json.loads(Path(os.environ['GITHUB_EVENT_PATH']).read_text()) if event_name == 'pull_request' else {}
        full, reason, paths = decide(event_name, event, os.environ.get('GITHUB_REPOSITORY', ''))
    except Exception as error:
        full, reason, paths = True, 'Could not safely classify the PR; performing the full build (' + type(error).__name__ + ').', []
    print(json.dumps({'full_build': full, 'reason': reason, 'changed_paths': paths}))
    with open(os.environ['GITHUB_OUTPUT'], 'a', encoding='utf-8') as out:
        out.write('full_build=' + str(full).lower() + '\n')
    with open(os.environ['GITHUB_STEP_SUMMARY'], 'a', encoding='utf-8') as summary:
        summary.write(('Full kernel build required. ' if full else 'Kernel build skipped. ') + reason + '\n')


if __name__ == '__main__':
    main()
