"""Select a reusable main-build producer from authenticated GitHub metadata.

This code does not check out, import, or execute candidate code. It does not
download or restore build outputs. Run the installed, reviewed copy before
candidate execution, with a step-scoped read-only token. A missing eligible
producer means a cold build, never a weaker audit.
"""
import base64
import hashlib
import json
import os
import re
import urllib.error
import urllib.request

from kernel_build_manifest import (WORKFLOW, JOB, authenticated_producer, digest,
                                   nested, positive_int, require, unique_json)

MAX_RESPONSE_BYTES = 8 * 1024 * 1024
MAX_LIST_ITEMS = 10000


def sha(value):
    return isinstance(value, str) and re.fullmatch(r'[0-9a-f]{40}', value) is not None


class GitHub:
    """JSON-only client. Never follow a redirect with the token attached."""

    def __init__(self, token):
        require(isinstance(token, str) and bool(token), 'Missing GitHub read token')
        self.token = token

    def __call__(self, path):
        require(isinstance(path, str) and path.startswith('/repos/')
                and not any(c in path for c in ('\\', '\r', '\n', '#')),
                'Invalid GitHub API path')

        class NoRedirect(urllib.request.HTTPRedirectHandler):
            def redirect_request(self, req, fp, code, msg, headers, newurl):
                return None

        req = urllib.request.Request('https://api.github.com' + path, headers={
            'Authorization': 'Bearer ' + self.token,
            'Accept': 'application/vnd.github+json',
            'X-GitHub-Api-Version': '2022-11-28',
            'User-Agent': 'kernel-verified-main-build'})
        with urllib.request.build_opener(NoRedirect()).open(req, timeout=30) as response:
            raw = response.read(MAX_RESPONSE_BYTES + 1)
        require(len(raw) <= MAX_RESPONSE_BYTES, 'GitHub JSON response is too large')
        value = unique_json(raw)
        require(isinstance(value, dict), 'Malformed GitHub object')
        return value


def complete_list(api, path, field):
    """Read every page, refusing duplicates, truncation and changing counts."""
    result, ids, count = [], set(), None
    for page in range(1, MAX_LIST_ITEMS // 100 + 2):
        response = api(path + ('&' if '?' in path else '?') + f'per_page=100&page={page}')
        require(isinstance(response, dict), 'Malformed paginated response')
        reported = response.get('total_count')
        rows = response.get(field)
        require(type(reported) is int and 0 <= reported <= MAX_LIST_ITEMS
                and isinstance(rows, list) and len(rows) <= 100,
                'Unbounded or malformed paginated response')
        if count is None:
            count = reported
        require(count == reported, 'Paginated inventory changed during selection')
        for row in rows:
            require(isinstance(row, dict) and positive_int(row.get('id'))
                    and row['id'] not in ids, 'Duplicate or malformed paginated item')
            ids.add(row['id'])
            result.append(row)
        require(len(result) <= count, 'Paginated count is inconsistent')
        if len(result) == count:
            return result
        require(len(rows) == 100, 'Paginated inventory is incomplete')
    raise ValueError('Paginated inventory exceeds the page limit')


def ancestor(api, prefix, commit, observed_main):
    require(sha(commit) and sha(observed_main), 'Invalid ancestry input')
    comparison = api(prefix + f'/compare/{commit}...{observed_main}')
    require(isinstance(comparison, dict)
            and nested(comparison, 'base_commit').get('sha') == commit
            and nested(comparison, 'merge_base_commit').get('sha') == commit
            and type(comparison.get('behind_by')) is int and comparison['behind_by'] == 0
            and comparison.get('status') in ('ahead', 'identical'),
            'Producer is not an ancestor of the observed main tip')


def workflow_digest(api, prefix, commit):
    value = api(prefix + f'/contents/{WORKFLOW}?ref={commit}')
    require(isinstance(value, dict) and value.get('path') == WORKFLOW
            and value.get('type') == 'file' and value.get('encoding') == 'base64'
            and isinstance(value.get('content'), str), 'Missing producer workflow bytes')
    content = base64.b64decode(''.join(value['content'].split()), validate=True)
    require(type(value.get('size')) is int and value['size'] == len(content),
            'Producer workflow byte count is inconsistent')
    return hashlib.sha256(content).hexdigest()


def select_producer(api, repository, approved_workflow_sha256, *, search_limit=10):
    """Inspect recent successes; an older omitted hit is only a cache miss.

    `api` must provide authenticated API responses; the approved workflow hash
    comes from the reviewed consumer workflow, never from the candidate or a
    bundle. Full job/artifact inventories are paginated. Fresh reads of the run
    and artifact reject a concurrent retry or deletion/replacement.
    """
    require(isinstance(repository, str)
            and re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)
            and digest(approved_workflow_sha256)
            and type(search_limit) is int and 1 <= search_limit <= 100,
            'Invalid trusted selector configuration')
    prefix = '/repos/' + repository
    repo = api(prefix)
    require(isinstance(repo, dict) and repo.get('full_name') == repository
            and repo.get('default_branch') == 'main', 'Unexpected repository/default branch')
    ref = api(prefix + '/git/ref/heads/main')
    observed_main = nested(ref, 'object').get('sha')
    require(ref.get('ref') == 'refs/heads/main' and nested(ref, 'object').get('type') == 'commit'
            and sha(observed_main), 'Missing authenticated main tip')
    response = api(prefix + '/actions/workflows/kernel-lean.yml/runs?branch=main&status=success&per_page=100')
    require(isinstance(response, dict) and isinstance(response.get('workflow_runs'), list)
            and len(response['workflow_runs']) <= 100, 'Malformed producer search')
    rejected = []
    seen = set()
    for candidate in response['workflow_runs'][:search_limit]:
        require(isinstance(candidate, dict) and positive_int(candidate.get('id'))
                and candidate['id'] not in seen, 'Malformed or duplicate producer search hit')
        run_id = candidate['id']
        seen.add(run_id)
        try:
            run = api(prefix + f'/actions/runs/{run_id}')
            require(isinstance(run, dict) and run.get('id') == run_id
                    and positive_int(run.get('run_attempt')) and sha(run.get('head_sha')),
                    'Malformed fresh producer run')
            # Refuse foreign or incomplete runs before any further artifact lookup.
            require(nested(run, 'repository').get('full_name') == repository
                    and nested(run, 'head_repository').get('full_name') == repository
                    and run.get('event') in ('push', 'workflow_dispatch')
                    and run.get('head_branch') == 'main' and run.get('path') == WORKFLOW
                    and run.get('status') == 'completed' and run.get('conclusion') == 'success',
                    'Run is not a successful main build')
            attempt, commit = run['run_attempt'], run['head_sha']
            ancestor(api, prefix, commit, observed_main)
            observed_hash = workflow_digest(api, prefix, commit)
            require(observed_hash == approved_workflow_sha256, 'Producer workflow is not approved')
            jobs = complete_list(api, prefix + f'/actions/runs/{run_id}/attempts/{attempt}/jobs', 'jobs')
            selected_jobs = [job for job in jobs if job.get('name') == JOB]
            require(len(selected_jobs) == 1, 'Missing or ambiguous kernel job')
            artifacts = complete_list(api, prefix + f'/actions/runs/{run_id}/artifacts', 'artifacts')
            matches = [a for a in artifacts if a.get('name') == f'kernel-main-build-{run_id}-{attempt}']
            require(len(matches) == 1, 'Missing or ambiguous main-build artifact')
            artifact = api(prefix + f"/actions/artifacts/{matches[0]['id']}")
            require(isinstance(artifact, dict) and artifact.get('id') == matches[0]['id'],
                    'Artifact changed during selection')
            archive_digest = artifact.get('digest')
            require(isinstance(archive_digest, str) and archive_digest.startswith('sha256:'),
                    'Missing authenticated artifact digest')
            producer = authenticated_producer(run, selected_jobs[0], artifact,
                repository=repository, approved_workflow_sha256=approved_workflow_sha256,
                observed_workflow_sha256=observed_hash, main_commit=commit,
                archive_sha256=archive_digest[len('sha256:'):])
            # The latest-run response changes on a retry. Never admit a still-
            # running attempt or accidentally combine the old job with a new run.
            again = api(prefix + f'/actions/runs/{run_id}')
            require(isinstance(again, dict) and all(again.get(k) == run.get(k) for k in (
                'id', 'run_attempt', 'head_sha', 'head_branch', 'event', 'path',
                'repository', 'head_repository', 'status', 'conclusion')),
                'Producer run changed during selection')
            return {'status': 'selected', 'observed_main': observed_main, 'producer': producer,
                    'job_id': selected_jobs[0]['id'], 'artifact_id': artifact['id'],
                    'archive_sha256': archive_digest[len('sha256:'):],
                    'rejected': rejected, 'search_limit': search_limit}
        except (ValueError, urllib.error.HTTPError, urllib.error.URLError) as error:
            # Log only a short reason, never request headers, a token, or a signed URL.
            reason = str(error) if isinstance(error, ValueError) else type(error).__name__
            rejected.append({'run_id': run_id, 'reason': reason[:240]})
    return {'status': 'cold', 'reason': 'No eligible verified main-build artifact',
            'observed_main': observed_main, 'rejected': rejected, 'search_limit': search_limit}


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True)
    parser.add_argument('--approved-workflow-sha256', required=True)
    args = parser.parse_args()
    result = select_producer(GitHub(os.environ.get('GH_TOKEN')),
                             args.repository, args.approved_workflow_sha256)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
