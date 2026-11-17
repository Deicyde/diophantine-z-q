"""Download one authenticated GitHub artifact without forwarding its API token.

The selector supplies the artifact ID and expected archive digest. A successful
download is not a successful build: the manifest verifier must still inspect
every archive member before restoration.
"""
import hashlib
import os
from pathlib import Path
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

from kernel_build_manifest import MAX_OUTPUT_BYTES, MAX_MANIFEST, MAX_MEMBERS, digest, positive_int, require
from kernel_build_restore import no_links

MAX_DOWNLOAD_BYTES = MAX_OUTPUT_BYTES + MAX_MANIFEST + MAX_MEMBERS * 1024
MAX_DOWNLOAD_SECONDS = 600


def storage_url(value):
    require(isinstance(value, str), 'Missing artifact download location')
    parsed = urllib.parse.urlsplit(value)
    hostname = parsed.hostname or ''
    require(parsed.scheme == 'https' and parsed.port in (None, 443)
            and parsed.username is None and parsed.password is None and not parsed.fragment
            and (hostname.endswith('.blob.core.windows.net')
                 or hostname.endswith('.actions.githubusercontent.com')),
            'Unrecognized artifact storage host')
    return value


class NoAPIRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


class StorageRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        storage_url(newurl)
        result = super().redirect_request(req, fp, code, msg, headers, newurl)
        if result is not None:
            result.remove_header('Authorization')
        return result


def download_archive(selection, token, directory, *, opener_factory=urllib.request.build_opener):
    """Write a unique verified ZIP, or remove this call's partial download.

    The directory must be a trusted local path outside candidate execution.
    Neither the API token nor the signed storage URL is included in the result
    or in error messages. Unknown storage endpoints take the cold-build path.
    """
    require(isinstance(selection, dict) and selection.get('status') == 'selected',
            'No selected artifact to download')
    producer = selection.get('producer')
    require(isinstance(producer, dict), 'Missing producer identity')
    repository = producer.get('repository')
    import re
    require(isinstance(repository, str)
            and re.fullmatch(r'[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+', repository)
            and positive_int(selection.get('artifact_id')) and digest(selection.get('archive_sha256')),
            'Invalid authenticated artifact identity')
    require(isinstance(token, str) and bool(token), 'Missing GitHub read token')
    directory = Path(directory).absolute()
    no_links(directory)
    require(directory.is_dir(), 'Missing trusted download directory')
    api_url = f"https://api.github.com/repos/{repository}/actions/artifacts/{selection['artifact_id']}/zip"
    request = urllib.request.Request(api_url, headers={
        'Authorization': 'Bearer ' + token, 'Accept': 'application/vnd.github+json',
        'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'kernel-verified-main-build'})
    try:
        with opener_factory(NoAPIRedirect()).open(request, timeout=30):
            raise ValueError('Artifact API did not return its storage redirect')
    except urllib.error.HTTPError as error:
        try:
            require(error.code == 302, 'Artifact API did not return a storage redirect')
            location = storage_url(error.headers.get('Location'))
        finally:
            error.close()
    except (urllib.error.URLError, OSError):
        raise ValueError('Artifact API request failed') from None
    # This request is deliberately new. Do not reuse the authorized API request
    # or its headers when following the signed redirect to object storage.
    request = urllib.request.Request(location, headers={'User-Agent': 'kernel-verified-main-build'})
    output = None
    complete = False
    try:
        started = time.monotonic()
        with opener_factory(StorageRedirect()).open(request, timeout=30) as response:
            with tempfile.NamedTemporaryFile(prefix='kernel-main-', suffix='.zip',
                                             dir=directory, delete=False) as target:
                output = Path(target.name)
                observed, size = hashlib.sha256(), 0
                while data := response.read(1024 * 1024):
                    size += len(data)
                    require(size <= MAX_DOWNLOAD_BYTES, 'Artifact exceeds the download size limit')
                    require(time.monotonic() - started <= MAX_DOWNLOAD_SECONDS,
                            'Artifact exceeds the download time limit')
                    observed.update(data)
                    target.write(data)
                require(observed.hexdigest() == selection['archive_sha256'],
                        'Downloaded artifact digest mismatch')
        os.chmod(output, 0o600)
        complete = True
        return {'path': str(output), 'archive_sha256': selection['archive_sha256'],
                'download_bytes': size, 'seconds': round(time.monotonic() - started, 3),
                'artifact_id': selection['artifact_id'], 'producer': producer}
    except (urllib.error.URLError, OSError):
        raise ValueError('Artifact storage download failed') from None
    finally:
        if output is not None and not complete:
            # Only this invocation's unique file is removed; no recursive cleanup.
            output.unlink(missing_ok=True)
