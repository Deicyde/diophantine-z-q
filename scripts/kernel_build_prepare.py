"""Connect authenticated artifact facts to input checking and output restore.

Run the reviewed copy without credentials, after the separate GitHub selector
and downloader have finished. Their receipt, not candidate input, supplies the
producer and archive digest. A missing or incompatible bundle selects a cold
build. Once installation starts, an error is fatal rather than hiding a possibly
partial restore behind the cold path. The full kernel audit is always required.
"""
import lzma
import os
import subprocess
import zipfile
import zlib

from kernel_build_context import capture_context
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import digest, require, verify_archive
from kernel_build_restore import install


def prepare_candidate(workspace, prefix, module_paths, build_commands, *, selection,
                      archive, driver_paths, system_drivers, controls, environ=None,
                      git_executable='git', progress=None):
    """Verify before restoring; never evaluate a config for an invalid bundle.

    archive is the already opened, seekable binary file returned by trusted
    downloading. The same open file is verified again during installation.
    No path is reopened and no producer claim comes from the archive itself.
    """
    environment = dict(os.environ if environ is None else environ)
    require(not any(environment.get(k) or os.environ.get(k) for k in FORBIDDEN_ENV),
            'Candidate preparation must run without credentials')
    require(isinstance(selection, dict) and selection.get('status') in ('selected', 'cold'),
            'Missing trusted selector result')
    if selection['status'] == 'cold':
        return {'status': 'cold', 'reason': 'No authenticated main producer selected',
                'audit_required': True}, None, None
    require(isinstance(selection.get('producer'), dict) and digest(selection.get('archive_sha256')),
            'Incomplete authenticated producer receipt')
    require(archive is not None and archive.seekable(), 'Missing open downloaded archive')
    producer, archive_sha256 = selection['producer'], selection['archive_sha256']
    # All optional-cache rejection occurs before any project outputs are installed.
    try:
        manifest = verify_archive(archive, archive_sha256, producer)
    except (ValueError, OSError, EOFError, NotImplementedError,
            zipfile.BadZipFile, zlib.error, lzma.LZMAError) as error:
        return {'status': 'cold', 'reason': 'Downloaded bundle failed verification',
                'detail': str(error)[:240] if isinstance(error, ValueError) else type(error).__name__,
                'audit_required': True}, None, None
    try:
        context, detail = capture_context(workspace, prefix, module_paths, build_commands,
            driver_paths=driver_paths, system_drivers=system_drivers, controls=controls,
            environ=environment, expected_environment=manifest['environment'],
            git_executable=git_executable, progress=progress)
    except (ValueError, OSError, subprocess.TimeoutExpired) as error:
        return {'status': 'cold', 'reason': 'Installed build inputs are ineligible or differ from the producer',
                'detail': str(error)[:240] if isinstance(error, ValueError) else type(error).__name__,
                'audit_required': True}, None, None
    restored = install(archive, archive_sha256, producer, context['modules'],
                       context['environment'], workspace)
    return {**restored, 'audit_required': True}, context, detail
