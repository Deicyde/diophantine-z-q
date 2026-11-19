"""Prepare explicit Lake cache controls outside the candidate checkout.

These controls are for the verified-output build path after dependency setup.
They do not fetch dependencies, restore outputs, authenticate a producer, or
replace runtime/input fingerprints. The trusted driver must pass the returned
environment to every Lake invocation and verify it before and after execution.
No process-wide environment or existing user configuration is changed.
"""
import hashlib
import os
from pathlib import Path

from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_manifest import require
from kernel_build_restore import no_links


SETTINGS = {
    # The flags separately disable artifact restoration and dependency cache
    # downloads. A fresh explicit cache path is set below: an empty path is
    # replaced by the workspace cache in child environments by Lake 4.35.
    'LAKE_NO_CACHE': 'true',
    'LAKE_ARTIFACT_CACHE': 'false',
    'LAKE_RESTORE_ARTIFACTS': 'false',
    'LAKE_PKG_URL_MAP': '{}',
}
CACHE_ENDPOINT_KEYS = ('LAKE_CACHE_ARTIFACT_ENDPOINT', 'LAKE_CACHE_REVISION_ENDPOINT',
                       'LAKE_CACHE_SERVICE')
EMPTY_HASH = hashlib.sha256(b'').hexdigest()


def verify_controls(workspace, controls, environment):
    """Fail before execution if controls moved, changed, or gained credentials."""
    workspace, controls = Path(workspace).absolute(), Path(controls).absolute()
    no_links(workspace); no_links(controls)
    require(controls.is_dir() and not controls.resolve().is_relative_to(workspace.resolve()),
            'Lake controls must be outside the candidate checkout')
    require(isinstance(environment, dict) and not any(environment.get(k) for k in FORBIDDEN_ENV),
            'Controlled Lake execution must have no API or artifact credentials')
    require(all(environment.get(k) == v for k, v in SETTINGS.items())
            and not any(k in environment for k in CACHE_ENDPOINT_KEYS),
            'Lake cache controls were changed')
    config = controls/'lake-config.toml'
    cache = controls/'cache'
    no_links(config)
    no_links(cache)
    require(environment.get('LAKE_CACHE_DIR') == str(cache) and cache.is_dir(),
            'Expected the fresh explicit Lake cache directory')
    require(environment.get('LAKE_CONFIG') == str(config) and config.is_file()
            and config.stat().st_size == 0 and config.read_bytes() == b'',
            'Expected the unchanged explicit empty Lake configuration')
    return {'schema': 'kernel-lake-controls/v1', 'settings': dict(SETTINGS),
            'config_sha256': EMPTY_HASH, 'cache_endpoints': 'unset', 'cache': 'fresh-per-run'}


def prepare_controls(workspace, destination, *, environ=None):
    """Create fresh per-run controls; never overwrite or read a user's config."""
    workspace, destination = Path(workspace).absolute(), Path(destination).absolute()
    original = dict(os.environ if environ is None else environ)
    require(not any(original.get(k) for k in FORBIDDEN_ENV),
            'Prepare Lake controls only after removing API/artifact credentials')
    no_links(workspace); no_links(destination)
    require(workspace.is_dir() and destination.parent.is_dir()
            and not destination.exists()
            and not destination.resolve().is_relative_to(workspace.resolve()),
            'A new control directory outside the candidate checkout is required')
    destination.mkdir()
    config = destination/'lake-config.toml'
    with config.open('xb'):
        pass
    (destination/'cache').mkdir()
    original.update(SETTINGS)
    original['LAKE_CONFIG'] = str(config)
    original['LAKE_CACHE_DIR'] = str(destination/'cache')
    for key in CACHE_ENDPOINT_KEYS:
        original.pop(key, None)
    record = verify_controls(workspace, destination, original)
    return original, record
