"""Stage verified module outputs, then install them into empty project roots.

The caller supplies the authenticated producer and archive digest, and the
current compiler-derived input inventory. No download or candidate execution
occurs here. Existing build roots are never cleaned or overwritten.
"""
import hashlib
import os
from pathlib import Path
import shutil
import tempfile
import zipfile

from kernel_build_manifest import require, reusable_modules, verify_archive

BUILD_ROOTS = ('.lake/build', 'lean/.lake/build')


def no_links(path):
    """Also reject Windows junctions, which need not report as symbolic links."""
    for part in (path, *path.parents):
        require(not part.is_symlink() and not part.is_junction(),
                'Linked directory is not a build-output destination')


def install(stream, archive_sha256, producer, current_modules, current_environment, workspace):
    """Return installed paths only after all bytes and destinations are checked.

    Use before starting any candidate build process. Source collection and the
    following build run without credentials or automatic Lake cache restores.
    On an install error, move this call's installed roots back into its private
    staging directory. No dependency package or pre-existing output is removed.
    """
    workspace = Path(workspace).absolute()
    no_links(workspace)
    require(workspace.is_dir(), 'Missing candidate workspace')
    manifest = verify_archive(stream, archive_sha256, producer)
    selected = reusable_modules(manifest['modules'], current_modules,
                                manifest['environment'], current_environment)
    paths = sorted(p for name in selected for p in manifest['modules'][name]['outputs'])
    if not paths:
        return {'status': 'cold', 'reason': 'No modules have unchanged complete inputs',
                'modules': [], 'outputs': [], 'output_bytes': 0}
    roots = [root for root in BUILD_ROOTS if any(p.startswith(root + '/') for p in paths)]
    for root in roots:
        destination = workspace / root
        no_links(destination)
        require(not destination.exists(), 'Project build root already exists; refusing to overwrite')
        # The local package must already be an ordinary source directory.
        require(root == '.lake/build' or (workspace / 'lean').is_dir(),
                'Missing local Lean source package')
    # A sibling of the root build directory keeps rename on the same filesystem.
    stage = Path(tempfile.mkdtemp(prefix='.kernel-verified-stage-', dir=workspace))
    installed = []
    complete = False
    try:
        stream.seek(0)
        with zipfile.ZipFile(stream) as archive:
            for relative in paths:
                destination = stage / relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                expected = manifest['outputs'][relative]
                observed, size = hashlib.sha256(), 0
                with archive.open('outputs/' + relative) as data, destination.open('xb') as out:
                    while chunk := data.read(1024 * 1024):
                        size += len(chunk)
                        require(size <= expected['size'], 'Output grew during staging')
                        observed.update(chunk)
                        out.write(chunk)
                require(size == expected['size'] and observed.hexdigest() == expected['sha256'],
                        'Output changed during staging')
                # Recent extraction timestamps must not bypass Lake input hashing.
                os.chmod(destination, 0o644)
                os.utime(destination, (1, 1))
        # Recheck the exact open archive, not a reopened path, before installation.
        stream.seek(0)
        require(hashlib.file_digest(stream, 'sha256').hexdigest() == archive_sha256,
                'Artifact changed during staging')
        for root in roots:
            destination = workspace / root
            no_links(destination)
            require(not destination.exists(), 'Build output appeared during staging')
            destination.parent.mkdir(parents=True, exist_ok=True)
        for root in roots:
            destination = workspace / root
            no_links(destination)
            require(not destination.exists(), 'Build output appeared before install')
            # No candidate process may run concurrently with this install.
            os.rename(stage / root, destination)
            installed.append(root)
        complete = True
    finally:
        if not complete:
            # Reverse only renames performed by this invocation. If rollback
            # itself fails, raise and retain the stage for diagnosis; never
            # continue into compilation with a partially restored state.
            for root in reversed(installed):
                os.rename(workspace / root, stage / root)
        # This unique stage was created by us under the checked workspace. It
        # contains verified regular output files only; dependency roots are not
        # included in its inventory and are never recursively removed.
        require(stage.parent == workspace and stage.name.startswith('.kernel-verified-stage-'),
                'Unexpected staging directory')
        no_links(stage)
        shutil.rmtree(stage)
    return {'status': 'restored', 'modules': sorted(selected), 'outputs': paths,
            'output_bytes': sum(manifest['outputs'][p]['size'] for p in paths),
            'archive_sha256': archive_sha256, 'producer': producer}
