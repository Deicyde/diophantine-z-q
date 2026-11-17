"""Capture one complete input context for the verified-output build path.

Use the reviewed driver, without credentials. The consumer must first verify
the producer and archive, then pass its environment as expected_environment.
Only a trusted cold-main producer calls this without an expected environment.
This module does not grant producer authority, install outputs, or accept an
audit. The driver compares captures before compilation and after the audit.
"""
import os
from pathlib import Path
import platform

from kernel_build_binding import collect_bound_inventory
from kernel_build_controls import verify_controls
from kernel_build_environment import collect_environment
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_layout import project_layout
from kernel_build_manifest import require
from kernel_build_resolution import capture_lake_environment
from kernel_build_runtime import capture_runtime


def portable_lookup(workspace, prefix, observed):
    """Normalize only verified workspace/toolchain roots, not arbitrary paths."""
    workspace, prefix = Path(workspace).resolve(), Path(prefix).resolve()
    def path(value):
        item = Path(value)
        if item.is_absolute():
            item = item.resolve()
            for root, label in ((workspace, '@workspace'), (prefix, '@toolchain')):
                if item.is_relative_to(root):
                    relative = item.relative_to(root).as_posix()
                    return label if relative == '.' else label+'/'+relative
        return value
    lists = {'PATH', 'LEAN_PATH', 'LEAN_SRC_PATH', 'LD_LIBRARY_PATH', 'DYLD_LIBRARY_PATH'}
    result = {}
    for key, value in observed.items():
        require(value is None or isinstance(value, str), 'Malformed actual Lake environment')
        result[key] = (None if value is None else
                       [path(part) for part in value.split(os.pathsep)] if key in lists else path(value))
    return result


def capture_context(workspace, prefix, module_paths, build_commands, *, driver_paths,
                    system_drivers, controls, environ=None, expected_environment=None,
                    git_executable='git', progress=None):
    """Check static inputs before executing the pinned Lake environment query.

    Initial consumer mismatch fails before Lake evaluates dependency configs.
    The actual lookup and Linux runtime then join the identity. New independent
    modules do not change the shared environment: each module's source/imports
    remain in the separate compiler-derived inventory.
    """
    environment = dict(os.environ if environ is None else environ)
    require(not any(environment.get(k) or os.environ.get(k) for k in FORBIDDEN_ENV),
            'Complete input capture requires a credential-free process')
    require(platform.system() == 'Linux', 'Production input context currently requires Linux')
    verify_controls(workspace, controls, environment)
    require(expected_environment is None or isinstance(expected_environment, dict),
            'Malformed authenticated producer environment')
    report = progress or (lambda phase: None)
    report('fingerprinting installed compiler, dependencies and drivers')
    layout = project_layout(workspace)
    identity, detail = collect_environment(workspace, prefix, build_commands, layout,
        driver_paths=driver_paths, git_executable=git_executable, environ=environment, controls=controls)
    if expected_environment is not None:
        require(all(expected_environment.get(k) == v for k, v in identity.items()),
                'Installed build inputs differ from the authenticated producer')
    packages = identity['packages']
    compiler = {'summary': identity['toolchain'], 'files': detail['toolchain_files'],
                'builtins': detail['builtins']}
    report('checking actual Lake and Lean lookup')
    lookup = capture_lake_environment(workspace, prefix, packages, identity['dependency_inputs'],
        compiler['summary'], git_executable=git_executable, environ=environment, controls=controls)
    modules, binding = collect_bound_inventory(workspace, prefix, module_paths, packages,
        compiler, detail['dependency_files'], lookup)
    require(binding['project_layout'] == layout, 'Build layout changed during context capture')
    # Include actual post-Lake search paths, in addition to configured overrides.
    identity['actual_lookup'] = portable_lookup(workspace, prefix, lookup)
    report('checking selected Linux runtime libraries')
    native_roots = {str(Path(prefix).resolve()): detail['toolchain_files']}
    for name, files in detail['dependency_files'].items():
        native_roots[str((Path(workspace)/packages['packages'][name]['location']).resolve())] = files
    runtime, runtime_detail = capture_runtime(native_roots, system_drivers, environ={**environment, **lookup})
    identity['runtime'] = runtime
    if expected_environment is not None:
        require(identity == expected_environment, 'Actual lookup or runtime differs from the authenticated producer')
    verify_controls(workspace, controls, environment)
    report('input context captured')
    return {'schema': 'kernel-build-context/v1', 'environment': identity, 'modules': modules,
            'project_paths': binding['project_resolution']}, {
                'installed_inputs': detail, 'binding': binding,
                'actual_lookup': lookup, 'runtime': runtime_detail}
