"""Observe Lake's search environment and Lean's actual direct-import lookup.

Only the fixed toolchain is executed. Before Lake loads dependency configuration,
the caller's expected installed-input fingerprints are checked, and project
configuration must pass the non-executable TOML subset. This module cannot
authenticate that expectation: the workflow must derive it from a verified
main producer, or from its own trusted cold main build. No credentials may be
present. A missing/mismatched input prevents the environment query.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from kernel_build_environment import dependency_inputs, toolchain_inputs
from kernel_build_inventory import FORBIDDEN_ENV
from kernel_build_layout import NAME, project_layout
from kernel_build_manifest import regular_path, require, unique_json
from kernel_build_packages import package_environment
from kernel_build_restore import no_links

SEARCH_KEYS = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH',
               'DYLD_LIBRARY_PATH', 'PATH', 'LEAN', 'LAKE', 'LAKE_HOME', 'LEAN_AR', 'LEAN_CC')


def validate_toolchain_selection(prefix, observed):
    """A fixed Lake binary must not silently select a different compiler.

    Lake 4.35 InstallPath.lean allows override selection and custom CC/AR.
    This first reuse profile accepts only the verified bundled installation.
    Other valid user toolchains can still build cold; they cannot reuse it.
    """
    prefix = Path(prefix).resolve()
    for key, expected in (('LEAN_SYSROOT', prefix), ('LAKE_HOME', prefix),
                          ('LEAN', prefix/'bin'/('lean.exe' if os.name == 'nt' else 'lean')),
                          ('LAKE', prefix/'bin'/('lake.exe' if os.name == 'nt' else 'lake'))):
        value = observed.get(key)
        require(isinstance(value, str) and Path(value).is_absolute()
                and Path(value).resolve() == expected, 'Lake selected an unverified '+key)
    for key in ('LEAN_AR', 'LEAN_CC'):
        value = observed.get(key)
        if key == 'LEAN_CC' and value is None:
            # None selects the installed Lean's bundled compiler.
            continue
        require(isinstance(value, str) and Path(value).is_absolute()
                and Path(value).resolve().is_relative_to(prefix) and Path(value).is_file(),
                'Lake selected an unverified native tool '+key)


def checked_packages(root, expected_packages, expected_dependencies, *, git_executable='git'):
    actual = package_environment(root, git_executable=git_executable)
    require(actual == expected_packages, 'Lake package configuration differs from verified inputs')
    dependencies, _ = dependency_inputs(root, actual)
    require(dependencies == expected_dependencies, 'Installed dependency bytes differ from verified inputs')


def capture_lake_environment(root, prefix, expected_packages, expected_dependencies,
                             expected_toolchain, *, git_executable='git', python=sys.executable):
    root, prefix = Path(root).absolute(), Path(prefix).absolute()
    no_links(root); no_links(prefix)
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV),
            'Lake environment lookup must run without credentials')
    require(os.environ.get('LAKE_OVERRIDE_LEAN') in (None, '', '0', 'false')
            and not os.environ.get('LEAN_GITHASH') and not os.environ.get('LD_PRELOAD')
            and not os.environ.get('DYLD_INSERT_LIBRARIES'),
            'Unsupported compiler/runtime override; do not query or reuse')
    project_layout(root)
    checked_packages(root, expected_packages, expected_dependencies, git_executable=git_executable)
    require(toolchain_inputs(prefix)['summary'] == expected_toolchain,
            'Compiler installation differs from verified inputs')
    lake = prefix/'bin'/('lake.exe' if os.name == 'nt' else 'lake')
    # Isolated Python ignores project/site modules and PYTHON* startup settings.
    script = 'import json,os;print(json.dumps({k:os.environ.get(k) for k in '+repr(SEARCH_KEYS)+'}))'
    process = subprocess.run([str(lake), 'env', str(python), '-I', '-S', '-c', script],
                             cwd=root, capture_output=True, timeout=120, check=False)
    require(process.returncode == 0 and len(process.stdout) < 1024*1024,
            'Lake search environment could not be observed')
    value = unique_json(process.stdout)
    require(isinstance(value, dict) and set(value) == set(SEARCH_KEYS)
            and all(v is None or isinstance(v, str) for v in value.values()),
            'Malformed Lake search environment')
    validate_toolchain_selection(prefix, value)
    checked_packages(root, expected_packages, expected_dependencies, git_executable=git_executable)
    return value


def observed_file(root, prefix, raw):
    require(isinstance(raw, str) and bool(raw) and '\x00' not in raw,
            'Missing compiler-resolved file')
    path = Path(raw)
    if not path.is_absolute():path = root/path
    no_links(path)
    resolved = path.resolve()
    require(resolved.is_file(), 'Compiler-resolved input file is missing')
    if resolved.is_relative_to(root.resolve()):
        owner, relative = 'workspace', resolved.relative_to(root.resolve()).as_posix()
    elif resolved.is_relative_to(prefix.resolve()):
        owner, relative = 'toolchain', resolved.relative_to(prefix.resolve()).as_posix()
    else:
        raise ValueError('Compiler resolved an input outside the verified workspace/toolchain')
    require(regular_path(relative), 'Unsafe resolved input path')
    before=resolved.stat()
    with resolved.open('rb') as stream:
        digest=hashlib.file_digest(stream,'sha256').hexdigest()
    after=resolved.stat()
    require((before.st_ino,before.st_size,before.st_mtime_ns) ==
            (after.st_ino,after.st_size,after.st_mtime_ns), 'Resolved input changed during lookup')
    return {'owner':owner,'path':relative,'sha256':digest,'size':after.st_size}


def resolve_imports(root, prefix, names, lake_environment, *, kinds=('compiled', 'source')):
    """Use header-only --deps and --src-deps; never import/elaborate PR modules.

    Names normally contain external imports only before compilation. A trusted
    producer can additionally verify its complete project lookup after building.
    Lean 4.35 prints one path per explicit import, in header order, for both
    switches (Lean/Elab/Import.lean printImports and printImportSrcs).
    """
    root, prefix = Path(root).absolute(), Path(prefix).absolute()
    require(not any(os.environ.get(k) for k in FORBIDDEN_ENV),
            'Import lookup must run without credentials')
    require(isinstance(names, (list, tuple)) and names and len(names) <= 10000
            and all(isinstance(n,str) and NAME.fullmatch(n) for n in names)
            and len({n.casefold() for n in names}) == len(names), 'Invalid direct-import inventory')
    require(isinstance(kinds, (list, tuple)) and kinds and len(set(kinds)) == len(kinds)
            and set(kinds) <= {'compiled', 'source'}, 'Invalid import lookup kinds')
    require(isinstance(lake_environment,dict) and set(lake_environment) == set(SEARCH_KEYS)
            and all(v is None or isinstance(v,str) for v in lake_environment.values()),
            'Missing observed Lake search environment')
    lean=prefix/'bin'/('lean.exe' if os.name=='nt' else 'lean')
    environ=dict(os.environ)
    for key,value in lake_environment.items():
        if value is None:environ.pop(key,None)
        else:environ[key]=value
    with tempfile.TemporaryDirectory(prefix='.kernel-import-lookup-',dir=root) as directory:
        source=Path(directory)/'Imports.lean'
        source.write_text('prelude\n'+''.join('import '+n+'\n' for n in names),encoding='utf-8')
        outputs={}
        for kind,switch in (('compiled','--deps'),('source','--src-deps')):
            if kind not in kinds:
                continue
            process=subprocess.run([str(lean),switch,str(source)],cwd=root,env=environ,
                                   capture_output=True,timeout=120,check=False)
            require(process.returncode==0 and len(process.stdout)<=16*1024*1024,
                    'Lean direct-import lookup failed')
            lines=process.stdout.decode('utf-8').splitlines()
            require(len(lines)==len(names), 'Lean returned incomplete or ambiguous import paths')
            outputs[kind]=[observed_file(root,prefix,line) for line in lines]
            require(len({(row['owner'], row['path'].casefold()) for row in outputs[kind]}) == len(names),
                    'Multiple module names resolve to the same input')
    return {name:{kind:rows[index] for kind,rows in outputs.items()} for index,name in enumerate(names)}
