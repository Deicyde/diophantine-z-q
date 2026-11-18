"""Build only missing local imports, and check the requested file(s) serially."""
import os
import pathlib
import re
import subprocess as sp
import sys
import fcntl

root = pathlib.Path.cwd()
store = root / '.lake/build/lib/lean'
third = root / 'ThirdParty/GreenTao'
checked = {}
cache_revision = os.environ.get('RC_STAGES_CACHE_REV')
dirty = set(sp.check_output(
    ['git', 'diff', '--name-only', '--diff-filter=M', cache_revision, 'HEAD', '--', '*.lean'],
    text=True).splitlines()) if cache_revision else set()
stamp = root / '.lake/rc-stages-rebuilt'
stamp.mkdir(exist_ok=True)
lock = open(root / '.lake/rc-stages-lean.lock', 'w')
fcntl.flock(lock, fcntl.LOCK_EX)

def run(path, out):
    up = sp.check_output(['uptime'], text=True)
    mem = sp.check_output(['free', '-g'], text=True)
    load = float(re.search(r'load average: ([\d.]+)', up)[1])
    avail = int(mem.splitlines()[1].split()[-1])
    if load > 120 or avail < 20:
        sys.exit(f'Lean held: load {load}, available memory {avail} GB')
    print(f'{path}: load {load}, available memory {avail} GB', flush=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    sp.run(['lake', 'env', 'lean', '-j1', f"-DmaxHeartbeats={os.environ.get('RC_STAGES_HEARTBEATS', '500000')}", '-o', str(out), str(path)], check=True)

def build(path, force=False):
    if path in checked:
        return checked[path]
    name = path.relative_to(third) if path.is_relative_to(third) else path.relative_to(root / 'lean') if path.is_relative_to(root / 'lean') else path.relative_to(root)
    out = store / name.with_suffix('.olean')
    refreshed = (stamp / '.'.join(name.parts)).exists()
    local_edit = ('OneProof/RC/Stages/' in name.as_posix() and out.exists()
                  and path.stat().st_mtime > out.stat().st_mtime)
    stale = not out.is_file() or local_edit or str(path.relative_to(root)) in dirty
    if refreshed and not force and not local_edit:
        checked[path] = True
        return True
    if not cache_revision and not stale and not force:
        checked[path] = False
        return False
    src = path.read_text()
    # Imports are in the module header. Strip nested comments before reading it.
    src = re.sub(r'/-.*?-/', '', src, flags=re.S)
    for m in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([\w.]+)', src, flags=re.M):
        rel = pathlib.Path(*m.split('.')).with_suffix('.lean')
        for folder in [root, third, root / 'lean']:
            dep = folder / rel
            if dep.is_file():
                stale |= build(dep)
                break
    if stale or force:
        run(path.relative_to(root), out)
        (stamp / '.'.join(name.parts)).touch()
    checked[path] = stale or force
    return checked[path]

failed = False
for arg in sys.argv[1:]:
    try:
        build((root / arg).resolve(), force=True)
    except sp.CalledProcessError as e:
        print(f"{arg}: build failed ({e.returncode})", flush=True)
        failed = True
sys.exit(int(failed))
