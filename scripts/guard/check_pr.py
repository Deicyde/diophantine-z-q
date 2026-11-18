"""Pull-request guard: board rows a change removes or adds, the owners of the files it touches, and the problems it
brings into the generated contributor files.

Usage (from the repository root):
  python3 scripts/guard/check_pr.py rows --base REV [--tree REV] [--removes "a, b"] [--adds "c, d"]
  python3 scripts/guard/check_pr.py owners --base REV [--tree REV]
  python3 scripts/guard/check_pr.py render --base REV

rows: compares docs/one-proof/open-statements.json at --base (main) with the merged result (--tree, default the
working tree; in a pull_request workflow the checkout is GitHub's merge commit). Every field present at --base and
missing from the result must be listed in the pull request body on a line `Removes-rows: field, field` (read from the
PR_BODY environment variable) or in --removes, and every field missing at --base and present in the result on a line
`Adds-rows: field, field` or in --adds. The names go on the same line as the label; lines inside HTML comments (such
as the pull request template's) do not count. Exit 1 otherwise. This catches a branch built on an older main that
would drop newer rows, or bring back rows that a fold removed.

owners: prints a warning for each file the change touches that OWNERS.tsv assigns to an owner, so the owner can be
told. The table is read at --base, so a change cannot edit away its own warning, and a moved file counts at its old
path as well as its new one.

rows and owners exit 2, having checked nothing, if --base or --tree does not name a commit or tree of this repository,
or if git cannot read a file there. Otherwise owners never fails.

render: runs scripts/one_proof/render_open.py --check in the working tree and in a temporary worktree of --base, and
prints a warning for each problem it reports in the working tree and not at --base, so a problem main already has
(for example an OPEN.md that lags a claims-sync commit until the next fold) is not blamed on the change. If --base has
no render_open.py, every problem is reported. It always exits 0.
"""
import json, os, re, shutil, subprocess, sys, tempfile

OPEN = 'docs/one-proof/open-statements.json'
OWNERS = 'OWNERS.tsv'
RENDER = 'scripts/one_proof/render_open.py'
HTML_COMMENT = re.compile(r'<!--.*?-->', re.S)


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, check=True).stdout


def tree_ish(rev):
    """True if rev names a commit or a tree of this repository."""
    return subprocess.run(['git', 'rev-parse', '--verify', '--quiet', f'{rev}^{{tree}}'],
                          capture_output=True).returncode == 0


def read_at(rev, path):
    """The file at rev (None: the working tree), or None if rev has no such path. Any other git failure raises."""
    if rev is None:
        return open(path).read() if os.path.exists(path) else None
    # rev-parse finds the path through the trees alone, so a blob that cannot be fetched (in a blobless clone) is not
    # taken for a missing file: git show fails on it instead.
    if subprocess.run(['git', 'rev-parse', '--verify', '--quiet', f'{rev}:{path}'], capture_output=True).returncode:
        return None
    return git('show', f'{rev}:{path}')


def fields(text):
    if text is None:
        return set()
    return {h['field'] for h in json.loads(text)['hypotheses']}


def listed(label, extra):
    """The names on `label:` lines of the pull request body (outside HTML comments) and in extra."""
    names = set()
    body = HTML_COMMENT.sub('', os.environ.get('PR_BODY') or '')
    for src in (body, f'{label}: {extra}' if extra else ''):
        # a bullet and backticks around the label are allowed: `Removes-rows: a`, `Removes-rows:` a, - Removes-rows: a
        for m in re.finditer(rf'^[ \t]*(?:[-*+][ \t]+)?`?{label}:`?[ \t]*(.*)$', src, re.M):
            names |= {n.strip(' `') for n in re.split(r'[,\s]+', m.group(1)) if n.strip(' `')}
    return names


def rows(base, tree, removes, adds):
    before, after = fields(read_at(base, OPEN)), fields(read_at(tree, OPEN))
    gone, added = before - after, after - before
    unlisted_gone = sorted(gone - listed('Removes-rows', removes))
    unlisted_added = sorted(added - listed('Adds-rows', adds))
    if gone:
        print(f'rows removed from {OPEN}: {", ".join(sorted(gone))}')
    if added:
        print(f'rows added to {OPEN}: {", ".join(sorted(added))}')
    if unlisted_gone:
        print(f'::error file={OPEN}::this change removes board rows that main has and the pull request body does not '
              f'list: {", ".join(unlisted_gone)}. If the removal is intended, add the line "Removes-rows: '
              f'{", ".join(unlisted_gone)}" to the body. If not, merge current main into the branch and regenerate.')
    if unlisted_added:
        print(f'::error file={OPEN}::this change adds board rows that main does not have and the pull request body '
              f'does not list: {", ".join(unlisted_added)}. A branch built on an older main can bring back rows that a '
              f'fold removed: if so, merge current main into the branch and regenerate. A genuine new hypothesis (or '
              f'the new name of a renamed row) is listed by adding the line "Adds-rows: {", ".join(unlisted_added)}" '
              f'to the body.')
    if unlisted_gone or unlisted_added:
        return 1
    print('ok: no unlisted board-row removals or additions')
    return 0


def owners(base, tree):
    text = read_at(base, OWNERS)
    if text is None:
        return 0
    table = []
    for line in text.splitlines():
        if line.strip() and not line.startswith('#') and not line.startswith('path\t'):
            path, owner, *note = line.split('\t')
            table.append((path, owner, note[0] if note else ''))
    # --no-renames: a moved file is listed at its old path too; -z: paths are not quoted
    changed = [f for f in git('diff', '--name-only', '--no-renames', '-z', base, tree or 'HEAD').split('\0') if f]
    seen = {}
    for f in changed:
        hits = [t for t in table if f == t[0] or (t[0].endswith('/') and f.startswith(t[0]))]
        if hits:
            path, owner, note = max(hits, key=lambda t: len(t[0]))
            seen.setdefault(owner, []).append(f)
    for owner, files in sorted(seen.items()):
        print(f'::warning::files owned by {owner} (OWNERS.tsv) change here; tell the owner: {", ".join(files[:10])}'
              + (f' and {len(files) - 10} more' if len(files) > 10 else ''))
    if not seen:
        print('ok: no owned files touched')
    return 0


def render_problems(root):
    """The lines `render_open.py --check` prints in the checkout at root, without its closing ok line, or None if
    that checkout has no render_open.py."""
    if not os.path.exists(os.path.join(root, RENDER)):
        return None
    out = subprocess.run([sys.executable, RENDER, '--check'], cwd=root, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, encoding='utf-8', errors='replace').stdout
    # a traceback names the checkout's own path: drop it, so the same failure reads the same in both checkouts
    out = out.replace(os.path.realpath(root) + os.sep, '')
    return [line for line in out.splitlines() if line.strip() and not line.startswith('ok: ')]


def render(base):
    here = render_problems('.')
    if here is None:
        print(f'ok: no {RENDER} here, so nothing to check')
        return 0
    if not here:
        print('ok: render_open.py --check finds no problems')
        return 0
    tmp = tempfile.mkdtemp(prefix='pr-guard-base-')
    try:
        git('worktree', 'add', '--detach', tmp, base)
        known = render_problems(tmp)
        if known is None:
            print(f'note: {base} has no {RENDER}, so every problem found here is reported')
    except subprocess.CalledProcessError as e:
        print(f'::warning::could not check out {base} to compare with, so every problem found here is reported: '
              + ' '.join(e.stderr.split()))
        known = None
    finally:
        subprocess.run(['git', 'worktree', 'remove', '--force', tmp], capture_output=True)
        shutil.rmtree(tmp, ignore_errors=True)
    known = set(known or ())
    new = [line for line in here if line not in known]
    for line in new:
        print(f'::warning::{line}')
    if not new:
        print(f'ok: every problem render_open.py --check finds here ({len(here)}) is already at {base}')
    return 0


def main():
    args = sys.argv[1:]
    if not args or args[0] not in ('rows', 'owners', 'render'):
        print(__doc__)
        return 2
    opt = {k: v for k, v in zip(args[1::2], args[2::2])}
    base, tree = opt.get('--base', 'HEAD^1'), opt.get('--tree')
    if args[0] == 'render':
        try:
            return render(base)
        except Exception as e:  # warning only: nothing here may fail the check
            print(f'::warning::could not compare render_open.py --check with {base}: {e!r}')
            return 0
    for name, rev in (('--base', base), ('--tree', tree)):
        if rev is not None and not tree_ish(rev):
            print(f'::error::{name} {rev} does not name a commit or tree of this repository, so nothing was checked')
            return 2
    try:
        if args[0] == 'rows':
            return rows(base, tree, opt.get('--removes', ''), opt.get('--adds', ''))
        return owners(base, tree)
    except subprocess.CalledProcessError as e:
        print(f'::error::git {" ".join(e.cmd[1:])} failed, so nothing was checked: {" ".join(e.stderr.split())}')
        return 2


if __name__ == '__main__':
    sys.exit(main())
