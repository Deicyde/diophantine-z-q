"""Pull-request guard: board rows a change removes, and the owners of the files it touches.

Usage (from the repository root):
  python3 scripts/guard/check_pr.py rows --base REV [--tree REV] [--removes "a, b"]
  python3 scripts/guard/check_pr.py owners --base REV [--tree REV]

rows: compares docs/one-proof/open-statements.json at --base (main) with the merged result (--tree, default the
working tree; in a pull_request workflow the checkout is GitHub's merge commit). Every field present at --base and
missing from the result must be listed in the pull request body on a line `Removes-rows: field, field` (read from the
PR_BODY environment variable) or in --removes. Exit 1 otherwise. This catches a branch built on an older main that
would bring back old rows or drop newer ones.

owners: prints a warning for each file the change touches that OWNERS.tsv assigns to an owner, so the owner can be
told. It never fails.
"""
import json, os, re, subprocess, sys

OPEN = 'docs/one-proof/open-statements.json'
OWNERS = 'OWNERS.tsv'


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, check=True).stdout


def read_at(rev, path):
    if rev is None:
        return open(path).read() if os.path.exists(path) else None
    try:
        return git('show', f'{rev}:{path}')
    except subprocess.CalledProcessError:
        return None


def fields(text):
    if text is None:
        return set()
    return {h['field'] for h in json.loads(text)['hypotheses']}


def listed_removals(extra):
    names = set()
    for src in (os.environ.get('PR_BODY', ''), f'Removes-rows: {extra}' if extra else ''):
        for m in re.finditer(r'^\s*Removes-rows:\s*(.+)$', src, re.M):
            names |= {n.strip(' `') for n in re.split(r'[,\s]+', m.group(1)) if n.strip(' `')}
    return names


def rows(base, tree, extra):
    gone = fields(read_at(base, OPEN)) - fields(read_at(tree, OPEN))
    unlisted = sorted(gone - listed_removals(extra))
    if gone:
        print(f'rows removed from {OPEN}: {", ".join(sorted(gone))}')
    if unlisted:
        print(f'::error file={OPEN}::this change removes board rows that main has and the pull request body does not '
              f'list: {", ".join(unlisted)}. If the removal is intended, add the line "Removes-rows: '
              f'{", ".join(unlisted)}" to the body. If not, merge current main into the branch and regenerate.')
        return 1
    print('ok: no unlisted board-row removals')
    return 0


def owners(base, tree):
    if not os.path.exists(OWNERS):
        return 0
    table = []
    for line in open(OWNERS).read().splitlines():
        if line.strip() and not line.startswith('#') and not line.startswith('path\t'):
            path, owner, *note = line.split('\t')
            table.append((path, owner, note[0] if note else ''))
    changed = git('diff', '--name-only', base, tree or 'HEAD').splitlines()
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


def main():
    args = sys.argv[1:]
    if not args or args[0] not in ('rows', 'owners'):
        print(__doc__)
        return 2
    opt = {k: v for k, v in zip(args[1::2], args[2::2])}
    base, tree = opt.get('--base', 'HEAD^1'), opt.get('--tree')
    if args[0] == 'rows':
        return rows(base, tree, opt.get('--removes', ''))
    return owners(base, tree)


if __name__ == '__main__':
    sys.exit(main())
