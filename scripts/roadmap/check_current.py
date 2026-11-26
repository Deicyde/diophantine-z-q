#!/usr/bin/env python3
"""Check that the roadmap (blueprint/roadmap/) agrees with the Lean and the records in this checkout.

Three checks, each read-only unless --fix is given:

1. Every name in a page's `lean:` frontmatter is a declaration or a structure field in a Lean file of the repository.
   Pages that say their Lean is kept only at the tag `route-k-final` are skipped.
2. The height-decomposition chapter is what scripts/one_proof/vault_chapter/gen.py writes from the current
   Lean and docs/one-proof/ records. The generator runs on a scratch copy; --fix runs it on this checkout.
3. Every `RCLeaves.x`, `PreLeaves.x` or `PostLeaves.x` in a page names a field of that structure or a theorem
   `RCLeaves.x` (the fields of Theorem 5.3's remaining hypotheses, in RC/Wiring/Leaves.lean).

Exit status 1 when any check finds drift. Usage: python3 scripts/roadmap/check_current.py [--fix]
"""
import filecmp
import glob
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '..', '..'))
ROADMAP = os.path.join(ROOT, 'blueprint', 'roadmap')
KEYWORDS = 'theorem|lemma|def|abbrev|structure|class|inductive|instance|axiom|opaque'
ROUTE_K_ONLY = ("not on this fork's main", 'Partly removed from the Lean development')


def git_grep(pattern):
    out = subprocess.run(['git', 'grep', '-h', '-E', pattern, '--', '*.lean'],
                         cwd=ROOT, capture_output=True, text=True)
    return out.stdout.splitlines()


def frontmatter(text):
    m = re.match(r'---\n(.*?)\n---', text, re.S)
    return m.group(1) if m else ''


def pages():
    for path in sorted(glob.glob(os.path.join(ROADMAP, '**', '*.md'), recursive=True)):
        with open(path, encoding='utf-8') as f:
            yield os.path.relpath(path, ROOT), f.read()


def check_lean_names():
    decls = set()
    for line in git_grep(rf'({KEYWORDS})[[:space:]]+[^[:space:]]+'):
        m = re.search(rf'\b({KEYWORDS})\s+([^\s(:{{]+)', line)
        if m:
            decls.add(m.group(2).split('.')[-1])
    fields = {m.group(1) for line in git_grep(r'^[[:space:]]+[A-Za-z_][A-Za-z0-9_\x27]*[[:space:]]*:')
              if (m := re.match(r"\s+([A-Za-z_][\w']*)\s*:", line))}
    bad, checked = [], 0
    for path, text in pages():
        lm = re.search(r'^lean:(.*?)(?=^\w+:|\Z)', frontmatter(text), re.M | re.S)
        if not lm or any(marker in text for marker in ROUTE_K_ONLY):
            continue
        for name in re.split(r'[,\s]+', lm.group(1).strip()):
            if not name:
                continue
            checked += 1
            short = name.split('.')[-1]
            if short not in decls and short not in fields:
                bad.append(f'{path}: lean name {name} is not declared in any Lean file')
    return checked, bad


def check_generated_chapter(fix):
    gen = os.path.join('scripts', 'one_proof', 'vault_chapter', 'gen.py')
    if fix:
        subprocess.run([sys.executable, gen, ROOT], cwd=ROOT, check=True)
        return []
    with tempfile.TemporaryDirectory() as scratch:
        for part in ('ZInQKernel/OneProof', 'docs/one-proof', 'blueprint', 'scripts/one_proof/vault_chapter'):
            shutil.copytree(os.path.join(ROOT, part), os.path.join(scratch, part))
        subprocess.run([sys.executable, '-I', os.path.join(scratch, gen), scratch], cwd=scratch, check=True,
                       capture_output=True, text=True)
        bad = []

        def walk(cmp, rel):
            for name in cmp.diff_files + cmp.left_only + cmp.right_only:
                bad.append(f'blueprint/{rel}{name}: differs from what gen.py writes (run with --fix)')
            for name, sub in cmp.subdirs.items():
                walk(sub, f'{rel}{name}/')
        walk(filecmp.dircmp(os.path.join(scratch, 'blueprint'), os.path.join(ROOT, 'blueprint'),
                            ignore=['.DS_Store']), '')
        return bad


def check_leaf_fields():
    paths = [line.split(':', 1)[0] for line in subprocess.run(
        ['git', 'grep', '-l', '-E', '^structure RCLeaves', '--', '*.lean'],
        cwd=ROOT, capture_output=True, text=True).stdout.splitlines()]
    if not paths:
        return ['RC/Wiring/Leaves.lean: no structure RCLeaves found']
    src = ''
    for path in paths:
        with open(os.path.join(ROOT, path), encoding='utf-8') as f:
            src += f.read() + '\n'
    known = {}
    for struct in ('PreLeaves', 'PostLeaves', 'RCLeaves'):
        end = r'(?=^(?:/--|theorem|lemma|def|structure|end\b|namespace|section|noncomputable|abbrev|instance|@\[)|\Z)'
        known[struct] = set()
        for m in re.finditer(rf'^structure {struct}\b.*?where\n(.*?){end}', src, re.S | re.M):
            known[struct] |= set(re.findall(r"^  ([A-Za-z_][\w']*)\s*:", m.group(1), re.M))
        known[struct] |= set(re.findall(rf"^theorem {struct}\.([A-Za-z_][\w']*)", src, re.M))
    bad = []
    for path, text in pages():
        for struct, field in sorted(set(re.findall(r'\b(PreLeaves|PostLeaves|RCLeaves)\.([A-Za-z_]\w*)', text))):
            if field not in known[struct]:
                bad.append(f'{path}: {struct}.{field} is neither a field nor a theorem of {struct}')
    return bad


def main():
    fix = '--fix' in sys.argv[1:]
    checked, names = check_lean_names()
    chapter = check_generated_chapter(fix)
    leaves = check_leaf_fields()
    print(f'lean names: {checked} checked, {len(names)} unresolved')
    print(f'height-decomposition chapter: {"regenerated" if fix else f"{len(chapter)} files differ"}')
    print(f'leaf-field references: {len(leaves)} unknown')
    for found in (names, chapter, leaves):
        for line in found[:25]:
            print('  ' + line)
        if len(found) > 25:
            print(f'  ... and {len(found) - 25} more')
    return 1 if names or chapter or leaves else 0


if __name__ == '__main__':
    sys.exit(main())
