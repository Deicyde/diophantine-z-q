#!/usr/bin/env python3
"""Backport supplement generator (task selmer-2infty).

Usage: bp_supplement.py <latest-module-path> <vendored-5a01-module-path-or-NONE> <out-path> [--keep name,...]

Reads the Tau Ceti main (commit 0642eae2) version of a module, removes every top-level declaration whose
name is declared in the vendored commit-5a01f5fe version (so only declarations that version lacks remain),
rewrites `TauCeti.` imports through the mapping file, adds an import of the vendored version, and writes the
result with the provenance header. With NONE, the whole module is copied (a module new since 5a01f5fe).
"""
import json, os, re, sys

L = os.environ['TAUCETI_MAIN']  # a checkout of Tau Ceti at commit 0642eae29e0a59ef798d04de325386445906e755
Z = os.environ.get('REPO', '.')  # this repository
COMMIT = '0642eae29e0a'
MAP = json.load(open(os.environ.get('BP_IMPORTMAP', 'importmap.json')))  # latest module name -> target module name

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|irreducible_def|opaque|alias)\s+([^\s:(\[{]+)?")
TOP = re.compile(r"^(/--|/-!|@\[|theorem |lemma |def |abbrev |instance |structure |class |inductive |"
                 r"private |protected |noncomputable |nonrec |irreducible_def |opaque |alias |section|end|"
                 r"namespace |variable|open |omit |include |set_option |attribute |universe |#|example |"
                 r"local |scoped |deriving |mutual|export |suppress_compilation|public section|public |meta )")


def _depth_delta(l):
    """Net change of block-comment nesting along a line (ignores string literals; adequate for Mathlib-style
    sources)."""
    d, i = 0, 0
    # strip line comments that are not inside a block comment start
    while i < len(l) - 1:
        two = l[i:i + 2]
        if two == '/-':
            d += 1
            i += 2
            continue
        if two == '-/':
            d -= 1
            i += 2
            continue
        if two == '--' and d <= 0:
            break
        i += 1
    return d


def chunks(lines):
    """Split into top-level chunks: a chunk starts at a line matching TOP at column 0, outside comments."""
    out, cur = [], []
    depth = 0
    for l in lines:
        if depth == 0 and TOP.match(l) and cur:
            # a doc comment / attribute line glues to the following declaration
            out.append(cur)
            cur = [l]
        else:
            cur.append(l)
        depth = max(0, depth + _depth_delta(l))
    if cur:
        out.append(cur)
    # merge doc-comment/attribute chunks into the next chunk
    merged, pend = [], []
    for c in out:
        head = c[0]
        joined = '\n'.join(c).rstrip()
        is_in_prefix = bool(re.match(r'^(omit|include|variable|open|set_option|local|attribute)\b', head)) and \
            bool(re.search(r'\bin$', joined))
        if is_in_prefix or ((head.startswith('/--') or (head.startswith('@[') and not DECL.match(' '.join(c)))) and
                            not head.startswith('/-!')):
            # a doc comment chunk: check it ends with -/ and holds no declaration
            pend += c
            continue
        merged.append(pend + c)
        pend = []
    if pend:
        merged.append(pend)
    return merged


def decl_name(chunk):
    txt = '\n'.join(chunk)
    # skip `... in` prefix commands and doc comments, in any order
    body = txt
    while True:
        b2 = re.sub(r"^/--.*?-/\s*", "", body, count=1, flags=re.S)
        b2 = re.sub(r"^(omit|include|variable|open|set_option|local|attribute)\b[^\n]*?\bin\s*\n", "", b2,
                    count=1)
        b2 = re.sub(r"^--[^\n]*\n", "", b2, count=1)
        if b2 == body:
            break
        body = b2
    m = DECL.match(body)
    if not m:
        return None
    if m.group(1) == 'instance' and (m.group(2) is None or m.group(2).startswith(':') or m.group(2) == ':'):
        # anonymous instance: key on its normalized header
        hdr = re.split(r':=|\bwhere\b', body, maxsplit=1)[0]
        hdr = re.sub(r"^(?:@\[[^\]]*\]\s*)*", "", hdr)
        return 'instance:' + ' '.join(hdr.split())
    return m.group(2)


def is_private_chunk(c):
    body = '\n'.join(c)
    while True:
        b2 = re.sub(r"^/--.*?-/\s*", "", body, count=1, flags=re.S)
        b2 = re.sub(r"^(omit|include|variable|open|set_option|local|attribute)\b[^\n]*?\bin\s*\n", "", b2,
                    count=1)
        b2 = re.sub(r"^--[^\n]*\n", "", b2, count=1)
        if b2 == body:
            break
        body = b2
    return bool(re.match(r"^(?:@\[[^\]]*\]\s*)*private\s", body))


def names_of(path):
    """Names declared (non-private: private names are not visible to other modules) in a module."""
    s = open(path, encoding='utf-8').read()
    return set(n for n, c in ((decl_name(c), c) for c in chunks(s.split('\n'))) if n and not is_private_chunk(c))


def main():
    lat, old, out = sys.argv[1], sys.argv[2], sys.argv[3]
    keep = set()
    if len(sys.argv) > 5 and sys.argv[4] == '--keep':
        keep = set(sys.argv[5].split(','))
    src = open(os.path.join(L, lat), encoding='utf-8').read()
    lines = src.split('\n')
    end = next(i for i, l in enumerate(lines) if l.strip() == '-/')
    header, rest = lines[:end + 1], lines[end + 1:]
    mod = lat[:-5].replace('/', '.')
    removed = []
    olds = [] if old == 'NONE' else old.split(',')
    if olds:
        oldnames = set()
        for o in olds:
            oldnames |= names_of(os.path.join(Z, o))
        cs = chunks(rest)
        kept = []
        for c in cs:
            n = decl_name(c)
            # a private latest declaration is kept (file-local), unless the old module declares the same
            # name publicly, in which case the old public one serves
            if n and n in oldnames and n not in keep:
                removed.append(n)
                continue
            kept.append(c)
        rest = [l for c in kept for l in c]
        note = ['-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit %s, module' % COMMIT,
                '-- %s), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which' % mod,
                '-- is vendored as `%s` (task selmer-2infty).' % ', '.join(o[:-5].replace('/', '.') for o in olds),
                '-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.']
    else:
        note = ['-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit %s, module' % COMMIT,
                '-- %s), Apache-2.0: the whole module (task selmer-2infty), placed under Backport/.' % mod,
                '-- Modified for the Z-in-Q kernel: imports rewritten to the vendored and Backport/ modules.']
    newrest = []
    added_old_import = False
    for l in rest:
        m = re.match(r'^(\s*(?:public\s+)?(?:meta\s+)?import\s+)(TauCeti\.[\w.]+)(.*)$', l)
        if m:
            tgt = MAP.get(m.group(2))
            if tgt is None:
                tgt = 'ZInQKernel.Contrib.' + m.group(2)
            l = m.group(1) + tgt + m.group(3)
        if olds and not added_old_import and re.match(r'^\s*(public\s+)?import\s', l):
            for o in olds:
                newrest.append('public import ' + o[:-5].replace('/', '.'))
            added_old_import = True
        newrest.append(l)
    # dedupe imports
    seen, final = set(), []
    for l in newrest:
        if re.match(r'^\s*(public\s+)?(meta\s+)?import\s', l):
            key = l.strip()
            if key in seen:
                continue
            seen.add(key)
        final.append(l)
    os.makedirs(os.path.dirname(os.path.join(Z, out)), exist_ok=True)
    if os.path.exists(os.path.join(Z, out)) and '--force' not in sys.argv:
        raise SystemExit('refusing to overwrite ' + out)
    open(os.path.join(Z, out), 'w', encoding='utf-8').write('\n'.join(header + note + final))
    print('wrote', out, 'removed', len(removed), 'declarations:', removed[:80])


main()
