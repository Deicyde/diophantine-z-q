"""cm-branch2: source-context extraction for copying Lean declarations.

context(path, line) returns the namespace path and the context commands (open / variable / set_option /
attribute [local ...] / universe / local notation) active at `line` (1-based) of the file, by scanning top-level
commands (column 0). `block(path, start, end)` returns the declaration text (lines start..end, inclusive), extended
upward over a preceding `open ... in` / `set_option ... in` line and a docstring/attribute run that the declaration
range may not include.
"""
import re

_cache = {}

def lines_of(path):
    if path not in _cache:
        _cache[path] = open(path).read().split('\n')
    return _cache[path]

SCOPE_RE = re.compile(r'^(noncomputable\s+)?section\b\s*(\S*)\s*$')
NS_RE = re.compile(r'^namespace\s+(\S+)\s*$')
END_RE = re.compile(r'^end\b\s*(\S*)\s*$')
OPEN_RE = re.compile(r'^open\b')
CTX_RE = re.compile(r'^(variable\b|include\b|omit\b|set_option\b(?!.*\bin\s*$)|attribute\s*\[local|universe\b|local\s+notation|noncomputable\s*$)')


def context(path, line):
    L = lines_of(path)
    # stack of scopes: (kind, name, [ctx commands])
    stack = [('root', '', [])]
    i = 0
    n = min(line - 1, len(L))
    depth = 0
    while i < n:
        s = L[i]
        if depth > 0 or s.startswith('/-') or s.startswith('--'):
            # comment tracking (block comments may nest)
            if s.startswith('--') and depth == 0:
                i += 1; continue
            d0 = depth
            depth += s.count('/-') - s.count('-/')
            if depth < 0: depth = 0
            i += 1; continue
        if s.startswith('namespace '):
            m = NS_RE.match(s)
            if m:
                # `namespace A.B` opens two scopes; record as one with the dotted name
                stack.append(('ns', m.group(1), []))
            i += 1; continue
        m = SCOPE_RE.match(s)
        if m:
            stack.append(('sec', m.group(2), []))
            i += 1; continue
        m = END_RE.match(s)
        if m:
            if len(stack) > 1:
                stack.pop()
            i += 1; continue
        if (OPEN_RE.match(s) and not re.search(r'\bin\s*$', s)) or CTX_RE.match(s):
            # take continuation lines (indented)
            cmd = [s]
            j = i + 1
            while j < n and L[j].startswith(' ') and L[j].strip():
                cmd.append(L[j]); j += 1
            if not s.startswith('export'):
                stack[-1][2].append('\n'.join(cmd))
            i = j; continue
        i += 1
    ns = '.'.join(x[1] for x in stack if x[0] == 'ns')
    ctx = []
    for x in stack:
        ctx.extend(x[2])
    return ns, ctx


def block(path, start, end):
    L = lines_of(path)
    s = start - 1
    # extend over doc comment / attributes directly above (declaration ranges usually include them)
    while s > 0 and (L[s - 1].startswith('@[') or re.match(r'^(open|set_option)\b.*\bin\s*$', L[s - 1])):
        s -= 1
    return '\n'.join(L[s:end])
