"""Comment/string-aware lexer for Lean 4 source (offline analysis tool, W13 normalization).

Written for this task; it executes nothing.  Character classes follow
Init/Meta/Defs.lean of leanprover/lean4 v4.35.0 (isIdFirst / isIdRest / isLetterLike /
isSubScriptAlnum) and the token dispatch of Lean.Parser.tokenFn (string, char, number,
name literal, raw string, identifier with dotted parts and «» escapes, otherwise symbol).

Tokens are tuples (kind, start, end) over the source string, with kinds
  'ws', 'comment', 'doc' (doc / module-doc comment), 'str', 'char', 'num', 'name' (`x),
  'ident', 'sym'.
Every character of the source belongs to exactly one token, so ''.join(...) round-trips.
"""
import re

def is_letter_like(o):
    return ((0x3b1 <= o <= 0x3c9 and o != 0x3bb) or
            (0x391 <= o <= 0x3a9 and o != 0x3a0 and o != 0x3a3) or
            (0x3ca <= o <= 0x3fb) or (0x1f00 <= o <= 0x1ffe) or
            (0x2100 <= o <= 0x214f) or (0x1d49c <= o <= 0x1d59f) or
            (0xc0 <= o <= 0xff and o != 0xd7 and o != 0xf7) or (0x100 <= o <= 0x17f))

def is_subscript_alnum(o):
    return (0x2080 <= o <= 0x2089) or (0x2090 <= o <= 0x209c) or (0x1d62 <= o <= 0x1d6a) or o == 0x2c7c

def is_id_first(c):
    o = ord(c)
    return ('a' <= c <= 'z') or ('A' <= c <= 'Z') or c == '_' or is_letter_like(o)

def is_id_rest(c):
    o = ord(c)
    return (('a' <= c <= 'z') or ('A' <= c <= 'Z') or ('0' <= c <= '9') or c in "_'!?"
            or is_letter_like(o) or is_subscript_alnum(o))

def _cls(pred, lo=0, hi=0x1FFFF):
    # build a regex character class for a predicate over code points
    ranges = []
    start = None
    for o in range(lo, hi + 1):
        if 0xD800 <= o <= 0xDFFF:
            ok = False
        else:
            ok = pred(chr(o))
        if ok and start is None:
            start = o
        elif not ok and start is not None:
            ranges.append((start, o - 1)); start = None
    if start is not None:
        ranges.append((start, hi))
    parts = []
    for a, b in ranges:
        if a == b:
            parts.append(re.escape(chr(a)))
        else:
            parts.append(re.escape(chr(a)) + '-' + re.escape(chr(b)))
    return '[' + ''.join(parts) + ']'

IDFIRST = _cls(is_id_first)
IDREST = _cls(is_id_rest)
ID_PART = '(?:«[^»]*»|' + IDFIRST + IDREST + '*)'
# an identifier: parts separated by '.', where '.' must be followed by an id start or «
IDENT_RE = re.compile(ID_PART + r'(?:\.' + ID_PART + ')*')
WS_RE = re.compile(r'[ \t\r\n]+')
NUM_RE = re.compile(r'0[xX][0-9a-fA-F_]+|0[bB][01_]+|0[oO][0-7_]+|[0-9][0-9_]*(?:\.[0-9]+)?(?:[eE][+-]?[0-9]+)?')
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'])'", re.S)


class LexError(Exception):
    pass


def _block_comment_end(src, i):
    """src[i:i+2] == '/-'; return index after the matching '-/' (nested)."""
    depth = 1
    j = i + 2
    n = len(src)
    while depth > 0:
        a = src.find('/-', j)
        b = src.find('-/', j)
        if b < 0:
            raise LexError('unterminated block comment at %d' % i)
        if 0 <= a < b:
            depth += 1
            j = a + 2
        else:
            depth -= 1
            j = b + 2
    return j


def _string_end(src, i, interpolated=False):
    """src[i] == '"'; return index after closing quote."""
    j = i + 1
    n = len(src)
    depth = 0
    while j < n:
        c = src[j]
        if c == '\\':
            j += 2
            continue
        if interpolated and c == '{':
            # nested term inside an interpolated string; skip balanced braces, strings
            k = j + 1
            d = 1
            while k < n and d > 0:
                ck = src[k]
                if ck == '"':
                    k = _string_end(src, k)
                    continue
                if ck == '{':
                    d += 1
                elif ck == '}':
                    d -= 1
                k += 1
            j = k
            continue
        if c == '"':
            return j + 1
        j += 1
    raise LexError('unterminated string at %d' % i)


def lex(src):
    toks = []
    i = 0
    n = len(src)
    append = toks.append
    while i < n:
        c = src[i]
        if c in ' \t\r\n':
            m = WS_RE.match(src, i)
            append(('ws', i, m.end())); i = m.end(); continue
        if c == '-' and src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            append(('comment', i, j)); i = j; continue
        if c == '/' and src.startswith('/-', i):
            j = _block_comment_end(src, i)
            kind = 'doc' if (src.startswith('/--', i) and not src.startswith('/--/', i)) else ('moddoc' if src.startswith('/-!', i) else 'comment')
            append((kind, i, j)); i = j; continue
        if c == '"':
            prev = toks[-1] if toks else None
            interp = False
            if prev and prev[0] == 'ident' and src[prev[1]:prev[2]] in ('s!', 'm!', 'f!', 'throwError', 'logInfo', 'logWarning', 'trace[', 'dbg_trace'):
                interp = True
            j = _string_end(src, i, interp)
            append(('str', i, j)); i = j; continue
        if c == "'" and (i + 1 < n and src[i + 1] != "'"):
            m = CHAR_RE.match(src, i)
            if m:
                append(('char', i, m.end())); i = m.end(); continue
            append(('sym', i, i + 1)); i += 1; continue
        if '0' <= c <= '9':
            m = NUM_RE.match(src, i)
            append(('num', i, m.end())); i = m.end(); continue
        if c == '`' and i + 1 < n and (is_id_first(src[i + 1]) or src[i + 1] == '«'):
            m = IDENT_RE.match(src, i + 1)
            append(('name', i, m.end())); i = m.end(); continue
        if c == 'r' and i + 1 < n and (src[i + 1] == '"' or (src[i + 1] == '#' and re.match(r'#+"', src[i + 1:i + 40] or ''))):
            m = re.match(r'r(#*)"', src[i:i + 60])
            if m:
                hashes = m.group(1)
                close = '"' + hashes
                j = src.find(close, i + len(m.group(0)))
                if j < 0:
                    raise LexError('unterminated raw string at %d' % i)
                append(('str', i, j + len(close))); i = j + len(close); continue
        if is_id_first(c) or c == '«':
            m = IDENT_RE.match(src, i)
            if m and m.end() > i:
                append(('ident', i, m.end())); i = m.end(); continue
        append(('sym', i, i + 1)); i += 1
    return toks


def code_tokens(toks):
    """tokens that are not whitespace/comments"""
    return [t for t in toks if t[0] not in ('ws', 'comment', 'doc', 'moddoc')]


def line_starts(src):
    ls = [0]
    for m in re.finditer('\n', src):
        ls.append(m.end())
    return ls


def strip_comments(src, toks=None, keep_newlines=True):
    """Return the source with comments (and doc comments) blanked, preserving offsets."""
    if toks is None:
        toks = lex(src)
    out = []
    for k, a, b in toks:
        seg = src[a:b]
        if k in ('comment', 'doc', 'moddoc'):
            out.append(''.join(ch if ch == '\n' else ' ' for ch in seg))
        else:
            out.append(seg)
    return ''.join(out)


if __name__ == '__main__':
    import sys
    for p in sys.argv[1:]:
        s = open(p, encoding='utf-8').read()
        t = lex(s)
        assert ''.join(s[a:b] for _, a, b in t) == s
        print(p, len(t))
