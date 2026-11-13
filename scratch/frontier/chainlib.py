"""chainlib: read Lean declarations at a git revision and check the hypotheses of a chain.

Used by scratch/frontier/chain.py. Read-only: every file is read with `git show REV:PATH`.
No Lean is run; the checks are textual (signatures and def bodies as written in the source).
"""
import re
import subprocess
import functools

ROOT = "/home/jackmccarthy/dzq-wt/frontier"


@functools.lru_cache(maxsize=None)
def show(rev, path):
    r = subprocess.run(["git", "-C", ROOT, "show", f"{rev}:{path}"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise FileNotFoundError(f"{rev}:{path}: {r.stderr.strip()}")
    return r.stdout


TOP_KW = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec )*"
                    r"(theorem|lemma|def|abbrev|structure|class|instance|opaque|axiom|example|"
                    r"namespace|end|section|open|variable|#print|#check|/--|/-!|attribute|set_option|"
                    r"universe|local|scoped|irreducible_def|inductive)\b")


def _decl_block(text, kind_re, short):
    """Return the text of the declaration `kind short` (signature + body up to the next
    top-level command), or None."""
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(?:%s)\s+%s(?=[\s:({\[]|$)"
                     % (kind_re, re.escape(short)), re.M)
    m = None
    for m0 in pat.finditer(text):
        m = m0
        break
    if m is None:
        return None
    start = m.start()
    lines = text[start:].split("\n")
    out = [lines[0]]
    for ln in lines[1:]:
        if ln and not ln[0].isspace() and TOP_KW.match(ln):
            break
        out.append(ln)
    return "\n".join(out)


def strip_comments(s):
    s = re.sub(r"/-.*?-/", " ", s, flags=re.S)
    s = re.sub(r"--[^\n]*", " ", s)
    return s


def signature(text, short, kind_re="theorem|lemma|def|abbrev"):
    """Signature (between the name and the top-level `:=` / `where`) of a declaration."""
    blk = _decl_block(text, kind_re, short)
    if blk is None:
        return None
    blk = strip_comments(blk)
    # cut at the first ':=' or ' where' at bracket depth 0
    depth = 0
    i = 0
    n = len(blk)
    while i < n:
        c = blk[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and blk.startswith(":=", i):
            return blk[:i]
        elif depth == 0 and re.match(r"\swhere\b", blk[i:i + 7] or ""):
            return blk[:i]
        i += 1
    return blk


def split_binders(sig, short):
    """Return (explicit binder types, conclusion) of a signature. Arrow antecedents in the
    conclusion are returned as further hypotheses."""
    s = sig.split(short, 1)[1]
    hyps = []
    i = 0
    n = len(s)
    # leading binders
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        c = s[i]
        if c in "([{⦃":
            close = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}[c]
            depth = 0
            j = i
            while j < n:
                if s[j] in "([{⦃⟨":
                    depth += 1
                elif s[j] in ")]}⦄⟩":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            inner = s[i + 1:j]
            if c == "(" and ":" in inner:
                names, ty = inner.split(":", 1)
                for _ in names.split():
                    hyps.append(ty.strip())
            i = j + 1
        elif c == ":":
            i += 1
            break
        else:
            break
    concl = s[i:].strip()
    # arrow antecedents at depth 0 (only if the conclusion is not a ∀ / ∃ at top)
    parts = []
    depth = 0
    cur = ""
    for ch in concl:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "→" and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    if len(parts) > 1 and not re.match(r"\s*(∀|∃|Π|fun)", concl):
        hyps += [p.strip() for p in parts[:-1]]
        concl = parts[-1].strip()
    return hyps, concl


def head(ty):
    """Head constant of a binder type (`ZInQ.X a b` -> `ZInQ.X`)."""
    ty = ty.strip()
    ty = re.sub(r"^@", "", ty)
    m = re.match(r"[\w.'₀-₉αβγδεζηθικλμνξοπρστυφχψω]+", ty)
    return m.group(0) if m else ty


def short_of(name):
    return name.split(".")[-1]


def same_const(a, b):
    """`a` and `b` name the same constant up to namespace qualification (one is a suffix of
    the other at a `.` boundary)."""
    a = a.lstrip("_root_.")
    b = b.lstrip("_root_.")
    return a == b or a.endswith("." + b) or b.endswith("." + a)


def structure_fields(text, short):
    blk = _decl_block(text, "structure", short)
    if blk is None:
        return None
    blk = strip_comments(blk)
    body = blk.split(" where", 1)[1] if " where" in blk else blk
    fields = []
    cur = None
    for ln in body.split("\n"):
        m = re.match(r"^\s{1,8}(\w[\w']*)\s*:\s*(.*)$", ln)
        if m and not ln.strip().startswith("|"):
            if cur:
                fields.append(cur)
            cur = [m.group(1), m.group(2)]
        elif cur and ln.strip():
            cur[1] += " " + ln.strip()
    if cur:
        fields.append(cur)
    return [(f, " ".join(t.split())) for f, t in fields]


def def_text(text, short):
    blk = _decl_block(text, "def|abbrev|structure|opaque|irreducible_def", short)
    if blk is None:
        return None
    blk = strip_comments(blk)
    return " ".join(blk.split())
