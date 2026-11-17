"""homfree-noemb: copy Lean declarations verbatim with their scope context (namespace/section/open/variable/...)
and a renaming map. Used to generate the rerouted chain."""
import re

CMD = re.compile(r"^(theorem|lemma|def|abbrev|structure|class|instance|inductive|/--|/-!|/-|@\[|end\b|namespace|section|"
                 r"noncomputable|open|variable|set_option|#|private|protected|attribute|local|universe|example|macro|"
                 r"syntax|notation|scoped|omit|include|export|initialize|elab|run_cmd|mutual)")
CTX = re.compile(r"^(open|variable|set_option|local notation|local infix|local prefix|local postfix|local macro|"
                 r"attribute \[local|universe|omit|include|local instance|local attribute|scoped\[)")
_files = {}

def lines(f):
    if f not in _files:
        _files[f] = open(f).read().split("\n")
    return _files[f]

def comment_mask(L):
    """mask[i] = True if line i starts inside a block comment (so a col-0 token is not a command)."""
    depth = 0
    mask = []
    for l in L:
        mask.append(depth > 0)
        i = 0
        while i < len(l):
            if depth == 0 and l.startswith("--", i):
                break
            if l.startswith("/-", i):
                depth += 1; i += 2; continue
            if depth > 0 and l.startswith("-/", i):
                depth -= 1; i += 2; continue
            if depth == 0 and l[i] == '"':
                j = i + 1
                while j < len(l) and l[j] != '"':
                    j += 2 if l[j] == '\\' else 1
                i = j + 1; continue
            i += 1
    return mask

_masks = {}
def mask(f):
    if f not in _masks:
        _masks[f] = comment_mask(lines(f))
    return _masks[f]

def is_cmd(f, i):
    L = lines(f); m = mask(f)
    return (not m[i]) and bool(CMD.match(L[i]))

def find_decl(f, name, kinds=("theorem", "lemma", "def", "abbrev", "structure", "instance")):
    L = lines(f); m = mask(f)
    pat = re.compile(r"^(@\[[^\]]*\]\s*)?((private|protected|noncomputable) )*(" + "|".join(kinds) + r") " + re.escape(name) + r"(\s|$)")
    hits = [i for i, l in enumerate(L) if not m[i] and pat.match(l)]
    return hits

def decl_extent(f, i):
    """start (with docstring / `open .. in` / attributes) and end (exclusive) of the declaration at line i."""
    L = lines(f); m = mask(f)
    j = i + 1
    while j < len(L) and not (L[j].strip() and not L[j][0].isspace() and is_cmd(f, j)):
        j += 1
    # trim trailing blank lines
    while j > i + 1 and not L[j - 1].strip():
        j -= 1
    s = i
    while s > 0:
        p = L[s - 1]
        if re.match(r"^(open .* in|set_option .* in|@\[.*\])\s*$", p):
            s -= 1; continue
        if p.rstrip().endswith("-/") and not mask(f)[s - 1] or (p.rstrip().endswith("-/") and mask(f)[s - 1]):
            # walk back to the docstring start
            k = s - 1
            while k >= 0 and "/--" not in L[k] and "/-" not in L[k]:
                k -= 1
            if k >= 0 and "/--" in L[k]:
                s = k; continue
            break
        break
    return s, j

def context(f, upto):
    """scope stack before line `upto`: list of (opener, closer, [ctx commands])."""
    L = lines(f); m = mask(f)
    stack = [("", "", [])]
    i = 0
    while i < upto:
        l = L[i]
        if m[i] or not l.strip() or l[0].isspace():
            i += 1; continue
        mm = re.match(r"^namespace (\S+)", l)
        if mm and re.search(r"\bend " + re.escape(mm.group(1)) + r"\s*$", l):
            i += 1; continue  # one-line `namespace X export ... end X` (aliases persist in the environment)
        if mm:
            stack.append((l.rstrip(), "end " + mm.group(1), [])); i += 1; continue
        mm = re.match(r"^(noncomputable )?section\s*(\S*)", l)
        if mm:
            stack.append((l.rstrip(), ("end " + mm.group(2)).rstrip(), [])); i += 1; continue
        if re.match(r"^end\b", l):
            if len(stack) > 1:
                stack.pop()
            i += 1; continue
        if CTX.match(l) and not re.search(r"\bin\s*$", l):
            # collect continuation lines (indented)
            cmd = [l]
            k = i + 1
            while k < upto and L[k].strip() and L[k][0].isspace():
                cmd.append(L[k]); k += 1
            stack[-1][2].append("\n".join(cmd))
            i = k; continue
        i += 1
    return stack

def rename(text, ren):
    """ren: dict short_name -> new_short_name (identifier-boundary aware; primes are identifier chars)."""
    if not ren:
        return text
    keys = sorted(ren, key=len, reverse=True)
    pat = re.compile(r"(?<![\w'!?₀-₉])(" + "|".join(re.escape(k) for k in keys) + r")(?![\w'!?₀-₉])")
    return pat.sub(lambda mo: ren[mo.group(1)], text)

def emit(f, name, ren, edits=(), kinds=None, which=0):
    hits = find_decl(f, name) if kinds is None else find_decl(f, name, kinds)
    if not hits:
        raise SystemExit(f"not found: {name} in {f}")
    i = hits[which]
    s, e = decl_extent(f, i)
    body = "\n".join(lines(f)[s:e])
    body = rename(body, ren)
    for a, b in edits:
        if a not in body:
            raise SystemExit(f"edit not applicable in {name}: {a!r}")
        body = body.replace(a, b)
    st = context(f, s)
    out = [f"-- copied from {f}:{i+1} ({name})"]
    out.extend(st[0][2])
    for op, cl, cmds in st[1:]:
        out.append(op)
        out.extend(cmds)
    out.append(body)
    for op, cl, cmds in reversed(st[1:]):
        out.append(cl)
    return "\n".join(out) + "\n"
