"""Generate the scratch bypass from the base declarations and the Lean dependency census.
Scope extraction is adapted from scratch/fold-b116/gen-d2a6b/copylib.py."""
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

from collections import defaultdict
from pathlib import Path

SCRATCH = Path(__file__).parent
MERGE = "_root_.DeRhamScholze.HTMerge."
G9 = "_root_.HDec.ZInQ.Contrib.G9."
OLD_TOP = "HDec.HSyn.sixContactMin_of_open82"
NEW_TOP = "HDec.HSyn.sixContactMin_of_open83"

# References redirected to proofs of the same instance at g = 2.
replace_tokens = {
    "_root_.DeRhamScholze.HTMerge.ScholzeH1AbVar": MERGE + "ScholzeH1Narrow",
    "_root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar": MERGE + "HodgeTateDecompAbSurf",
    "_root_.DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1":
        MERGE + "hodgeTateDecompAbSurf_of_narrow",
    "_root_.ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT":
        MERGE + "r10Surface_of_leaves",
    "HodgeLF7.r10": "HodgeLF7.r10Surface",
    "_root_.HDec.PkgI4.DeRhamComparisonHT": "_root_.HDec.PkgI4.R10Surface",
    "_root_.HDec.PkgI4.DeRhamComparison": "_root_.HDec.PkgI4.R10Surface",
    "HDec.PkgI4.DeRhamComparisonHT": "_root_.HDec.PkgI4.R10Surface",
    "HDec.PkgI4.DeRhamComparison": "_root_.HDec.PkgI4.R10Surface",
    "PkgI4.DeRhamComparisonHT": "_root_.HDec.PkgI4.R10Surface",
    "PkgI4.DeRhamComparison": "_root_.HDec.PkgI4.R10Surface",
    "HodgeTateDecompAbVar": MERGE + "HodgeTateDecompAbSurf",
    "hodgeTateDecompAbVar": "hodgeTateDecompAbSurf",
    "G9GlueNoT23": "G9GlueFromSurfaces",
    "scholzeH1AbVar": "scholzeH1Narrow",
    "OpenAddedLeaves28": "OpenAddedLeaves29",
    "c8Leaves_of_OpenAddedLeaves28": "c8Leaves_of_OpenAddedLeaves29",
    "sixContactMin_of_open82": "sixContactMin_of_open83",
}

# Dropped internal slots have no downstream projection in the live chain.
def edits(name, body):
    if name.endswith(("OpenResearchLeaves60_y3x6", "OpenResearchLeaves59_y3x6",
                      "OpenResearchLeaves54SFU_y3x6")):
        body = edit_once(body, r"^  hodgeTateDecompOr : .*\n")
    if name.endswith(("openResearchLeaves60_y3x6_of_OpenResearchLeaves63",
                      "openResearchLeaves59_y3x6_of_60_y3x6", "openResearchLeaves54SFU_y3x6_of_59_y3x6")):
        body = edit_once(body, r"^  hodgeTateDecompOr := .*\n")
    if name.endswith("OpenResearchLeaves36EBCFSFU_y3x6"):
        body = edit_once(body, r"^  hodgeTateDecompExists : .*\n")
    if name.endswith("openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6"):
        body = edit_once(body, r"^  hodgeTateDecompExists := .*\n")
    if name == "HDec.G0Galois.GaloisPiecesC8":
        body = edit_once(body, r"^  deRham : G9Glue\n")
    if "g9GlueNoT23_of_deRhamComparisonHT r.r10" in body:
        body = edit_once(body, r"^          g9Glue_of_deRhamComparisonHT r\.r10,\n")
        body = edit_once(body, r"\(g9GlueNoT23_of_deRhamComparisonHT r\.r10\)", G9 + "g9GlueFromSurfaces")
    if "PkgI4.deRhamComparison_of_HT" in body:
        body = edit_once(body, r"PkgI4\.deRhamComparison_of_HT r\.r10", "r.r10")
    # Field/dictionary selectors can be imported from a slightly different enclosing open.
    return body

def edit_once(body, pattern, repl=""):
    body, n = re.subn(pattern, repl, body, flags=re.M)
    assert n == 1, (pattern, n)
    return body

def strip_comments(body):
    # Strip source comments and docstrings, retaining source locators on each copy.
    body = re.sub(r"/-.*?-/", "", body, flags=re.S)
    body = re.sub(r"^\s*--[^\n]*\n", "", body, flags=re.M)
    return re.sub(r"\n\s*\n+", "\n", body).strip()

def locate(mod, full):
    file = mod.replace(".", "/") + ".lean"
    if not Path(file).is_file():
        return
    basename = full.split(".")[-1]
    for spelling in dict.fromkeys(("_root_." + full, basename)):
        hits = find_decl(file, spelling)
        if len(hits) > 1:
            raise ValueError((file, full, hits))
        if hits:
            return file, spelling, hits[0]

def proof_part():
    raw = {}
    for s in (SCRATCH / "census-output.txt").read_text().splitlines():
        if s.startswith("COPY\t"):
            _, mod, full, *rest = s.split("\t", 3)
            deps = rest[0] if rest else ""
            raw[full] = (mod, deps.split())
    assert OLD_TOP in raw
    # These are either existing retained definitions or explicit replacements in ScholzeNarrow.
    skip = {
        "HDec.PkgI4.DeRhamComparison", "HDec.PkgI4.DeRhamComparisonHT",
        "PkgI4.DeRhamComparison", "PkgI4.DeRhamComparisonHT",
        "HDec.PkgI4.deRhamComparisonHT_iff", "HDec.PkgI4.r10Weights_of_HT",
        "HDec.G0Galois.G9Glue", "HDec.G0Galois.G9GlueNoT23",
        "ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar",
        "ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leaves",
    }
    skip |= {c for c in raw if c.startswith("HDec.ZInQ.Contrib.G9.g9Glue")}
    skip |= {c for c in raw if any(c.startswith(d + ".") for d in skip)}
    located = {}
    for full, (mod, _) in raw.items():
        if full in skip:
            continue
        found = locate(mod, full)
        if found:
            located[full] = found
    # A Prop structure's info has type Prop; its field types first appear in the
    # constructor/projection declarations. Recover the source owner from those edges.
    for c, (mod, deps) in list(raw.items()):
        if c in located or c in skip:
            continue
        owners = [c.rsplit(".", 1)[0]] if "." in c else []
        for owner in owners:
            found = located.get(owner) or locate(mod, owner)
            if found:
                located[owner] = found
                extra = raw.get(owner, (mod, []))[1]
                raw[owner] = (mod, sorted(set(extra + deps)))
                break
        else:
            raise ValueError(f"no source declaration for {c} in {mod}")

    ren = replace_tokens.copy()
    for c in sorted(located, key=lambda n: (n.count("."), n)):
        tail = c.split(".")[-1]
        owner = next((d for d in ren if c.startswith(d + ".") and d in located), None)
        if owner:
            # A method such as r.h5 keeps its short name in the new structure namespace.
            ren[c] = ren[owner] + c[len(owner):]
        else:
            new_tail = ren.get(tail, tail + "_scholzeNarrow")
            ren[tail] = new_tail
            ren[c] = c.removesuffix(tail) + new_tail
    direct = defaultdict(set)
    for c, (_, deps) in raw.items():
        if c not in located:
            continue
        for d in deps:
            while d not in located and "." in d:
                d = d.rsplit(".", 1)[0]
            if d in located and c != d:
                direct[c].add(d)

    out, order, visited, active = [], [], set(), set()
    def emit(c):
        if c in visited:
            return
        assert c not in active, ("cycle", c)
        active.add(c)
        for d in sorted(direct[c]):
            emit(d)
        active.remove(c)
        visited.add(c)
        file, spelling, i = located[c]
        start, end = decl_extent(file, i)
        # Keep the terminator newline so the slot-removal edits work at end of a declaration.
        body = strip_comments("\n".join(lines(file)[start:end])) + "\n"
        body = rename(edits(c, body), ren).strip()
        scopes = context(file, start)
        out.extend([f"-- {file}:{i + 1}", "section"])
        for op, _, cmds in scopes:
            if op:
                out.append(rename(op, ren))
            out.extend(cmds)
        out.append(body)
        for _, cl, _ in reversed(scopes):
            if cl:
                out.append(rename(cl, ren))
        out.extend(["end", ""])
        order.append((c, file, i + 1, ren[c], body.startswith("theorem ")))

    emit(OLD_TOP)
    # Tainted functions can occur through a constructor/projection edge, and are
    # also checked if not picked up through the top's proof value.
    assert set(located) == visited, sorted(set(located) - visited)
    return "\n".join(out), order

if __name__ == "__main__":
    chain, order = proof_part()
    (SCRATCH / "generated-declarations.tsv").write_text("".join(
        f"{file}:{line}\t{old}\t{new}\n" for old, file, line, new, _ in order))
    (SCRATCH / "Chain.lean").write_text(
        "import ZInQKernel.OneProof.H.TailZ89\n"
        "import ZInQKernel.Contrib.OneProof.ScholzeNarrow\n\n"
        "/-! Generated Scholze surface bypass for the base H proof. -/\n\n" + chain)
    main = Path("ZInQKernel/OneProof/Main.lean").read_text()
    theorem = main[main.index("theorem _root_.ZInQ.OneProof.frozenTarget"): main.index("\nend ZInQ.OneProof")]
    theorem = rename(theorem, {
        "ZInQ.OneProof.frozenTarget": "ZInQ.OneProof.frozenTargetScholzeNarrow",
        "OpenAddedLeaves28": "OpenAddedLeaves29",
        OLD_TOP: NEW_TOP,
    })
    checks = (SCRATCH / "Closure.lean.txt").read_text()
    (SCRATCH / "DryRun.lean").write_text(
        "import ZInQKernel.OneProof.Main\n"
        "import ZInQKernel.Contrib.OneProof.ScholzeNarrow\n"
        "import Lean\n\n"
        "/-! Generated dry run, including the identical outer proof and a closure check. -/\n\n"
        + chain + "\n" + theorem + "\n"
        + "".join(f"#print axioms {new}\n" for _, _, _, new, is_thm in order if is_thm)
        + "#print axioms ZInQ.OneProof.frozenTargetScholzeNarrow\n\n" + checks)
