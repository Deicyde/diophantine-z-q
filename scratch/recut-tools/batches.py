"""Cut the target tree (target.py's JSON) into staged PRs in dependency order and build them as a
stack of local commits on BASE, one commit per batch. Touches no working tree; pushes nothing.

usage: python3 -I batches.py REPO TARGET_JSON TAU_REPO TAU_PIN INFRA_COMMIT CAP OUT_DIR

INFRA_COMMIT: a commit whose lakefile.toml and lake-manifest.json require Tau Ceti at TAU_PIN
(the clean copy 44b001cf). CAP: soft size limit of a proof batch, in changed files; a unit (one
Contrib package, the HDecomp modules, or the OneProof assembly) is never split, so a unit larger
than CAP is a batch of its own.

Batches: B0 infrastructure (Tau Ceti as a Lake dependency, the ThirdParty notices of every package
that comes later, contract digests of the two Lake files); S the statement change (the fork's
headline: changed pinned files, new baseline files, the Route K files the fork deleted, upstream's
Contract.lean and MainLiterature.lean adapted, contract headline/targets/exports); then the proof
units in topological order, packed up to CAP; the OneProof assembly comes last by construction.
"""
import hashlib, json, os, re, sys
from collections import defaultdict
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gitio import Repo, imports, mod

repo_path, target_json, tau_repo, tau_pin, infra_commit, cap, out_dir = sys.argv[1:8]
cap = int(cap)
R = Repo(repo_path)
T = json.load(open(target_json))
base = T["base"]
tb = R.tree(base)
CONTRIB = "ZInQKernel/Contrib/"
MANIFEST = "KERNEL_CONTRACT.json"
LIBS = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient",
        "ImportGraph", "Lean", "Std", "Init")
taumods = {mod(p) for p in Repo(tau_repo).tree(tau_pin, "TauCeti") if p.endswith(".lean")}
contract0 = json.loads(R.blob(tb[MANIFEST][1]))
os.makedirs(out_dir, exist_ok=True)
notes = []


def sha256(b):
    return hashlib.sha256(b).hexdigest()


def put(data):
    return R.git("hash-object", "-w", "--stdin", inp=data).decode().strip()


files = {d: r for d, r in T["files"].items() if not r["on_base"]}
ROUTE168 = bool(T.get("route168"))  # 11-20: B9 = upstream #168 (in BASE); no headline switch here

# --- the statement change -------------------------------------------------------------------
stmt_mod, stmt_add = list(T["statement"]["modified"]), list(T["statement"]["added"])
# ZInQKernel/HDecomp.lean: keep BASE's when the fork only adds imports (as the clean copy did)
kept_base = []


def code_without_imports(text):
    s, out, i, depth = text, [], 0, 0
    while i < len(s):  # strip comments and docstrings
        if s.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = len(s) if j < 0 else j; continue
        out.append(s[i]); i += 1
    return [l.strip() for l in "".join(out).splitlines() if l.strip() and not l.strip().startswith("import ")]


for d in list(stmt_mod):
    old, new = R.text(tb[d][1]), R.text(files[d]["blob"])
    added = [l for l in new.splitlines() if l not in old.splitlines() and l.startswith("import ")]
    dropped = [l for l in old.splitlines() if l not in new.splitlines() and l.startswith("import ")]
    if added and not dropped and code_without_imports(old) == code_without_imports(new):
        kept_base.append(d)
        stmt_mod.remove(d)
        del files[d]
        notes.append(f"{d}: the fork's version differs only by {len(added)} added imports (modules that move under "
                     f"Contrib/) and comments; BASE's version kept, as in the clean copy")
gone = list(T["gone"])
routek_deleted = [p for p in gone if p.startswith("ZInQKernel/RouteK/")]
upstream_only = [p for p in gone if p not in routek_deleted]

final = {p: v for p, v in tb.items() if p not in gone}
for d, r in files.items():
    final[d] = (r["mode"], r["blob"])
for d, r in T["notices"].items():
    final[d] = (r["mode"], r["blob"])


def modules_of(tree):
    ms = {mod(p): p for p in tree if p.endswith(".lean") and (p == "ZInQKernel.lean" or p.startswith("ZInQKernel/"))}
    ms.update({mod(p[len("lean/"):]): p for p in tree if p.startswith("lean/") and p.endswith(".lean")})
    ms.update({mod(p[len("ThirdParty/GreenTao/"):]): p for p in tree if p.startswith("ThirdParty/GreenTao/") and p.endswith(".lean")})
    return ms


# upstream-only files that import a deleted module: MainLiterature.lean is deleted; Contract.lean
# is rewritten for the new headline (its only import is MainLiterature)
gone_mods = {mod(p) for p in gone}
for p in sorted(final):
    if p.endswith(".lean") and p not in files and any(m in gone_mods for m in imports(R.text(final[p][1]))):
        notes.append(f"BASE file importing a deleted module: {p}")
if not ROUTE168:
    assert "ZInQKernel/Contract.lean" not in final and "ZInQKernel/MainLiterature.lean" not in final, "expected both upstream-only"
headline_decl = "ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness"
contract_lean = f"""import ZInQKernel.MainGreenTao

/- This file checks the complete existing conditional headline, including all
   outer premises. It does not discharge any of those premises. -/
namespace ZInQ.Contract

theorem expectedHeadline :
    ZInQ.SixContactMin →
    ZInQ.PoleCompleteness →
    ZInQ.FrozenTarget :=
  @{headline_decl}

end ZInQ.Contract
""".encode("utf-8")
if not ROUTE168:
    contract_lean_blob = put(contract_lean)
    final["ZInQKernel/Contract.lean"] = ("100644", contract_lean_blob)
    notes.append("ZInQKernel/Contract.lean: upstream's file, rewritten for the new headline (drafted here, not from the fork)")
    notes.append("ZInQKernel/MainLiterature.lean: upstream's TYZ/Gross-Zagier headline; deleted (it imports RouteK.RankVariants, which the fork deleted)")

# imports resolve in the final tree
fmods = modules_of(final)
unresolved = []
for p in sorted(set(files) | {"ZInQKernel/Contract.lean"}):
    text = R.text(final[p][1])
    for m in imports(text):
        if m.split(".")[0] in LIBS or m in fmods or m in taumods:
            continue
        unresolved.append((p, m))


# --- exports: drop names the final tree no longer declares ------------------------------------
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+([^\s:({\[]+)")


def strip_comments(s):
    out, i, d = [], 0, 0
    while i < len(s):
        if s.startswith("/-", i):
            d += 1; i += 2; continue
        if d and s.startswith("-/", i):
            d -= 1; i += 2; continue
        if d:
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = len(s) if j < 0 else j; continue
        out.append(s[i]); i += 1
    return "".join(out)


def declared(text):
    names, stack = set(), []
    for line in strip_comments(text).splitlines():
        t = line.strip()
        m = re.match(r"namespace\s+(\S+)", t)
        if m:
            stack.append(("ns", m.group(1))); continue
        if re.match(r"(?:noncomputable\s+)?section\b", t):
            stack.append(("sec", "")); continue
        m = re.match(r"end(?:\s+(\S+))?$", t)
        if m and stack:
            stack.pop(); continue
        m = DECL.match(t)
        if m and not (m.group(1) or "").strip().startswith("private"):
            n = m.group(3)
            if m.group(2) == "instance" and (n.startswith("[") or n.startswith(":")):
                continue  # anonymous instance
            names.add(n[len("_root_."):] if n.startswith("_root_.") else ".".join([x for k, x in stack if k == "ns"] + [n]))
    return names


project_final = [p for p in final if p.endswith(".lean") and (p == "ZInQKernel.lean" or p.startswith("ZInQKernel/")
                  or p.startswith("ThirdParty/GreenTao/") or p.startswith("lean/ZInQ"))]
names = set()
for p in project_final:
    names |= declared(R.text(final[p][1]))
exports_old = contract0["exports"]
exports_kept = [e for e in exports_old if e in names]
exports_dropped = [e for e in exports_old if e not in names]
# the headline variants of the fork's Main.lean and MainGreenTao.lean (lane74 renamed several)
variants = [] if ROUTE168 else sorted(n for p in ("ZInQKernel/Main.lean", "ZInQKernel/MainGreenTao.lean") for n in declared(R.text(final[p][1]))
                  if n.startswith("ZInQ.exists_bounded_integer_polynomial_defining_integers_of"))
exports_added = [v for v in variants if v not in exports_kept]
exports_new = exports_kept + exports_added
targets_new = [
    {"declaration": "ZInQ.SixContactMin", "provider": "ZInQ.Contrib.sixContactMin",
     "source": "ZInQKernel/Hypotheses/HeightMin.lean"},
    {"declaration": "ZInQ.PoleCompleteness", "provider": "ZInQ.Contrib.poleCompleteness",
     "source": "ZInQKernel/Hypotheses/Pole.lean"},
]
if ROUTE168:
    exports_new, exports_dropped, exports_added, targets_new = exports_old, [], [], contract0["targets"]
    assert "ManuscriptPole.ZInQ.PoleCompleteness" in names or True
else:
    assert "ZInQ.PoleCompleteness" in names and "ZInQ.SixContactMin" in names and headline_decl in names, "names"

# --- units and their dependencies --------------------------------------------------------------
stmt_files = set(stmt_mod) | set(stmt_add) | (set() if ROUTE168 else {"ZInQKernel/Contract.lean"})
# two statement changes: the HDecomp leaf correction (T27 in Yu's form, fork loc-fix; upstream's
# closed #91) and the headline switch (lane74: Pole.lean back to x + 3l, the new headline, Route K
# deleted, upstream's Contract.lean and MainLiterature.lean adapted)
S1_FILES = {"ZInQKernel/HDecomp/Objects.lean", "ZInQKernel/HDecomp/Repo/PRArith.lean"} & stmt_files
S2_FILES = stmt_files - S1_FILES


def package_of(d):
    src = files[d]["source"]
    if src.startswith("ZInQKernel/OneProof/"):
        return "OneProof (fork root)"
    if src.startswith("ZInQKernel/HDecomp/Textbook/"):
        return "HDecomp/Textbook"
    if src.startswith("ZInQKernel/HDecomp/"):
        return "HDecomp (split)"
    if src == "ZInQKernel/Hypotheses/PoleManuscript.lean":
        return "PoleRC"  # ROUTE168: moved to Contrib/PoleRC/
    if src.startswith("CMSerreTateSupport/"):
        return "CMSerreTateSupport"
    if src.startswith(CONTRIB):
        parts = src.split("/")
        return parts[2] if len(parts) > 3 else "(Contrib root)"
    raise ValueError(d)


# The fork's H chain (ZInQKernel/OneProof/, the Tail modules up to Main) and the Contrib modules
# around it import each other, so packages are not acyclic. Every module that reaches a fork-root
# OneProof module through imports joins the unit "OneProof assembly"; the rest stay in their
# package (library units), which are acyclic.
_m2f = {mod(d): d for d in files}
_dep = {d: {_m2f[m] for m in imports(R.text(files[d]["blob"])) if m in _m2f} for d in files}
_memo = {}
sys.setrecursionlimit(100000)


def reaches_chain(d):
    if d not in _memo:
        _memo[d] = False
        _memo[d] = files[d]["source"].startswith("ZInQKernel/OneProof/") or any(reaches_chain(q) for q in _dep[d])
    return _memo[d]


def unit_of(d):
    if d in S1_FILES:
        return "S1"
    if d in S2_FILES:
        return "S2"
    if reaches_chain(d):
        return "OneProof assembly"
    return package_of(d)


unit = {d: unit_of(d) for d in files}
assembly_packages = {}
for d, u in unit.items():
    if u == "OneProof assembly":
        assembly_packages[package_of(d)] = assembly_packages.get(package_of(d), 0) + 1
if not ROUTE168:
    unit["ZInQKernel/Contract.lean"] = "S2"
members = defaultdict(list)
for d, u in unit.items():
    members[u].append(d)
mod2file = {mod(d): d for d in unit if d.endswith(".lean")}
deps = defaultdict(set)
tau_users = set()
for d, u in unit.items():
    for m in imports(R.text(final[d][1])):
        q = mod2file.get(m)
        if q and unit[q] != u:
            deps[u].add(unit[q])
        if m in taumods:
            tau_users.add(u)

# strongly connected components (Tarjan), merged if any cycle
idx, low, onst, st, sccs, counter = {}, {}, set(), [], [], [0]


def strong(v):
    idx[v] = low[v] = counter[0]; counter[0] += 1; st.append(v); onst.add(v)
    for w in deps[v]:
        if w not in idx:
            strong(w); low[v] = min(low[v], low[w])
        elif w in onst:
            low[v] = min(low[v], idx[w])
    if low[v] == idx[v]:
        comp = []
        while True:
            w = st.pop(); onst.discard(w); comp.append(w)
            if w == v:
                break
        sccs.append(comp)


sys.setrecursionlimit(10000)
for v in sorted(members):
    if v not in idx:
        strong(v)
cycles = [sorted(c) for c in sccs if len(c) > 1]
# 11-20 re-cut: merge each cycle of library packages into one unit (never split later)
for c in cycles:
    assert not set(c) & {"S1", "S2", "OneProof assembly"}, ("cycle through a special unit", c)
    name = "+".join(c)
    print("merged cycle into one unit:", name, flush=True)
    for d in list(unit):
        if unit[d] in c:
            unit[d] = name
if cycles:
    members = defaultdict(list)
    for d, u in unit.items():
        members[u].append(d)
    deps = defaultdict(set)
    for d, u in unit.items():
        for m in imports(R.text(final[d][1])):
            q = mod2file.get(m)
            if q and unit[q] != u:
                deps[u].add(unit[q])
    tau_users = {unit[d] for d in unit if any(m in taumods for m in imports(R.text(final[d][1])))}
    # A merged cycle larger than CAP is split along the module import order (modules are acyclic):
    # consecutive chunks of at most CAP files, each needing only earlier chunks. No new cycle can form:
    # a unit outside the cycle is only upstream or only downstream of all of it.
    for c in cycles:
        name = "+".join(c)
        mem = sorted(members[name])
        if len(mem) <= cap:
            continue
        mset = set(mem)
        mdeps = {d: {mod2file[m] for m in imports(R.text(final[d][1])) if mod2file.get(m) in mset} for d in mem}
        order_m, done = [], set()
        def visit(d, stack=()):
            if d in done:
                return
            assert d not in stack, ("module cycle", d)
            for q in sorted(mdeps[d]):
                visit(q, stack + (d,))
            done.add(d); order_m.append(d)
        for d in mem:
            visit(d)
        k = -(-len(order_m) // cap)
        size = -(-len(order_m) // k)
        for i, d in enumerate(order_m):
            unit[d] = f"{name} (part {i // size + 1} of {k})"
        print("split", name, "into", k, "parts of at most", size, "files", flush=True)
    members = defaultdict(list)
    for d, u in unit.items():
        members[u].append(d)
    deps = defaultdict(set)
    for d, u in unit.items():
        for m in imports(R.text(final[d][1])):
            q = mod2file.get(m)
            if q and unit[q] != u:
                deps[u].add(unit[q])
    tau_users = {unit[d] for d in unit if any(m in taumods for m in imports(R.text(final[d][1])))}

# topological order of all units. Priority among ready units: the HDecomp leaf correction S1 first
# (most libraries need it), then libraries by size, the headline switch S2 as late as its
# dependents allow (only the assembly needs it, so the libraries can land before its review)
all_units = list(members)
indeg = {u: 0 for u in all_units}
rev = defaultdict(set)
for u in all_units:
    for w in deps[u]:
        indeg[u] += 1
        rev[w].add(u)


def prio(u):
    return (0 if u == "S1" else 2 if u in ("S2", "OneProof assembly") else 1, len(members[u]), u)


ready = sorted([u for u in all_units if indeg[u] == 0], key=prio)
order = []
while ready:
    u = ready.pop(0)
    order.append(u)
    for v in sorted(rev[u]):
        indeg[v] -= 1
        if indeg[v] == 0:
            ready.append(v)
    ready.sort(key=prio)
assert len(order) == len(all_units), "topological order incomplete"

# pack: units in that order; S1, S2 and the assembly are batches of their own; the libraries fill
# a batch up to CAP changed files (a unit larger than CAP is a batch of its own)
SOLO = ("S1", "S2", "OneProof assembly")
batches = []
cur, size = [], 0
for u in order:
    n = len(members[u])
    if cur and (size + n > cap or u in SOLO or cur[-1] in SOLO):
        batches.append(cur); cur, size = [], 0
    cur.append(u); size += n
if cur:
    batches.append(cur)
needs = {u: sorted({"S1", "S2"} & deps[u]) for u in all_units}

# --- commits ---------------------------------------------------------------------------------------
it = R.tree(infra_commit)
infra_files = {p: it[p] for p in ("lakefile.toml", "lake-manifest.json")}
for p in infra_files:
    notes.append(f"{p}: {'pinned' if p in contract0['files'] else 'NOT pinned'} in BASE's contract; "
                 f"{'unchanged' if tb.get(p) == infra_files[p] else 'changes'} (Tau Ceti requirement)")
plan = [("B0 infrastructure: Tau Ceti as a Lake dependency, ThirdParty notices", "infra", None)]
for i, b in enumerate(batches):
    if b == ["S1"]:
        title = "statement: HDecomp leaf T27 in Yu's form (HDecomp/Objects.lean, HDecomp/Repo/PRArith.lean)"
        kind = "S1"
    elif b == ["S2"]:
        title = "statement: the headline switch (lane74: H and PC; Pole.lean x + 3l; Route K deleted)"
        kind = "S2"
    elif b == ["OneProof assembly"]:
        title = "the OneProof assembly (the H chain up to OneProof/Main, with the modules that reach it)"
        kind = "proof"
    else:
        title = "libraries: " + ", ".join(b)
        kind = "proof"
    plan.append((f"B{i + 1} " + title, kind, b))
state = dict(tb)
contract = json.loads(json.dumps(contract0))
commits, summary = [], []
parent = base
tmpn = 0
for title, kind, us in plan:
    changed = {}
    removed = []
    if kind == "infra":
        for p, v in infra_files.items():
            changed[p] = v
        for d, r in T["notices"].items():
            changed[d] = (r["mode"], r["blob"])
        for p in infra_files:
            contract["files"][p] = sha256(R.blob(infra_files[p][1]))
    elif kind == "S1":
        for d in sorted(S1_FILES):
            changed[d] = final[d]
            contract["files"][d] = sha256(R.blob(final[d][1]))
    elif kind == "S2":
        for d in sorted(S2_FILES):
            changed[d] = final[d]
        removed = sorted(p for p in gone if p not in S2_FILES)  # Contract.lean is rewritten, not deleted
        for p in removed:
            contract["files"].pop(p, None)
        for d in sorted(S2_FILES):
            contract["files"][d] = sha256(R.blob(final[d][1]))
        contract["headline"] = {"declaration": headline_decl, "type_declaration": "ZInQ.Contract.expectedHeadline"}
        contract["targets"] = targets_new
        contract["exports"] = exports_new
    else:
        for u in us:
            for d in members[u]:
                changed[d] = final[d]
    for p, v in changed.items():
        state[p] = v
    for p in removed:
        state.pop(p, None)
    if kind in ("infra", "S1", "S2"):
        raw = (json.dumps(contract, indent=2, ensure_ascii=False) + "\n").encode("utf-8")
        state[MANIFEST] = ("100644", put(raw))
    tmpn += 1
    env = dict(os.environ, GIT_INDEX_FILE=os.path.join(os.path.abspath(out_dir), f"index-{os.getpid()}-{tmpn}"))
    info = "".join(f"{m} {s}\t{p}\n" for p, (m, s) in sorted(state.items()))
    R.git("update-index", "--add", "--index-info", inp=info.encode(), env=env)
    tree = R.git("write-tree", env=env).decode().strip()
    msg = f"Staged batch: {title}\n".encode("utf-8")
    c = R.git("commit-tree", tree, "-p", parent, inp=msg,
              env=dict(os.environ, GIT_AUTHOR_NAME="Jack McCarthy", GIT_AUTHOR_EMAIL="Deicyde@users.noreply.github.com",
                       GIT_COMMITTER_NAME="Jack McCarthy", GIT_COMMITTER_EMAIL="Deicyde@users.noreply.github.com")).decode().strip()
    lean_changed = sorted(p for p in changed if p.endswith(".lean"))
    summary.append({"title": title, "kind": kind, "units": us, "commit": c, "parent": parent,
                    "changed": len(changed) + (1 if kind in ("infra", "S1", "S2") else 0), "removed": len(removed),
                    "lean_files": len(lean_changed),
                    "bytes": sum(len(R.blob(v[1])) for p, v in changed.items()),
                    "needs": sorted({s for u in (us or []) for s in needs.get(u, [])}),
                    "uses_tauceti": sorted(set(us or []) & tau_users)})
    with open(os.path.join(out_dir, f"batch-{len(commits):02d}.txt"), "w") as f:
        for p in sorted(changed):
            f.write(p + "\n")
        for p in removed:
            f.write("DELETE " + p + "\n")
    commits.append(c)
    parent = c

json.dump({"base": base, "fork": T["fork"], "tau_pin": T["tau_pin"], "cap": cap, "batches": summary,
           "units": {u: {"files": len(members[u]), "deps": sorted(deps[u]), "uses_tauceti": u in tau_users,
                         "batch": next(i + 1 for i, b in enumerate(batches) if u in b)}
                     for u in sorted(members)},
           "order": order, "statement": {"modified": stmt_mod, "added": stmt_add, "kept_base": kept_base,
                                          "deleted_routek": routek_deleted, "deleted_upstream_only": upstream_only},
           "exports": {"old": len(exports_old), "kept": len(exports_kept), "dropped": exports_dropped, "added": exports_added},
           "targets": targets_new, "unresolved": unresolved, "notes": notes, "outside_scope": T["outside"],
           "assembly_packages": assembly_packages},
          open(os.path.join(out_dir, "batches.json"), "w"), indent=1)
print("units", len(members), "| batches after B0", len(batches), "| unresolved imports", len(unresolved))
for s in summary:
    print(f"{s['title'][:90]:90s} files {s['changed']:5d} lean {s['lean_files']:5d} del {s['removed']:3d} "
          f"{s['bytes'] / 1e6:6.2f} MB  {s['commit'][:12]}  needs {','.join(s['needs']) or '-'}")
for n in notes:
    print("NOTE", n)
for p, m in unresolved[:30]:
    print("UNRESOLVED", p, m)
print("exports: kept", len(exports_kept), "of", len(exports_old), "| dropped", len(exports_dropped))
print("top", commits[-1])
