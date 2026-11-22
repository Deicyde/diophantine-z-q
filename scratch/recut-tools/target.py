"""Target tree for the staged upstream PRs: upstream main plus the fork's proof, in the
contract-clean layout of 44b001cf, restricted to what the proof needs.

usage: python3 -I target.py REPO BASE FORK TAU_REPO TAU_PIN MOVED_LIST OUT_JSON

Scope: the import closure (through ZInQKernel.* imports) of every fork module under
ZInQKernel/OneProof/, plus the fork sources of every file BASE already has under Contrib/.
Layout (as build-everything.py, which built the clean copy 44b001cf):
  ZInQKernel/OneProof/X            -> ZInQKernel/Contrib/OneProof/X
  ZInQKernel/HDecomp/X (not pinned on BASE: #62's split and Textbook) -> ZInQKernel/Contrib/HDecomp/X
  ZInQKernel/Contrib/TauCeti/X     -> dropped; the Lake dependency on Tau Ceti provides TauCeti.X
  ZInQKernel/Contrib/<pkg>/X       -> same path; its non-.lean files -> ThirdParty/<pkg>/X
  trusted files (every other ZInQKernel path) -> same path; a file that differs from BASE is a
  statement change (pinned on BASE) or a new baseline file.
Writes OUT_JSON: per destination path, its source, blob, unit and imports, plus the statement
set, the deletions and the checks. Creates blobs with git hash-object -w; touches no working tree.
"""
import json, os, re, sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from gitio import Repo, imports, mod

repo_path, base_ref, fork_ref, tau_repo, tau_pin, moved_list, out_json = sys.argv[1:8]
R = Repo(repo_path)
TR = Repo(tau_repo)
CONTRIB = "ZInQKernel/Contrib/"
V = CONTRIB + "TauCeti/"
LIBS = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient",
        "ImportGraph", "Lean", "Std", "Init")

base, fork = R.rev(base_ref), R.rev(fork_ref)
tb, tf = R.tree(base), R.tree(fork)
contract = json.loads(R.blob(tb["KERNEL_CONTRACT.json"][1]))
pins = set(contract["files"])
taumods = {mod(p) for p in TR.tree(tau_pin, "TauCeti") if p.endswith(".lean")}
moved = [l.strip() for l in open(moved_list) if l.strip()]
moved_set = set(moved)
# 11-20: the fork's lean_lib CMSerreTateSupport (top-level module names, srcDir CMSerreTateSupport/) moves to
# ZInQKernel/Contrib/CMSerreTateSupport/; only import lines change.
CMS = "CMSerreTateSupport/"
cms_mods = {mod(p[len(CMS):]): p for p in tf if p.startswith(CMS) and p.endswith(".lean")}


# 11-20, ROUTE168=1: B9 takes upstream #168's form. BASE already contains #168 (Route K stays pinned; the
# manuscript route is the generated copy ZInQKernel/Contrib/ManuscriptPole/, namespace ManuscriptPole). The
# fork's edits to the pinned pole files are not carried (the copy has them); the fork's files that use the
# manuscript's pole objects point at the copy instead; no Route K file is deleted.
ROUTE168 = os.environ.get("ROUTE168") == "1"
POLE_KEEP = {"ZInQKernel/Hypotheses/Pole.lean", "ZInQKernel/Syntax/Templates/Core.lean",
             "ZInQKernel/Assembly/Local/PoleObstruction.lean", "ZInQKernel/Multiplication/Certificate/Parity.lean",
             "ZInQKernel/Main.lean", "ZInQKernel/MainGreenTao.lean", "ZInQKernel.lean"}
PM_SRC, PM_DEST = "ZInQKernel/Hypotheses/PoleManuscript.lean", "ZInQKernel/Contrib/PoleRC/PoleManuscript.lean"
MP = "ZInQKernel.Contrib.ManuscriptPole."
R168_MODS = {"ZInQKernel.Hypotheses.Pole": MP + "Hypotheses.Pole", "ZInQKernel.Main": MP + "Main",
             "ZInQKernel.MainGreenTao": MP + "MainGreenTao",
             "ZInQKernel.Hypotheses.PoleManuscript": "ZInQKernel.Contrib.PoleRC.PoleManuscript",
             "ZInQKernel/Hypotheses/Pole.lean": "ZInQKernel/Contrib/ManuscriptPole/Hypotheses/Pole.lean",
             "ZInQKernel/Main.lean": "ZInQKernel/Contrib/ManuscriptPole/Main.lean",
             "ZInQKernel/MainGreenTao.lean": "ZInQKernel/Contrib/ManuscriptPole/MainGreenTao.lean",
             "ZInQKernel/Hypotheses/PoleManuscript.lean": PM_DEST}
R168_PAT = re.compile("|".join(re.escape(k) + r"(?![A-Za-z0-9_'])" for k in sorted(R168_MODS, key=len, reverse=True)))
R168_NAMES = r"(polePoly|PoleSoluble|PoleCompleteness|poleS0|exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness)"
R168_ROOT = re.compile(r"_root_\.ZInQ\." + R168_NAMES + r"(?![A-Za-z0-9_'])")
R168_QUAL = re.compile(r"(?<![.A-Za-z0-9_'])ZInQ\." + R168_NAMES + r"(?![A-Za-z0-9_'])")
R168_BARE_S0 = re.compile(r"(?<![.A-Za-z0-9_'])poleS0(?![A-Za-z0-9_'])")
R168_BARE_FILES = {"ZInQKernel/Contrib/PoleRC/Bookkeeping.lean"}


def rewrite168(p, text):
    text = R168_PAT.sub(lambda m: R168_MODS[m.group(0)], text)
    text = R168_ROOT.sub(lambda m: "_root_.ManuscriptPole.ZInQ." + m.group(1), text)
    text = R168_QUAL.sub(lambda m: "ManuscriptPole.ZInQ." + m.group(1), text)
    if p in R168_BARE_FILES:
        text = R168_BARE_S0.sub("ManuscriptPole.ZInQ.poleS0", text)
    return text


def src_of(m):
    if m.startswith("ZInQKernel"):
        q = m.replace(".", "/") + ".lean"
        return q if q in tf else None
    return cms_mods.get(m)


def trusted(p):
    return (p == "ZInQKernel.lean" or (p.endswith(".lean") and p.split("/")[0] in ("ZInQKernel", "ThirdParty", "lean"))) \
        and not p.startswith(CONTRIB)


def fimports(p):
    return imports(R.text(tf[p][1]))


# scope: closure of ZInQKernel/OneProof/**
starts = [p for p in tf if p.startswith("ZInQKernel/OneProof/") and p.endswith(".lean")]
seen, todo = set(starts), list(starts)
while todo:
    p = todo.pop()
    for m in fimports(p):
        q = src_of(m)
        if q and q not in seen:
            seen.add(q)
            todo.append(q)
closure_size = len(seen)
# fork sources of files BASE already has under Contrib/ (so no stale copy stays behind)
base_contrib_sources = {}
for d in tb:
    if d.startswith(CONTRIB) and d.endswith(".lean"):
        rest = d[len(CONTRIB):]
        cands = [c for c in (("ZInQKernel/" + rest) if rest.startswith(("OneProof/", "HDecomp/")) else None, d) if c]
        srcs = [c for c in cands if c in tf]
        assert len(srcs) <= 1, ("ambiguous fork source", d, srcs)
        base_contrib_sources[d] = srcs[0] if srcs else None
        if srcs and srcs[0] not in seen:
            seen.add(srcs[0])
            todo.append(srcs[0])
while todo:  # their closures too
    p = todo.pop()
    for m in fimports(p):
        q = src_of(m)
        if q and q not in seen:
            seen.add(q)
            todo.append(q)

fork_hdecomp_unpinned = sorted(p for p in tf if p.startswith("ZInQKernel/HDecomp/") and p.endswith(".lean") and p not in pins)
textbook_all = [p for p in fork_hdecomp_unpinned if p.startswith("ZInQKernel/HDecomp/Textbook/")]
odd_hdecomp = [p for p in fork_hdecomp_unpinned if p not in moved_set and p not in textbook_all]
textbook = sorted(p for p in seen if p in textbook_all)
oneproof = sorted(p for p in seen if p.startswith("ZInQKernel/OneProof/"))
split = sorted(p for p in seen if p in moved_set)
other_moved = sorted(p for p in seen if p in odd_hdecomp)


def dest(p):
    if ROUTE168 and p == PM_SRC:
        return PM_DEST
    if p.startswith(CMS):
        return CONTRIB + p
    if p.startswith("ZInQKernel/OneProof/") or p in moved_set or p in textbook_all or p in odd_hdecomp:
        return CONTRIB + p[len("ZInQKernel/"):]
    return p


# rename rules: as build-everything.py
def renames_for(paths, src_tree):
    r = {mod(p): mod(dest(p)) for p in paths}
    r.update({p: dest(p) for p in paths})
    dirs = {}
    for p in paths:
        dirs.setdefault(p.rsplit("/", 1)[0] + "/", []).append(p)
    for d in dirs:
        whole = all(q in paths for q in src_tree if q.startswith(d) and q.endswith(".lean"))
        if whole and not any(q.startswith(d) for q in tb):
            r[d] = CONTRIB + d[len("ZInQKernel/"):]
    return r


def compile_pat(r):
    keys = sorted(r, key=len, reverse=True)
    return re.compile("|".join(re.escape(k) + (r"(?!\.?[A-Za-z0-9_'])" if not k.endswith(("/", ".lean")) else "")
                               for k in keys))


split_r = renames_for(moved, tf)
split_pat = compile_pat(split_r)
full_r = dict(split_r)
full_r.update(renames_for(textbook_all, tf))
full_r.update(renames_for(sorted(p for p in tf if p.startswith("ZInQKernel/OneProof/") and p.endswith(".lean")), tf))
if odd_hdecomp:
    full_r.update(renames_for(odd_hdecomp, tf))
full_pat = compile_pat(full_r)
TAU_MOD = re.compile(r"ZInQKernel\.Contrib\.TauCeti\.(?=[A-Za-z])")
TAU_PATH = re.compile(r"ZInQKernel/Contrib/TauCeti/")


CMS_IMPORT = re.compile(r"^((?:(?:public|private|meta)\s+)*import\s+)(\S+)", re.M)


def cms_imports(text):
    return CMS_IMPORT.sub(lambda m: m.group(1) + ("ZInQKernel.Contrib.CMSerreTateSupport." + m.group(2)
                                                   if m.group(2) in cms_mods else m.group(2)), text)


def rewrite(p, text):
    text = cms_imports(text)
    if ROUTE168:
        text = rewrite168(p, text)
    if p in moved_set:
        return split_pat.sub(lambda m: split_r[m.group(0)], text)
    text = full_pat.sub(lambda m: full_r[m.group(0)], text)
    text = TAU_MOD.sub("TauCeti.", text)
    return TAU_PATH.sub("TauCeti/", text)


files = {}       # dest -> record
statement = {"modified": [], "added": [], "kept_base": []}
same_trusted, tau_dropped = 0, 0
for p in sorted(seen):
    if p.startswith(V):
        tau_dropped += 1
        continue
    d = dest(p)
    if ROUTE168 and d in POLE_KEEP:
        same_trusted += 1
        continue
    if trusted(d):
        if tb.get(d, (None, None))[1] == tf[p][1]:
            same_trusted += 1
            continue
        kind = "modified" if d in tb else "added"
        statement[kind].append(d)
    text = R.text(tf[p][1])
    out = rewrite(p, text).encode("utf-8")
    sha = R.git("hash-object", "-w", "--stdin", inp=out).decode().strip()
    files[d] = {"source": p, "mode": tf[p][0], "blob": sha, "imports": imports(out.decode("utf-8")),
                "on_base": tb.get(d, (None, None))[1] == sha, "base_has": d in tb}

# trusted files that differ but are outside the scope (e.g. the root ZInQKernel.lean)
for p in sorted(tf):
    if trusted(p) and p not in seen and dest(p) == p and p.endswith(".lean") and not (ROUTE168 and p in POLE_KEEP):
        if tb.get(p, (None, None))[1] != tf[p][1]:
            kind = "modified" if p in tb else "added"
            text = R.text(tf[p][1])
            out = rewrite(p, text).encode("utf-8")
            sha = R.git("hash-object", "-w", "--stdin", inp=out).decode().strip()
            files[p] = {"source": p, "mode": tf[p][0], "blob": sha, "imports": imports(out.decode("utf-8")),
                        "on_base": False, "base_has": p in tb, "outside_scope": True}
            statement[kind].append(p)

# trusted files BASE has and the fork does not (deleted by the fork, or upstream-only)
gone = [] if ROUTE168 else sorted(p for p in tb if trusted(p) and p not in tf)

# non-.lean files of the included Contrib packages -> ThirdParty/<pkg>/
# 11-20: only licence, notice, attribution, README and source-manifest files; the packages' working
# artifacts (verification notes, audit outputs, reports) stay in the fork.
# (Apache-2.0 4(b): files stating modifications stay with the licence.)
NOTICE_RE = re.compile(r"(LICEN[CS]E|NOTICE|COPYING|ATTRIBUTION|README|SOURCE_MANIFEST|EXTRACTED_SOURCES|MODIFIED|MODIFICATIONS|PORT_CHANGES|PORTING)", re.I)


def notice_like(p):
    return bool(NOTICE_RE.search(p.rsplit("/", 1)[-1]))
pkgs = sorted({src.split("/")[2] for d, r in files.items() for src in [r["source"]] if src.startswith(CONTRIB)})
notices = {}
for p in sorted(tf):
    if p.startswith(CONTRIB) and not p.startswith(V) and p.split("/")[2] in pkgs and not p.endswith(".lean"):
        d = "ThirdParty/" + p[len(CONTRIB):]
        if tb.get(d) == tf[p]:
            continue
        if not notice_like(p):
            continue
        notices[d] = {"source": p, "mode": tf[p][0], "blob": tf[p][1], "base_has": d in tb}

if any(p.startswith(CMS) for p in seen):
    for p in sorted(tf):
        if p.startswith(CMS) and not p.endswith(".lean") and notice_like(p):
            notices["ThirdParty/" + p] = {"source": p, "mode": tf[p][0], "blob": tf[p][1], "base_has": False}

# fork Lean outside the scope (not needed by the proof)
outside = sorted(p for p in tf if p.endswith(".lean") and p.startswith(("ZInQKernel/OneProof/", CONTRIB, "ZInQKernel/HDecomp/"))
                 and not p.startswith(V) and p != CONTRIB + "AllContrib.lean" and p not in seen
                 and (p.startswith(CONTRIB) or p.startswith("ZInQKernel/OneProof/") or p not in pins))

json.dump({"base": base, "fork": fork, "tau_pin": TR.rev(tau_pin), "closure_size": closure_size,
           "scope_size": len(seen), "tau_dropped": tau_dropped, "same_trusted": same_trusted,
           "oneproof": len(oneproof), "split": len(split), "textbook": len(textbook), "other_moved_hdecomp": other_moved,
           "odd_hdecomp_all": odd_hdecomp, "base_contrib_sources": base_contrib_sources,
           "statement": statement, "gone": gone, "files": files, "notices": notices, "outside": outside,
           "taumods_count": len(taumods), "route168": ROUTE168},
          open(out_json, "w"), indent=1, sort_keys=True)
print("scope", len(seen), "| closure of OneProof", closure_size, "| Tau Ceti dropped", tau_dropped,
      "| trusted unchanged", same_trusted, "| written", len(files), "| notices", len(notices), "| outside", len(outside))
print("statement:", {k: len(v) for k, v in statement.items()}, "| gone", len(gone), "| odd HDecomp", odd_hdecomp)
