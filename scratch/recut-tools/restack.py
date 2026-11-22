"""Restack the ROUTE168 batch stack (cut on M = upstream main + #168) for upstream review:
upstream main -> the batches that don't need #168 -> merge of #168 -> the batches that do.

usage: python3 -I restack.py REPO BATCHES_JSON TARGET_JSON UPSTREAM_MAIN PR168_HEAD OUT_JSON
A batch needs #168 when one of its files imports a ZInQKernel.Contrib.ManuscriptPole module, or a module
of a batch that needs it. Each batch's tree diff is replayed with git merge-tree (3-way, base = its old parent).
"""
import json, os, subprocess, sys

repo, bj, tj, up, pr168, out = sys.argv[1:7]
B = json.load(open(bj))["batches"]
T = json.load(open(tj))
ENV = dict(os.environ, GIT_AUTHOR_NAME="Jack McCarthy", GIT_AUTHOR_EMAIL="Deicyde@users.noreply.github.com",
           GIT_COMMITTER_NAME="Jack McCarthy", GIT_COMMITTER_EMAIL="Deicyde@users.noreply.github.com")


def git(*a, inp=None):
    return subprocess.run(["git", "-C", repo, *a], input=inp, capture_output=True, check=True, env=ENV).stdout.decode().strip()


def mod(p):
    return p[:-5].replace("/", ".")


files_of = []
for b in B:
    names = git("diff", "--name-only", b["parent"], b["commit"]).splitlines()
    files_of.append([n for n in names if n.endswith(".lean")])
needs, tainted = [], {m for m in []}
MP = "ZInQKernel.Contrib.ManuscriptPole."
for fs in files_of:
    imps = {m for f in fs if f in T["files"] for m in T["files"][f]["imports"]}
    n = any(m.startswith(MP) or m in tainted for m in imps)
    needs.append(n)
    if n:
        tainted |= {mod(f) for f in fs}
# a later batch may import a tainted module of a batch listed after it in the old order: iterate to a fixpoint
changed = True
while changed:
    changed = False
    for i, fs in enumerate(files_of):
        if needs[i]:
            continue
        imps = {m for f in fs if f in T["files"] for m in T["files"][f]["imports"]}
        if imps & tainted:
            needs[i] = True; tainted |= {mod(f) for f in fs}; changed = True
order = [i for i in range(len(B)) if not needs[i]] + ["pr168"] + [i for i in range(len(B)) if needs[i]]
parent, res = up, []
for i in order:
    if i == "pr168":
        tree = git("merge-tree", "--write-tree", parent, pr168).splitlines()[0]
        c = git("commit-tree", tree, "-p", parent, "-p", pr168, inp=b"Merge upstream #168 (the manuscript's pole route beside Route K)\n")
        res.append({"title": "upstream #168 (merge)", "commit": c, "parent": parent})
    else:
        b = B[i]
        tree = git("merge-tree", "--write-tree", "--merge-base", b["parent"], parent, b["commit"]).splitlines()[0]
        msg = git("log", "-1", "--format=%B", b["commit"]).encode() + b"\n"
        c = git("commit-tree", tree, "-p", parent, inp=msg)
        res.append({"title": b["title"], "commit": c, "parent": parent, "old": b["commit"], "needs168": needs[i]})
    parent = c
    print(f"{res[-1]['commit'][:12]}  {res[-1]['title'][:100]}", flush=True)
# the restacked top must equal the cut's top tree
assert git("rev-parse", parent + "^{tree}") == git("rev-parse", B[-1]["commit"] + "^{tree}"), "top tree differs"
print("top tree identical to the cut:", git("rev-parse", parent + "^{tree}"))
json.dump({"upstream_main": up, "pr168": pr168, "stack": res}, open(out, "w"), indent=1)
