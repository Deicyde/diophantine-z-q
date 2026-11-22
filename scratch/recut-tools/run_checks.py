"""Run upstream's trusted contract checker on every batch commit, as each staged PR would see it:
the worktree at the batch's commit, --base-ref the previous batch (the state after it merged).

usage: python3 -I run_checks.py WORKTREE CHECKER BATCHES_JSON OUT_JSON
"""
import json, subprocess, sys

wt, checker, batches_json, out_json = sys.argv[1:5]
B = json.load(open(batches_json))
results = []
for b in B["batches"]:
    subprocess.run(["git", "-C", wt, "checkout", "-q", "--detach", b["commit"]], check=True)
    p = subprocess.run([sys.executable, "-I", checker, "--root", wt, "--base-ref", b["parent"]],
                       capture_output=True, text=True)
    row = {"title": b["title"], "commit": b["commit"], "exit": p.returncode}
    if p.returncode == 0:
        j = json.loads(p.stdout)
        row.update(status=j["status"], files=j["files"], modules=len(j["modules"]),
                   route=j["review"]["route"], changed=len(j["review"]["changed"]),
                   lock_changed=len(j["review"]["lock_changed"]))
    else:
        row["error"] = p.stderr.strip()[-600:]
    results.append(row)
    print(f"{b['title'][:70]:70s} exit {p.returncode} "
          + (f"{row['status']} route={row['route']} changed={row['changed']} lock_changed={row['lock_changed']} "
             f"pins={row['files']} modules={row['modules']}" if p.returncode == 0 else row["error"]), flush=True)
json.dump(results, open(out_json, "w"), indent=1)
