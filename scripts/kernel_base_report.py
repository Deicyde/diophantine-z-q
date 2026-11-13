#!/usr/bin/env python3
"""Obtain comparison evidence from a successful main-push kernel CI run.

The evidence is for a progress table only. It never authorizes a merge.
Missing evidence remains explicitly unmeasured, never zero/proved.
"""
import hashlib
import io
import json
import os
import subprocess
from pathlib import Path
import urllib.error
import urllib.request
import zipfile

from check_kernel_contract import ROOT, git


def request(path, raw=False):
    # GitHub's artifact archive redirects to signed object storage. urllib
    # must not forward a repository token to that different host.
    class NoAuthRedirect(urllib.request.HTTPRedirectHandler):
        def redirect_request(self, req, fp, code, msg, headers, newurl):
            new = super().redirect_request(req, fp, code, msg, headers, newurl)
            if new is not None:
                new.remove_header("Authorization")
            return new
    url = "https://api.github.com" + path
    req = urllib.request.Request(url, headers={
        "Authorization": "Bearer " + os.environ["GH_TOKEN"],
        "Accept": "application/vnd.github+json", "User-Agent": "kernel-base-evidence"})
    with urllib.request.build_opener(NoAuthRedirect()).open(req, timeout=60) as response:
        body = response.read()
    return body if raw else json.loads(body)


def main():
    out = ROOT / "build/kernel-ci"
    out.mkdir(parents=True, exist_ok=True)
    repo = os.environ["GITHUB_REPOSITORY"]
    event = json.loads(Path(os.environ["GITHUB_EVENT_PATH"]).read_bytes())
    if "pull_request" in event:
        base = git(ROOT, "merge-base", event["pull_request"]["base"]["sha"],
                   event["pull_request"]["head"]["sha"]).decode().strip()
    else:
        base = event.get("before")
    provenance = {"base_sha": base, "status": "not_measured", "targets": []}
    report = {"targets": []}
    has_contract = False
    if base and base != "0" * 40:
        try:
            git(ROOT, "cat-file", "-e", base + ":KERNEL_CONTRACT.json")
            has_contract = True
        except subprocess.CalledProcessError:
            provenance["reason"] = "No kernel contract at the base revision"
    if has_contract:
        runs = request(f"/repos/{repo}/actions/workflows/kernel-lean.yml/runs?head_sha={base}&event=push&status=success&per_page=100")
        for run in runs.get("workflow_runs", []):
            if not (run["head_sha"] == base and run["head_branch"] == "main"
                    and run["head_repository"]["full_name"] == repo and run["event"] == "push"
                    and run["conclusion"] == "success"):
                continue
            artifacts = request(f"/repos/{repo}/actions/runs/{run['id']}/artifacts?per_page=100")
            found = [a for a in artifacts["artifacts"] if a["name"] == "kernel-audit" and not a["expired"]]
            if len(found) != 1:
                continue
            artifact = found[0]
            data = request(f"/repos/{repo}/actions/artifacts/{artifact['id']}/zip", raw=True)
            digest = "sha256:" + hashlib.sha256(data).hexdigest()
            if artifact.get("digest") != digest:
                raise RuntimeError("Base artifact digest missing or mismatched")
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                if archive.namelist().count("audit.json") != 1:
                    raise RuntimeError("Missing/ambiguous base audit report")
                candidate = json.loads(archive.read("audit.json"))
            if candidate["status"] != "passed" or candidate["head_sha"] != base:
                raise RuntimeError("Base report does not match the main commit")
            actual_contract = hashlib.sha256(git(ROOT, "show", base + ":KERNEL_CONTRACT.json")).hexdigest()
            if candidate["contract_sha256"] != actual_contract:
                raise RuntimeError("Base report contract mismatch")
            report = candidate
            provenance.update(status="authenticated_main_ci", run_id=run["id"],
                              artifact_id=artifact["id"], digest=digest)
            break
    (out / "base-audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    (out / "base-evidence.json").write_text(json.dumps(provenance, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(provenance))


if __name__ == "__main__":
    main()
