"""Check published manuscript numbering against a separately identified Git baseline."""
import argparse
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import tempfile

import check_current_manuscript as current

ROOT = Path(__file__).resolve().parents[1]
SHA = re.compile(r"[0-9a-f]{40}")
PUBLISHED_PAIR = re.compile(r"manuscripts/quartic_v([1-9][0-9]*)\.(tex|pdf)")
require = current.require


def git(root, *args):
    result = subprocess.run(["git", *args], cwd=root, capture_output=True, timeout=180)
    require(result.returncode == 0, "Git baseline unavailable: " + result.stderr.decode(errors="replace").strip())
    return result.stdout


def commit_sha(value):
    require(isinstance(value, str) and SHA.fullmatch(value) and value != "0" * 40,
            "Expected a nonzero full baseline commit SHA")
    return value


def portable_name(name):
    require(isinstance(name, str) and name and not PurePosixPath(name).is_absolute()
            and not any(c in name for c in '\\:<>"|?*') and not any(ord(c) < 32 for c in name)
            and all(p not in ("", ".", "..") and p == p.rstrip(" .") for p in name.split("/")),
            "Unsafe baseline file path")
    reserved = {"con", "prn", "aux", "nul"} | {f"{p}{n}" for p in ("com", "lpt") for n in range(1, 10)}
    require(all(p.split(".")[0].lower() not in reserved for p in name.split("/")),
            "Reserved baseline file path")
    return name


def blob(root, revision, name):
    return git(root, "show", commit_sha(revision) + ":" + portable_name(name))


def baseline_profile(root, revision):
    """Validate the trusted baseline with the unchanged full pair validator too."""
    raw = blob(root, revision, current.PROFILE)
    profile = current.load_json(raw)
    require(type(profile) is dict and type(profile.get("required_tex_inputs")) is list,
            "Invalid baseline profile")
    pins = [profile[k] for k in ("tex", "pdf", "build_record")] + profile["required_tex_inputs"]
    with tempfile.TemporaryDirectory(prefix="published-manuscript-") as directory:
        stage = Path(directory)
        names = {current.PROFILE: raw}
        for pin in pins:
            require(type(pin) is dict and set(pin) == {"path", "sha256"}, "Invalid baseline pin")
            name = portable_name(pin["path"])
            require(name not in names, "Duplicate baseline path")
            names[name] = blob(root, revision, name)
        for name, data in names.items():
            path = stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        validated, _, _ = current.validate(stage)
    return validated


def artifact_fingerprint(profile):
    # Build diagnostics, engine information and build-record paths do not consume
    # a version when the published TeX, PDF and declared input bytes stay fixed.
    return (profile["tex"]["sha256"], profile["pdf"]["sha256"],
            tuple(sorted((p["path"], p["sha256"]) for p in profile["required_tex_inputs"])))


def versioned_paths(profile):
    for role in ("tex", "pdf"):
        require(profile[role]["path"] == f"manuscripts/quartic_v{profile['version']}.{role}",
                "Current manuscript paths must use the ordinary integer Version without a suffix")


def validate_transition(root, revision):
    root = Path(root).resolve()
    revision = commit_sha(revision)
    before = baseline_profile(root, revision)
    after, _, state = current.validate(root)
    versioned_paths(before)
    versioned_paths(after)
    changed = artifact_fingerprint(before) != artifact_fingerprint(after)
    expected = before["version"] + int(changed)
    require(after["version"] == expected,
            f"Published content {'changed' if changed else 'unchanged'}: expected Version {expected}, "
            f"found Version {after['version']}")

    # Preserve the preceding published project's actual files, not just its
    # profile hashes. New editions must use new paths for changed local inputs.
    preserved = {p["path"]: p["sha256"] for p in
                 [before["tex"], before["pdf"]] + before["required_tex_inputs"]}
    # Keep older numbered manuscript pairs immutable as well. Files for a future
    # draft number beyond the published baseline are not yet frozen by this rule.
    for name in git(root, "ls-tree", "-r", "--name-only", revision, "--", "manuscripts").decode().splitlines():
        match = PUBLISHED_PAIR.fullmatch(name)
        if match and int(match[1]) <= before["version"]:
            preserved[name] = current.sha(blob(root, revision, name))
    for name, digest in preserved.items():
        path = current.safe_path(root, name)
        require(not path.is_symlink() and current.sha(path.read_bytes()) == digest,
                "Published artifact was rewritten or relabeled: " + name)
    return {"status": "PASS", "baseline_sha": revision, "baseline_version": before["version"],
            "version": after["version"], "published_content_changed": changed,
            "preserved_published_files": sorted(preserved), "current_pair": state,
            "scope": "Integer publication transition and preserved artifact bytes; not mathematical or protected App acceptance."}


def remote_default(root, branch):
    """Read the live server branch named by the trusted event, without a shell."""
    require(isinstance(branch, str), "Missing trusted default branch")
    ref = "refs/heads/" + branch
    git(root, "check-ref-format", ref)
    lines = git(root, "ls-remote", "--exit-code", "origin", ref).decode().splitlines()
    require(len(lines) == 1, "Ambiguous live publication branch")
    sha, actual_ref = lines[0].split()
    require(actual_ref == ref, "Unexpected publication ref")
    return commit_sha(sha)


def event_baseline(root, event_name, event, github_sha, repository, live_branch=remote_default):
    """Select publication state from runner event data, never candidate JSON."""
    github_sha = commit_sha(github_sha)
    require(git(root, "rev-parse", "HEAD").decode().strip() == github_sha,
            "Checkout does not match the trusted event SHA")
    require(event.get("repository", {}).get("full_name") == repository,
            "Event repository does not match runner repository")
    default = event["repository"].get("default_branch")
    require(isinstance(default, str) and default, "Missing trusted default branch")
    if event_name == "pull_request":
        base = event["pull_request"]["base"]
        require(base.get("repo", {}).get("full_name") == repository, "Unexpected PR base repository")
        if base["ref"] == default:
            revision = commit_sha(base["sha"])
            require(live_branch(root, default) == revision,
                    "Publication base advanced; update the PR and rerun against the current base")
            return revision, "trusted pull_request.base.sha, matched to live publication branch"
        return live_branch(root, default), "trusted event default branch for an unpublished integration PR"
    if event_name == "push":
        require(not event.get("deleted"), "Invalid push publication event")
        if str(event.get("ref", "")).startswith("refs/tags/"):
            return None, "tag push: current-pair state check only, no publication-transition decision"
        require(event.get("after") == github_sha, "Invalid push publication event")
        if event.get("ref") == "refs/heads/" + default:
            return commit_sha(event.get("before")), "trusted default-branch push.before SHA"
        if str(event.get("ref", "")).startswith("refs/heads/"):
            return live_branch(root, default), "trusted event default branch for a pre-release branch push"
        raise ValueError("Unsupported push ref for publication-version enforcement")
    if event_name == "workflow_dispatch":
        if event.get("ref") in (default, "refs/heads/" + default):
            return None, "manual default-branch run: current-pair state check only, no publication-transition decision"
        return live_branch(root, default), "trusted event default branch for a pre-release manual run"
    raise ValueError("Unsupported event for publication-version enforcement")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--github-event", action="store_true")
    mode.add_argument("--base-ref", help="Explicit local comparison only; not accepted in GitHub Actions")
    mode.add_argument("--state-only", action="store_true", help="Validate current files without accepting a publication transition")
    args = parser.parse_args()
    root = args.repo.resolve()
    actions = os.environ.get("GITHUB_ACTIONS") == "true"
    require(not actions or args.github_event, "CI requires its trusted GitHub event baseline")
    if args.github_event:
        require(actions and root == Path(os.environ["GITHUB_WORKSPACE"]).resolve(),
                "GitHub mode requires the runner workspace")
        event_path = Path(os.environ["GITHUB_EVENT_PATH"]).resolve()
        require(not event_path.is_relative_to(root), "Event data must not come from the candidate repository")
        event = current.load_json(event_path.read_bytes())
        revision, authority = event_baseline(root, os.environ["GITHUB_EVENT_NAME"], event,
                                             os.environ["GITHUB_SHA"], os.environ["GITHUB_REPOSITORY"])
        if revision:
            # Fetch only the trusted commit needed for the comparison. No caller
            # supplied ref or profile field can substitute another baseline.
            git(root, "fetch", "--no-tags", "--depth=1", "origin", revision)
    elif args.base_ref:
        revision = git(root, "rev-parse", "--verify", "--end-of-options", args.base_ref + "^{commit}").decode().strip()
        authority = "explicit local diagnostic baseline; not a trusted CI publication decision"
    else:
        revision, authority = None, "explicit local current-pair state check only"
    if revision:
        report = validate_transition(root, revision)
        if args.github_event and (os.environ["GITHUB_EVENT_NAME"] != "push"
                                  or event.get("ref") != "refs/heads/" + event["repository"]["default_branch"]):
            require(remote_default(root, event["repository"]["default_branch"]) == revision,
                    "Publication base advanced during validation; update and rerun")
    else:
        profile, _, state = current.validate(root)
        versioned_paths(profile)
        report = {"status": "PASS", "mode": "state-only", "publication_transition_accepted": False,
                  "current_pair": state}
    report["baseline_authority"] = authority
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
